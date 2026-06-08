-- Path-compressed (Patricia) trie — the height-erased successor to `NatCol.Tree`.
--
-- `Tree leaf : Nat → Type` (Tree.lean) indexes height in the TYPE, so a single sparse key
-- forces a chain of single-child `Node`s up to that height (≈13 for a 63-bit key). This module
-- replaces it with a height-ERASED trie where a single-child run creates no node at all: a `tip`
-- carries its whole prefix, a `bin` branches only where ≥2 keys actually diverge. That removes the
-- chains the benchmark showed cost ~6× memory and a cache-missing pointer per level.
--
-- Because children of a `bin` have non-uniform depth, there is no height index to recurse on, so
-- every operation is TOTAL via well-founded recursion on `sizeOf` (see
-- `~/.claude/.../path-compression-termination-recipe.md`). This iteration is implementation +
-- `#guard` cross-checks against the verified `NatSet`; the well-formedness predicate and the
-- denotational/lattice proofs are layered on top in later stages.
import NatCol

namespace NatCol

/-- A 32-way, big-endian, path-compressed set of `Nat` keys.
* `tip pfx bits` — a leaf holding every key `k` with `k >>> 5 = pfx`, membership of the bottom 5
  bits given by the set positions of `bits`. A lone key is a single `tip`, zero interior nodes.
* `bin pfx level mask kids` — a path-compressed branch on the 5-bit `chunk` at `level` (always
  `≥ 1`); `pfx` is the common prefix above `level` (`k >>> 5*(level+1)`), `kids` holds the present
  children compactly (`kids.size = popCount mask`, maintained by construction). -/
inductive PTree where
  | nil
  | tip (pfx : Nat) (bits : UInt32)
  | bin (pfx : Nat) (level : Nat) (mask : UInt32) (kids : Array PTree)
  deriving Inhabited

namespace PTree

----------------------------------------------------------------------------------------------------
-- Implementation
----------------------------------------------------------------------------------------------------

/-- The prefix of `k` strictly above `level` — the bits shared by everything under a `bin`
branching at `level`. -/
@[inline] def prefixAbove (k level : Nat) : Nat := k >>> (5 * (level + 1))

/-- The highest 5-bit chunk index at which `a` and `b` differ (meaningful only for `a ≠ b`):
the chunk holding the top set bit of `a ^^^ b`. -/
@[inline] def branchLevel (a b : Nat) : Nat := requiredHeight (a ^^^ b)

/-- An arbitrary member key (O(1); bits below the node's level are left `0`, which is all
`branchLevel`/prefix comparisons need). -/
def someKey : PTree → Nat
  | .nil                => 0
  | .tip pfx bits       => (pfx <<< 5) ||| (lowestSetIdx bits).toNat
  | .bin pfx level mask _ => (pfx <<< (5 * (level + 1))) ||| ((lowestSetIdx mask).toNat <<< (5 * level))

/-- The empty set. -/
@[inline] def empty : PTree := .nil

/-- The singleton `{k}` — a single `tip`, no interior nodes. -/
@[inline] def singleton (k : Nat) : PTree := .tip (k >>> 5) (setBit 0 (chunk k 0))

/-- Combine two subtrees with **disjoint** prefixes (representative keys `ka ≠ kb`) under a fresh
`bin` branching at their first differing chunk. -/
@[inline] def join (ka : Nat) (a : PTree) (kb : Nat) (b : PTree) : PTree :=
  let l := branchLevel ka kb
  let ca := chunk ka l
  let cb := chunk kb l
  .bin (prefixAbove ka l) l (setBit (setBit 0 ca) cb) (if ca < cb then #[a, b] else #[b, a])

-- `hb` is consumed by the `'hb` term-level array access; the linter doesn't track that through `dite`.
set_option linter.unusedVariables false in
/-- Membership (classic Patricia: route by chunk through the bins, verify the prefix at the tip).
Total: the present child is reached with the in-bounds proof `hb` (a `dite`, never an
`Option`-match — the latter trips the kernel's deep-recursion check inside well-founded recursion). -/
def contains (k : Nat) : PTree → Bool
  | .nil          => false
  | .tip pfx bits => k >>> 5 == pfx && testBit bits (chunk k 0)
  | .bin _ level mask kids =>
    if testBit mask (chunk k level) then
      if hb : arrayIndex mask (chunk k level) < kids.size then
        contains k (kids[arrayIndex mask (chunk k level)]'hb)
      else false
    else false
decreasing_by
  simp_wf
  rename_i hb
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb)
  omega

set_option linter.unusedVariables false in
/-- Insert `k`. Descends by chunk while the prefix matches; a prefix mismatch (divergence at a
compressed level) `join`s a fresh singleton in. -/
def insert (k : Nat) : PTree → PTree
  | .nil          => singleton k
  | .tip pfx bits =>
    if k >>> 5 == pfx then .tip pfx (setBit bits (chunk k 0))
    else join k (singleton k) ((pfx <<< 5) ||| (lowestSetIdx bits).toNat) (.tip pfx bits)
  | .bin pfx level mask kids =>
    if prefixAbove k level == pfx then
      if testBit mask (chunk k level) then
        if hb : arrayIndex mask (chunk k level) < kids.size then
          .bin pfx level mask (kids.setIfInBounds (arrayIndex mask (chunk k level))
            (insert k (kids[arrayIndex mask (chunk k level)]'hb)))
        else .bin pfx level mask kids
      else
        .bin pfx level (setBit mask (chunk k level))
          (kids.insertIdx! (arrayIndex mask (chunk k level)) (singleton k))
    else join k (singleton k) (someKey (.bin pfx level mask kids)) (.bin pfx level mask kids)
decreasing_by
  simp_wf
  rename_i hb
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb)
  omega

/-- Number of keys, bit-scanning each `tip`'s bitset and summing over children (`attach` carries
the membership the well-founded recursion needs). -/
def size : PTree → Nat
  | .nil           => 0
  | .tip _ bits    => popCount bits
  | .bin _ _ _ kids => kids.attach.foldl (fun acc ⟨c, _⟩ => acc + c.size) 0
decreasing_by
  simp_wf
  rename_i c hc
  have := Array.sizeOf_lt_of_mem hc
  omega

-- Set union — three mutually-recursive pieces, total via a shared lexicographic measure on combined
-- subtree size. `mergeChild` is split out of `mergeKids` only to keep the latter's body shallow: a
-- deeply-nested `let` under a well-founded recursion trips the kernel's deep-recursion check. The
-- `+1` on `mergeKids`'s measure orders its (equal-size) hand-off to `mergeChild` as a strict
-- decrease; `mergeKids`'s own recursion shrinks the leftover mask `rem` in the second component.
set_option linter.unusedVariables false in
mutual
/-- Union driver: merge matching `tip`/`bin` shapes in place, `join` mismatched prefixes under a
fresh branch, and combine two aligned `bin`s child-by-child through `mergeKids`. -/
def unionU : PTree → PTree → PTree
  | .nil, t => t
  | s, .nil => s
  | .tip p1 b1, .tip p2 b2 =>
    if p1 == p2 then .tip p1 (b1 ||| b2)
    else join (someKey (.tip p1 b1)) (.tip p1 b1) (someKey (.tip p2 b2)) (.tip p2 b2)
  | .tip p1 b1, .bin bp bl bm bk =>
      if prefixAbove (someKey (.tip p1 b1)) bl == bp then
        if testBit bm (chunk (someKey (.tip p1 b1)) bl) then
          if h : arrayIndex bm (chunk (someKey (.tip p1 b1)) bl) < bk.size then
            .bin bp bl bm (bk.setIfInBounds (arrayIndex bm (chunk (someKey (.tip p1 b1)) bl))
              (unionU (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h) (.tip p1 b1)))
          else .bin bp bl bm bk
        else .bin bp bl (setBit bm (chunk (someKey (.tip p1 b1)) bl))
          (bk.insertIdx! (arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)) (.tip p1 b1))
      else join (someKey (.bin bp bl bm bk)) (.bin bp bl bm bk) (someKey (.tip p1 b1)) (.tip p1 b1)
  | .bin bp bl bm bk, .tip p2 b2 =>
      if prefixAbove (someKey (.tip p2 b2)) bl == bp then
        if testBit bm (chunk (someKey (.tip p2 b2)) bl) then
          if h : arrayIndex bm (chunk (someKey (.tip p2 b2)) bl) < bk.size then
            .bin bp bl bm (bk.setIfInBounds (arrayIndex bm (chunk (someKey (.tip p2 b2)) bl))
              (unionU (bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h) (.tip p2 b2)))
          else .bin bp bl bm bk
        else .bin bp bl (setBit bm (chunk (someKey (.tip p2 b2)) bl))
          (bk.insertIdx! (arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)) (.tip p2 b2))
      else join (someKey (.bin bp bl bm bk)) (.bin bp bl bm bk) (someKey (.tip p2 b2)) (.tip p2 b2)
  | .bin p1 l1 m1 k1, .bin p2 l2 m2 k2 =>
    if l1 == l2 && p1 == p2 then
      .bin p1 l1 (m1 ||| m2) (mergeKids m1 k1 m2 k2 (m1 ||| m2) #[])
    else if l1 == l2 then
      join (someKey (.bin p1 l1 m1 k1)) (.bin p1 l1 m1 k1) (someKey (.bin p2 l2 m2 k2)) (.bin p2 l2 m2 k2)
    else if l2 < l1 then
      if prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 == p1 then
        if testBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) then
          if h : arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) < k1.size then
            .bin p1 l1 m1 (k1.setIfInBounds (arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1))
              (unionU (k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h) (.bin p2 l2 m2 k2)))
          else .bin p1 l1 m1 k1
        else .bin p1 l1 (setBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1))
          (k1.insertIdx! (arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)) (.bin p2 l2 m2 k2))
      else join (someKey (.bin p1 l1 m1 k1)) (.bin p1 l1 m1 k1) (someKey (.bin p2 l2 m2 k2)) (.bin p2 l2 m2 k2)
    else
      if prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 == p2 then
        if testBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) then
          if h : arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) < k2.size then
            .bin p2 l2 m2 (k2.setIfInBounds (arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2))
              (unionU (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h) (.bin p1 l1 m1 k1)))
          else .bin p2 l2 m2 k2
        else .bin p2 l2 (setBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2))
          (k2.insertIdx! (arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)) (.bin p1 l1 m1 k1))
      else join (someKey (.bin p2 l2 m2 k2)) (.bin p2 l2 m2 k2) (someKey (.bin p1 l1 m1 k1)) (.bin p1 l1 m1 k1)
termination_by s t => (sizeOf s + sizeOf t, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := Array.sizeOf_lt_of_mem (Array.getElem_mem h); omega)

/-- The merged child at one mask position `i`: present in both operands → recurse with `unionU`;
present in just one → carry that side over. -/
def mergeChild (m1 : UInt32) (k1 : Array PTree) (m2 : UInt32) (k2 : Array PTree) (i : UInt32) : PTree :=
  if testBit m1 i then
    if testBit m2 i then
      if h1 : arrayIndex m1 i < k1.size then
        if h2 : arrayIndex m2 i < k2.size then
          unionU (k1[arrayIndex m1 i]'h1) (k2[arrayIndex m2 i]'h2)
        else k1[arrayIndex m1 i]'h1
      else .nil
    else if h1 : arrayIndex m1 i < k1.size then k1[arrayIndex m1 i]'h1 else .nil
  else if h2 : arrayIndex m2 i < k2.size then k2[arrayIndex m2 i]'h2 else .nil
termination_by (sizeOf k1 + sizeOf k2, 0)
decreasing_by
  all_goals simp_wf
  all_goals (have := Array.sizeOf_lt_of_mem (Array.getElem_mem h1)
             have := Array.sizeOf_lt_of_mem (Array.getElem_mem h2); omega)

/-- Fold over the leftover union mask `rem`, appending each present position's `mergeChild` to
`acc` (one bit per step, lowest first). -/
def mergeKids (m1 : UInt32) (k1 : Array PTree) (m2 : UInt32) (k2 : Array PTree)
    (rem : UInt32) (acc : Array PTree) : Array PTree :=
  if hrem : rem == 0 then acc
  else
    mergeKids m1 k1 m2 k2 (clearLowest rem) (acc.push (mergeChild m1 k1 m2 k2 (lowestSetIdx rem)))
termination_by (sizeOf k1 + sizeOf k2 + 1, rem.toNat)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have : (clearLowest rem).toNat < rem.toNat :=
         UInt32.lt_iff_toNat_lt.mp (clearLowest_lt rem (by simp_all)); omega)
end

/-- Set union `a ∪ b`. -/
@[inline] def union (a b : PTree) : PTree := unionU a b

/-- `{0,…}` from a list, by repeated insertion. -/
def ofList (ks : List Nat) : PTree := ks.foldl (fun s k => s.insert k) .nil

----------------------------------------------------------------------------------------------------
-- Validation: `PTree` must agree with the verified `NatSet` (implementation-level cross-checks;
-- proofs are added in later stages)
----------------------------------------------------------------------------------------------------

private def seqK : List Nat := List.range 1000
private def sparseK : List Nat :=
  [0, 31, 32, 1023, 1024, 42, 1000000, 999999999, 4294967296, 9223372036854775807, 7]

#guard (ofList seqK).size == (NatSet.ofList seqK).size
#guard (ofList seqK).size == 1000
#guard (ofList sparseK).size == (NatSet.ofList sparseK).size
-- membership agrees for present keys
#guard sparseK.all fun k => (ofList sparseK).contains k == (NatSet.ofList sparseK).contains k
-- …and for absent keys (incl. a near-miss of the 63-bit key)
#guard [1, 33, 1025, 5, 123456, 8, 12345, 9223372036854775806].all fun k =>
  (ofList sparseK).contains k == (NatSet.ofList sparseK).contains k
-- idempotent re-insert
#guard ((empty.insert 42).insert 42).size == 1

private def evenK : List Nat := (List.range 400).map (2 * ·)
private def oddK : List Nat := (List.range 400).map (2 * · + 1)

-- union sizes agree with `NatSet.union` across dense/overlapping/sparse mixes
#guard ((ofList evenK).union (ofList oddK)).size == (NatSet.ofList (evenK ++ oddK)).size
#guard ((ofList sparseK).union (ofList (List.range 50))).size == (NatSet.ofList (sparseK ++ List.range 50)).size
#guard ((ofList sparseK).union (ofList sparseK)).size == (ofList sparseK).size       -- idempotent
#guard ((ofList (List.range 500)).union (ofList ((List.range 500).map (· + 250)))).size == 750
#guard ((ofList sparseK).union (ofList evenK)).size == (NatSet.ofList (sparseK ++ evenK)).size
-- membership after union agrees with NatSet
#guard (sparseK ++ List.range 50).all fun k =>
  ((ofList sparseK).union (ofList (List.range 50))).contains k == true

----------------------------------------------------------------------------------------------------
-- Theorems
--
-- The denotational layer: membership (`contains`) is the set's semantics, and a well-formedness
-- predicate `WF` captures the canonical shape the operations maintain and the membership proofs
-- rely on. The `contains_*` lemmas are the seams the (eventual) lattice/order suite routes through,
-- mirroring `Tree`'s `get?_*` seams but over the height-erased Patricia shape.
----------------------------------------------------------------------------------------------------

/-- Total child accessor: the subtree a `bin`'s mask routes slot `c` to, `nil` when the slot is
absent (or the compact index is out of range). Gives every membership/merge proof one total
accessor in place of the raw `dite` bounds juggling. -/
@[inline] def childAt (mask : UInt32) (kids : Array PTree) (c : UInt32) : PTree :=
  (kids[arrayIndex mask c]?).getD .nil

/-- The empty set contains nothing. -/
theorem contains_nil (k : Nat) : contains k .nil = false := by rw [contains]

/-- Membership on a `bin` factors through `childAt`: route by the level's chunk, then recurse.
Holds unconditionally — an absent slot and an out-of-range index both read `nil`, which contains
nothing — so it is the structural rewrite every `bin` membership proof opens with. -/
theorem contains_bin (k pfx level : Nat) (mask : UInt32) (kids : Array PTree) :
    contains k (.bin pfx level mask kids)
      = (testBit mask (chunk k level) && contains k (childAt mask kids (chunk k level))) := by
  rw [contains]; simp only [childAt]
  by_cases hb : testBit mask (chunk k level) = true
  · rw [if_pos hb, hb, Bool.true_and]
    by_cases hidx : arrayIndex mask (chunk k level) < kids.size
    · rw [dif_pos hidx, Array.getElem?_eq_getElem hidx, Option.getD_some]
    · rw [dif_neg hidx, Array.getElem?_eq_none (Nat.le_of_not_lt hidx), Option.getD_none,
          contains_nil]
  · rw [if_neg hb]
    simp only [Bool.not_eq_true] at hb
    rw [hb, Bool.false_and]

/-- Well-formedness: the canonical-shape invariant `contains` relies on.
* a `tip` carries a non-empty bitset;
* a `bin pfx level mask kids` branches at `level ≥ 1`, stores its present children compactly
  (`kids.size = popCount mask`), is path-compression-minimal (`≥ 2` children), every child is WF,
  and — the routing invariant — every key a present child holds agrees with the slot it hangs under
  (`chunk k level = c`) and the branch prefix (`prefixAbove k level = pfx`). -/
def WF : PTree → Prop
  | .nil => True
  | .tip _ bits => bits ≠ 0
  | .bin pfx level mask kids =>
      0 < level
      ∧ kids.size = popCount mask
      ∧ 2 ≤ popCount mask
      ∧ (∀ c ∈ kids, WF c)
      ∧ (∀ c, c < 32 → testBit mask c = true →
            ∀ k, contains k (childAt mask kids c) = true →
               chunk k level = c ∧ prefixAbove k level = pfx)
termination_by t => sizeOf t
decreasing_by
  simp_wf
  rename_i hc
  have := Array.sizeOf_lt_of_mem hc
  omega

/-- The empty set is well-formed. -/
theorem WF_empty : WF empty := by rw [empty, WF]; trivial

/-- A singleton is well-formed (one non-empty `tip`). -/
theorem WF_singleton (k : Nat) : WF (singleton k) := by
  rw [singleton, WF]; exact setBit_ne_zero 0 (chunk k 0)

/-- `k >>> 5` is `k / 32` — the high bits a `tip` stores as its prefix. -/
private theorem shiftRight5_eq (k : Nat) : k >>> 5 = k / 32 := by rw [Nat.shiftRight_eq_div_pow]

/-- A key's bottom chunk is its residue mod 32. -/
private theorem chunk0_eq (k : Nat) : chunk k 0 = UInt32.ofNat (k % 32) := by
  unfold chunk
  congr 1
  rw [Nat.mul_zero, Nat.shiftRight_zero, show (31 : Nat) = 2 ^ 5 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]

/-- A `Nat` is pinned by its high bits (`>>> 5`) and bottom chunk: the prefix/chunk split a `tip`
stores is lossless. Backs `contains_singleton`. -/
private theorem key_eq_iff (k j : Nat) :
    k = j ↔ (k >>> 5 = j >>> 5 ∧ chunk k 0 = chunk j 0) := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨hdiv, hmod⟩ => ?_⟩
  rw [shiftRight5_eq, shiftRight5_eq] at hdiv
  rw [chunk0_eq, chunk0_eq] at hmod
  have hm : k % 32 = j % 32 := by
    have hk : k % 32 < UInt32.size := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    have hj : j % 32 < UInt32.size := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    have := congrArg UInt32.toNat hmod
    rwa [UInt32.toNat_ofNat_of_lt' hk, UInt32.toNat_ofNat_of_lt' hj] at this
  omega

/-- Membership in a singleton is key equality — the `get?_singleton` seam for the set. -/
theorem contains_singleton (k j : Nat) : contains k (singleton j) = true ↔ k = j := by
  rw [singleton, contains, testBit_setBit 0 (chunk j 0) (chunk k 0) (chunk_lt _ _) (chunk_lt _ _),
      testBit_zero, Bool.false_or, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, key_eq_iff k j]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩

end PTree
end NatCol
