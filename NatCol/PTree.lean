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

/-- Membership on a `tip`: the prefix must match and the bottom chunk's bit must be set. -/
theorem contains_tip (j pfx : Nat) (bits : UInt32) :
    contains j (.tip pfx bits) = (j >>> 5 == pfx && testBit bits (chunk j 0)) := by rw [contains]

/-- Every key a subtree holds hangs under slot `c` at level `l` and shares prefix `p`. The routing
content of `WF`'s `bin` clause, named so the merge proofs (`join`/`insert`/`union`) can carry it. -/
def AlignedAt (l : Nat) (c : UInt32) (p : Nat) (t : PTree) : Prop :=
  ∀ k, contains k t = true → chunk k l = c ∧ prefixAbove k l = p

/-- Well-formedness: the canonical-shape invariant `contains` relies on.
* a `tip` carries a non-empty bitset;
* a `bin pfx level mask kids` branches at `level ≥ 1`, stores its present children compactly
  (`kids.size = popCount mask`), is path-compression-minimal (`≥ 2` children), every child is WF
  and non-empty (`≠ nil` — an empty child carries no keys, so it could be dropped without changing
  membership, which would break `ext`), and — the routing invariant (`AlignedAt`) — every key a
  present child holds agrees with the slot it hangs under (`chunk k level = c`) and the branch
  prefix (`prefixAbove k level = pfx`). -/
def WF : PTree → Prop
  | .nil => True
  | .tip _ bits => bits ≠ 0
  | .bin pfx level mask kids =>
      0 < level
      ∧ kids.size = popCount mask
      ∧ 2 ≤ popCount mask
      ∧ (∀ c ∈ kids, WF c)
      ∧ (∀ c ∈ kids, c ≠ .nil)
      ∧ (∀ c, c < 32 → testBit mask c = true → AlignedAt level c pfx (childAt mask kids c))
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

/-! ### Non-emptiness

The canonical invariant `WF` forbids `nil` children (a `nil` child at a present slot would carry no
keys, so it could be dropped without changing membership — exactly what would break `ext`). These
structural facts let the merge/insert proofs discharge that clause: the operations never produce a
`nil`. -/

/-- A singleton is a `tip`, never empty. -/
theorem singleton_ne_nil (k : Nat) : singleton k ≠ .nil := by
  rw [singleton]; exact fun h => PTree.noConfusion h

/-- `insert` always yields a `tip` or a `bin`, never `nil`. -/
theorem insert_ne_nil (k : Nat) (t : PTree) : insert k t ≠ .nil := by
  cases t <;> simp only [insert] <;> (repeat' split) <;> simp [join, singleton]

/-- Union with a non-empty operand is non-empty: every non-`nil` shape feeds a `tip`/`bin`/`join`
result. -/
theorem unionU_ne_nil_of_left (a b : PTree) (h : a ≠ .nil) : unionU a b ≠ .nil := by
  cases a with
  | nil => exact absurd rfl h
  | tip p1 b1 => cases b <;> simp only [unionU] <;> (repeat' split) <;> simp [join]
  | bin p1 l1 m1 k1 => cases b <;> simp only [unionU] <;> (repeat' split) <;> simp [join]

/-! ### The `join` seams

`join ka a kb b` builds a fresh 2-slot `bin` over two subtrees with divergent prefixes. The two
slots `ca = chunk ka l`, `cb = chunk kb l` are distinct, so membership splits cleanly. These are the
`get?_join` analogues for the prefix-divergent case of `insert`/`union`; both are stated on the
constructed `bin` and parametrized by the slot alignments, keeping the `branchLevel` arithmetic at
the call sites. -/

private theorem arrayIndex_zero (i : UInt32) : arrayIndex 0 i = 0 := by
  unfold arrayIndex
  rw [show ((0 : UInt32) &&& lowerMask i) = 0 from by bv_decide]; rfl

private theorem arrayIndex_self_setBit0 (i : UInt32) : arrayIndex (setBit 0 i) i = 0 := by
  rw [arrayIndex_setBit_self, arrayIndex_zero]

private theorem testBit_setBit0_ne (i j : UInt32) (hi : i < 32) (hj : j < 32) (h : i ≠ j) :
    testBit (setBit 0 i) j = false := by
  rw [testBit_setBit 0 i j hi hj, testBit_zero, Bool.false_or, beq_eq_false_iff_ne.mpr h]

private theorem uint32_not_lt_of_gt {a b : UInt32} (h : a > b) : ¬ a < b := by
  intro h2
  have := UInt32.lt_iff_toNat_lt.mp h
  have := UInt32.lt_iff_toNat_lt.mp h2
  omega

/-- The slot-`ca` child of a join is its first operand. -/
private theorem childAt_join_ca (ca cb : UInt32) (a b : PTree)
    (hca : ca < 32) (hcb : cb < 32) (hne : ca ≠ cb) :
    childAt (setBit (setBit 0 ca) cb) (if ca < cb then #[a, b] else #[b, a]) ca = a := by
  unfold childAt
  rcases lt_or_gt_uint32 hne with hlt | hgt
  · rw [if_pos hlt, arrayIndex_setBit_of_le (setBit 0 ca) cb ca hcb hca (uint32_le_of_lt hlt),
        arrayIndex_self_setBit0]
    rfl
  · rw [if_neg (uint32_not_lt_of_gt hgt),
        arrayIndex_setBit_of_gt (setBit 0 ca) cb ca hcb hca hgt (testBit_setBit0_ne ca cb hca hcb hne),
        arrayIndex_self_setBit0]
    rfl

/-- The slot-`cb` child of a join is its second operand. -/
private theorem childAt_join_cb (ca cb : UInt32) (a b : PTree)
    (hca : ca < 32) (hcb : cb < 32) (hne : ca ≠ cb) :
    childAt (setBit (setBit 0 ca) cb) (if ca < cb then #[a, b] else #[b, a]) cb = b := by
  unfold childAt
  rcases lt_or_gt_uint32 hne with hlt | hgt
  · rw [if_pos hlt, arrayIndex_setBit_self,
        arrayIndex_setBit_of_gt 0 ca cb hca hcb hlt (testBit_zero ca), arrayIndex_zero]
    rfl
  · rw [if_neg (uint32_not_lt_of_gt hgt), arrayIndex_setBit_self,
        arrayIndex_setBit_of_le 0 ca cb hca hcb (uint32_le_of_lt hgt), arrayIndex_zero]
    rfl

private theorem testBit_join_mask (ca cb s : UInt32) (hca : ca < 32) (hcb : cb < 32) (hs : s < 32) :
    testBit (setBit (setBit 0 ca) cb) s = ((ca == s) || (cb == s)) := by
  rw [testBit_setBit (setBit 0 ca) cb s hcb hs, testBit_setBit 0 ca s hca hs, testBit_zero,
      Bool.false_or, Bool.or_comm]

private theorem popCount_join_mask (ca cb : UInt32) (hca : ca < 32) (hcb : cb < 32) (hne : ca ≠ cb) :
    popCount (setBit (setBit 0 ca) cb) = 2 := by
  rw [popCount_setBit _ _ (testBit_setBit0_ne ca cb hca hcb hne),
      popCount_setBit _ _ (testBit_zero ca)]
  rfl

private theorem mem_pair {c x y : PTree} (h : c ∈ (#[x, y] : Array PTree)) : c = x ∨ c = y := by
  simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at h
  exact h

/-- Membership in a `join` of two slot-aligned subtrees is membership in either. The `get?_join`
seam for a prefix-divergent insert/union: the two subtrees route to distinct slots, so no key can
sit in both. -/
theorem contains_join (j p l : Nat) (ca cb : UInt32) (a b : PTree)
    (hca : ca < 32) (hcb : cb < 32) (hne : ca ≠ cb)
    (ha : AlignedAt l ca p a) (hb : AlignedAt l cb p b) :
    contains j (.bin p l (setBit (setBit 0 ca) cb) (if ca < cb then #[a, b] else #[b, a]))
      = (contains j a || contains j b) := by
  rw [contains_bin, testBit_join_mask ca cb (chunk j l) hca hcb (chunk_lt j l)]
  by_cases hjca : chunk j l = ca
  · rw [hjca, beq_self_eq_true, Bool.true_or, Bool.true_and,
        childAt_join_ca ca cb a b hca hcb hne]
    have hjb : contains j b = false := by
      cases hcon : contains j b with
      | true => have := (hb j hcon).1; rw [hjca] at this; exact absurd this hne
      | false => rfl
    rw [hjb, Bool.or_false]
  · by_cases hjcb : chunk j l = cb
    · rw [hjcb, beq_self_eq_true, Bool.or_true, Bool.true_and,
          childAt_join_cb ca cb a b hca hcb hne]
      have hja : contains j a = false := by
        cases hcon : contains j a with
        | true => have := (ha j hcon).1; rw [hjcb] at this; exact absurd this.symm hne
        | false => rfl
      rw [hja, Bool.false_or]
    · rw [beq_eq_false_iff_ne.mpr (fun h => hjca h.symm),
          beq_eq_false_iff_ne.mpr (fun h => hjcb h.symm), Bool.or_false, Bool.false_and]
      have hja : contains j a = false := by
        cases hcon : contains j a with
        | true => exact absurd (ha j hcon).1 hjca
        | false => rfl
      have hjb : contains j b = false := by
        cases hcon : contains j b with
        | true => exact absurd (hb j hcon).1 hjcb
        | false => rfl
      rw [hja, hjb, Bool.or_false]

/-- A `join` of two well-formed, slot-aligned subtrees is well-formed. The `bin` it builds is
2-child path-compression-minimal by construction, and its routing invariant is exactly the two
alignments. -/
theorem WF_join (p l : Nat) (ca cb : UInt32) (a b : PTree)
    (hl : 0 < l) (hca : ca < 32) (hcb : cb < 32) (hne : ca ≠ cb)
    (ha : AlignedAt l ca p a) (hb : AlignedAt l cb p b) (hwa : WF a) (hwb : WF b)
    (hane : a ≠ .nil) (hbne : b ≠ .nil) :
    WF (.bin p l (setBit (setBit 0 ca) cb) (if ca < cb then #[a, b] else #[b, a])) := by
  rw [WF]
  refine ⟨hl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [popCount_join_mask ca cb hca hcb hne]; split <;> rfl
  · rw [popCount_join_mask ca cb hca hcb hne]; exact Nat.le_refl 2
  · intro c hc
    have hcab : c = a ∨ c = b := by
      split at hc
      · exact mem_pair hc
      · exact (mem_pair hc).symm
    rcases hcab with rfl | rfl
    · exact hwa
    · exact hwb
  · intro c hc
    have hcab : c = a ∨ c = b := by
      split at hc
      · exact mem_pair hc
      · exact (mem_pair hc).symm
    rcases hcab with rfl | rfl
    · exact hane
    · exact hbne
  · intro s hs hts
    rw [testBit_join_mask ca cb s hca hcb hs, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hts
    rcases hts with hsa | hsb
    · subst hsa; rw [childAt_join_ca ca cb a b hca hcb hne]; exact ha
    · subst hsb; rw [childAt_join_cb ca cb a b hca hcb hne]; exact hb

/-! ### Alignment: a well-formed tree's keys share a high prefix

The `join` seams above need their operands `AlignedAt` a common level. These lemmas supply that: a
non-empty subtree's keys all agree above its own branch level, so it is aligned at every level
strictly above. This is what lets a prefix-divergent `insert`/`union` slot an existing subtree
under a fresh branch. -/

/-- A low part below `2^n` does not survive a right shift by `n`: `(p <<< n ||| j) >>> n = p`. The
bit-level core of the `someKey` high-bit facts. -/
private theorem shiftLeft_lor_shiftRight (p j n : Nat) (hj : j < 2 ^ n) :
    (p <<< n ||| j) >>> n = p := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  have hjf : Nat.testBit j (n + i) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hj (Nat.pow_le_pow_right (by decide) (by omega)))
  rw [hjf, Bool.or_false]
  simp [Nat.add_sub_cancel_left]

/-- Agreement on a right shift propagates to any larger shift (the higher bits are a suffix). -/
private theorem shiftRight_mono_eq {k m a b : Nat} (h : k >>> a = m >>> a) (hab : a ≤ b) :
    k >>> b = m >>> b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Nat.shiftRight_add, Nat.shiftRight_add, h]

private theorem chunk_eq_of_shiftRight_eq {k m l : Nat} (h : k >>> (5 * l) = m >>> (5 * l)) :
    chunk k l = chunk m l := by unfold chunk; rw [h]

private theorem prefixAbove_eq_of_shiftRight_eq {k m l : Nat}
    (h : k >>> (5 * (l + 1)) = m >>> (5 * (l + 1))) : prefixAbove k l = prefixAbove m l := by
  unfold prefixAbove; exact h

/-- A non-empty `tip`'s representative key carries the prefix `pfx` above the bottom chunk. -/
private theorem someKey_tip_shiftRight5 (pfx : Nat) (bits : UInt32) (hb : bits ≠ 0) :
    someKey (.tip pfx bits) >>> 5 = pfx := by
  show ((pfx <<< 5) ||| (lowestSetIdx bits).toNat) >>> 5 = pfx
  apply shiftLeft_lor_shiftRight
  have h := UInt32.lt_iff_toNat_lt.mp (lowestSetIdx_lt bits hb)
  rw [show (32 : UInt32).toNat = 32 from by decide] at h
  exact h

/-- A `bin`'s representative key carries the branch prefix `pfx` above `level`. -/
private theorem someKey_bin_prefixAbove (pfx level : Nat) (mask : UInt32) (kids : Array PTree)
    (hm : mask ≠ 0) : prefixAbove (someKey (.bin pfx level mask kids)) level = pfx := by
  show ((pfx <<< (5 * (level + 1))) ||| ((lowestSetIdx mask).toNat <<< (5 * level)))
        >>> (5 * (level + 1)) = pfx
  apply shiftLeft_lor_shiftRight
  have hlsi : (lowestSetIdx mask).toNat < 32 := by
    have h := UInt32.lt_iff_toNat_lt.mp (lowestSetIdx_lt mask hm)
    rwa [show (32 : UInt32).toNat = 32 from by decide] at h
  rw [Nat.shiftLeft_eq, show 5 * (level + 1) = 5 * level + 5 from by omega, Nat.pow_add]
  calc (lowestSetIdx mask).toNat * 2 ^ (5 * level)
      < 32 * 2 ^ (5 * level) :=
        Nat.mul_lt_mul_of_pos_right hlsi (Nat.pow_pos (by decide))
    _ = 2 ^ (5 * level) * 2 ^ 5 := by rw [Nat.mul_comm]

/-- A non-empty `tip` is aligned at every level `≥ 1`: all its keys agree with the representative
above the bottom chunk. -/
theorem aligned_tip (pfx : Nat) (bits : UInt32) (hb : bits ≠ 0) (l : Nat) (hl : 0 < l) :
    AlignedAt l (chunk (someKey (.tip pfx bits)) l) (prefixAbove (someKey (.tip pfx bits)) l)
      (.tip pfx bits) := by
  intro k hk
  rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hk
  have hk5 : k >>> 5 = someKey (.tip pfx bits) >>> 5 := by
    rw [someKey_tip_shiftRight5 pfx bits hb]; exact hk.1
  exact ⟨chunk_eq_of_shiftRight_eq (shiftRight_mono_eq hk5 (by omega)),
         prefixAbove_eq_of_shiftRight_eq (shiftRight_mono_eq hk5 (by omega))⟩

/-- A well-formed `bin` is aligned at every level strictly above its own: all its keys share the
branch prefix `pfx`, hence agree above `level`. -/
theorem aligned_bin (pfx level : Nat) (mask : UInt32) (kids : Array PTree)
    (hwf : WF (.bin pfx level mask kids)) (l : Nat) (hl : level < l) :
    AlignedAt l (chunk (someKey (.bin pfx level mask kids)) l)
      (prefixAbove (someKey (.bin pfx level mask kids)) l) (.bin pfx level mask kids) := by
  rw [WF] at hwf
  obtain ⟨_, _, hpc, _, _, hrout⟩ := hwf
  have hm : mask ≠ 0 := by
    intro h; rw [h, show popCount 0 = 0 from rfl] at hpc; omega
  intro k hk
  rw [contains_bin, Bool.and_eq_true] at hk
  obtain ⟨htb, hcc⟩ := hk
  have hkp : prefixAbove k level = pfx :=
    (hrout (chunk k level) (chunk_lt _ _) htb k hcc).2
  have hsp : prefixAbove (someKey (.bin pfx level mask kids)) level = pfx :=
    someKey_bin_prefixAbove pfx level mask kids hm
  have hkey : k >>> (5 * (level + 1)) = someKey (.bin pfx level mask kids) >>> (5 * (level + 1)) := by
    show prefixAbove k level = prefixAbove (someKey (.bin pfx level mask kids)) level
    rw [hkp, hsp]
  exact ⟨chunk_eq_of_shiftRight_eq (shiftRight_mono_eq hkey (by omega)),
         prefixAbove_eq_of_shiftRight_eq (shiftRight_mono_eq hkey (by omega))⟩

/-! ### Branch-level facts

`branchLevel ka kb = requiredHeight (ka ^^^ kb)` is the level a `join ka _ kb _` branches at. These
pin down what the `join` seams need at the call site: the two keys agree above the branch level (so
the shared prefix is well-defined) and the level is high enough to sit above an existing subtree. -/

private theorem pow32_eq (n : Nat) : (32 : Nat) ^ n = 2 ^ (5 * n) := by
  rw [show (32 : Nat) = 2 ^ 5 from rfl, ← Nat.pow_mul]

/-- If two keys' xor is below `2^m`, they agree on all bits at/above `m`. -/
private theorem shiftRight_eq_of_xor_lt {x y m : Nat} (h : x ^^^ y < 2 ^ m) :
    x >>> m = y >>> m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  have hf : Nat.testBit (x ^^^ y) (m + i) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
  rw [Nat.testBit_xor] at hf
  revert hf
  cases Nat.testBit x (m + i) <;> cases Nat.testBit y (m + i) <;> simp

/-- Two keys agree above their branch level: the join's shared prefix is well-defined. -/
theorem prefixAbove_branchLevel_eq (ka kb : Nat) :
    prefixAbove ka (branchLevel ka kb) = prefixAbove kb (branchLevel ka kb) := by
  unfold prefixAbove branchLevel
  apply shiftRight_eq_of_xor_lt
  rw [← pow32_eq]
  exact lt_pow_of_requiredHeight_le (Nat.le_refl _)

/-- A high-bit divergence forces a positive branch level (the tip join always branches at `≥ 1`). -/
theorem branchLevel_pos (k kb : Nat) (h : k >>> 5 ≠ kb >>> 5) : 0 < branchLevel k kb := by
  rcases Nat.eq_zero_or_pos (branchLevel k kb) with hz | hp
  · refine absurd ?_ h
    apply shiftRight_eq_of_xor_lt (m := 5)
    unfold branchLevel at hz
    have hlt := lt_pow_of_requiredHeight_le (h := 0) (Nat.le_of_eq hz)
    rw [pow32_eq] at hlt
    simpa using hlt
  · exact hp

/-- Divergence above a bin's level forces the branch level past it (the bin join branches deeper). -/
theorem lt_branchLevel (k kb level : Nat)
    (h : k >>> (5 * (level + 1)) ≠ kb >>> (5 * (level + 1))) : level < branchLevel k kb := by
  rcases Nat.lt_or_ge level (branchLevel k kb) with hlt | hge
  · exact hlt
  · refine absurd ?_ h
    apply shiftRight_eq_of_xor_lt (m := 5 * (level + 1))
    rw [← pow32_eq]
    apply lt_pow_of_requiredHeight_le
    unfold branchLevel at hge
    exact hge

/-- The bottom chunk of a xor is the xor of the operands' bottom chunks. -/
private theorem nchunk_xor (ka kb l : Nat) :
    ((ka ^^^ kb) >>> (5 * l)) &&& 31
      = ((ka >>> (5 * l)) &&& 31) ^^^ ((kb >>> (5 * l)) &&& 31) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_xor]
  cases Nat.testBit ka (5 * l + i) <;> cases Nat.testBit kb (5 * l + i) <;>
    cases Nat.testBit 31 i <;> rfl

private theorem chunk_xor_eq_zero_of_chunk_eq {ka kb l : Nat} (h : chunk ka l = chunk kb l) :
    chunk (ka ^^^ kb) l = 0 := by
  have E : (ka >>> (5 * l)) &&& 31 = (kb >>> (5 * l)) &&& 31 := by
    have h' : UInt32.ofNat ((ka >>> (5 * l)) &&& 31) = UInt32.ofNat ((kb >>> (5 * l)) &&& 31) := h
    have := congrArg UInt32.toNat h'
    rwa [UInt32.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt Nat.and_le_right (by decide)),
         UInt32.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))] at this
  show UInt32.ofNat (((ka ^^^ kb) >>> (5 * l)) &&& 31) = 0
  rw [nchunk_xor, E, Nat.xor_self]; rfl

private theorem xor_ne_zero_of_ne {ka kb : Nat} (h : ka ≠ kb) : ka ^^^ kb ≠ 0 := by
  intro h0
  apply h
  have : ka ^^^ kb ^^^ kb = 0 ^^^ kb := by rw [h0]
  rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at this

private theorem chunk_branchLevel_xor_ne_zero (ka kb : Nat) (h : ka ≠ kb) :
    chunk (ka ^^^ kb) (branchLevel ka kb) ≠ 0 := by
  have hx : ka ^^^ kb ≠ 0 := xor_ne_zero_of_ne h
  unfold branchLevel
  rcases Nat.eq_zero_or_pos (requiredHeight (ka ^^^ kb)) with hL | hL
  · rw [hL]
    have hlt : ka ^^^ kb < 2 ^ 5 := by
      have := lt_pow_of_requiredHeight_le (h := 0) (Nat.le_of_eq hL)
      rw [pow32_eq] at this; simpa using this
    show UInt32.ofNat (((ka ^^^ kb) >>> (5 * 0)) &&& 31) ≠ 0
    rw [Nat.mul_zero, Nat.shiftRight_zero, show (31 : Nat) = 2 ^ 5 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
    intro hzero
    apply hx
    have := congrArg UInt32.toNat hzero
    rwa [UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hlt (by decide)),
         show (0 : UInt32).toNat = 0 from rfl] at this
  · have he : (requiredHeight (ka ^^^ kb) - 1) + 1 = requiredHeight (ka ^^^ kb) := by omega
    rw [← he]
    exact chunk_ne_zero_of_requiredHeight_eq (by omega)

/-- The two slots a `join ka _ kb _` branches at are distinct, so its 2-child `bin` is well-formed
(the `hne` the `join` seams demand). -/
theorem chunk_branchLevel_ne (ka kb : Nat) (h : ka ≠ kb) :
    chunk ka (branchLevel ka kb) ≠ chunk kb (branchLevel ka kb) := fun heq =>
  chunk_branchLevel_xor_ne_zero ka kb h (chunk_xor_eq_zero_of_chunk_eq heq)

/-! ### The `insert` seams

`contains_insert` — the `get?_insert` analogue — characterizes membership after an insert. The two
stitching lemmas below wrap the singleton/join shapes; the three `childAt_*` array lemmas describe
how a present slot's child, a freshly-spliced slot, and the other slots read after the compact-array
update `insert` performs. -/

/-- Membership in a singleton, as a `Bool` (the `decide`-free form the extensionality proofs use). -/
theorem contains_singleton_eq (j k : Nat) : contains j (singleton k) = (j == k) := by
  rw [Bool.eq_iff_iff, contains_singleton, beq_iff_eq]

/-- Membership in a `join` of two slot-aligned subtrees, stated directly on `join` (unfolds the
branch arithmetic once so the call sites need only supply the alignments). -/
theorem contains_join_eq (j ka kb : Nat) (a b : PTree) (hne : ka ≠ kb)
    (ha : AlignedAt (branchLevel ka kb) (chunk ka (branchLevel ka kb))
            (prefixAbove ka (branchLevel ka kb)) a)
    (hb : AlignedAt (branchLevel ka kb) (chunk kb (branchLevel ka kb))
            (prefixAbove ka (branchLevel ka kb)) b) :
    contains j (join ka a kb b) = (contains j a || contains j b) := by
  rw [join]
  exact contains_join j (prefixAbove ka (branchLevel ka kb)) (branchLevel ka kb)
    (chunk ka (branchLevel ka kb)) (chunk kb (branchLevel ka kb)) a b
    (chunk_lt _ _) (chunk_lt _ _) (chunk_branchLevel_ne ka kb hne) ha hb

/-- Overwriting present slot `c`'s child: any other present slot reads through unchanged. -/
private theorem childAt_setIfInBounds (mask c cj : UInt32) (kids : Array PTree) (nc : PTree)
    (hc : c < 32) (hcj : cj < 32) (htc : testBit mask c = true) (htcj : testBit mask cj = true)
    (hsize : kids.size = popCount mask) :
    childAt mask (kids.setIfInBounds (arrayIndex mask c) nc) cj
      = if cj = c then nc else childAt mask kids cj := by
  unfold childAt
  rw [Array.getElem?_setIfInBounds]
  have hlt : arrayIndex mask c < kids.size := by rw [hsize]; exact arrayIndex_lt mask c htc
  by_cases hjc : cj = c
  · subst hjc; rw [if_pos rfl, if_pos hlt, Option.getD_some, if_pos rfl]
  · rw [if_neg (arrayIndex_inj mask c cj hc hcj htc htcj (Ne.symm hjc)), if_neg hjc]

/-- Reading the freshly-inserted slot `c` yields the new child. -/
private theorem childAt_insertIdx_self (mask c : UInt32) (kids : Array PTree) (nc : PTree)
    (hsize : kids.size = popCount mask) :
    childAt (setBit mask c) (kids.insertIdx! (arrayIndex mask c) nc) c = nc := by
  unfold childAt
  have hle : arrayIndex mask c ≤ kids.size := by rw [hsize]; exact arrayIndex_le mask c
  rw [arrayIndex_setBit_self, show kids.insertIdx! (arrayIndex mask c) nc
        = kids.insertIdx (arrayIndex mask c) nc hle from dif_pos hle,
      Array.getElem?_insertIdx_self hle, Option.getD_some]

/-- Splicing a fresh slot `c` leaves every other present slot's child reachable (its compact index
shifts with the insertion but still names the same element). -/
private theorem childAt_insertIdx_of_ne (mask c cj : UInt32) (kids : Array PTree) (nc : PTree)
    (hc : c < 32) (hcj : cj < 32) (hne : cj ≠ c) (htc : testBit mask c = false)
    (htcj : testBit mask cj = true) (hsize : kids.size = popCount mask) :
    childAt (setBit mask c) (kids.insertIdx! (arrayIndex mask c) nc) cj = childAt mask kids cj := by
  unfold childAt
  have hle : arrayIndex mask c ≤ kids.size := by rw [hsize]; exact arrayIndex_le mask c
  rw [show kids.insertIdx! (arrayIndex mask c) nc = kids.insertIdx (arrayIndex mask c) nc hle
        from dif_pos hle]
  rcases lt_or_gt_uint32 hne with hlt | hgt
  · rw [arrayIndex_setBit_of_le mask c cj hc hcj (uint32_le_of_lt hlt),
        Array.getElem?_insertIdx_of_lt hle (arrayIndex_lt_of_lt mask cj c hcj hc htcj hlt)]
  · rw [arrayIndex_setBit_of_gt mask c cj hc hcj hgt htc, Array.getElem?_insertIdx hle,
        if_neg (by have := arrayIndex_le_of_le mask c cj hc hcj (uint32_le_of_lt hgt); omega),
        if_neg (by have := arrayIndex_le_of_le mask c cj hc hcj (uint32_le_of_lt hgt); omega),
        Nat.add_sub_cancel]

set_option linter.unusedVariables false in
/-- `get?_insert` for the set: membership after `insert k` adds exactly `k`. The single point of
contact between the lattice/order proofs and `insert`'s structural code. -/
theorem contains_insert (k j : Nat) :
    ∀ (t : PTree), WF t → contains j (insert k t) = ((j == k) || contains j t) := by
  intro t
  induction t using insert.induct (k := k) with
  | case1 =>
    intro _
    rw [insert, contains_singleton_eq, contains_nil, Bool.or_false]
  | case2 pfx bits hmatch =>
    intro _
    rw [insert, if_pos hmatch, contains_tip, contains_tip,
        testBit_setBit bits (chunk k 0) (chunk j 0) (chunk_lt _ _) (chunk_lt _ _)]
    have hk5 : k >>> 5 = pfx := by simpa using hmatch
    have hdec : (j == k) = ((j >>> 5 == pfx) && (chunk k 0 == chunk j 0)) := by
      rw [Bool.eq_iff_iff, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq, key_eq_iff j k, hk5]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
    rw [hdec]
    cases (j >>> 5 == pfx) <;> cases testBit bits (chunk j 0) <;>
      cases (chunk k 0 == chunk j 0) <;> rfl
  | case3 pfx bits hmatch =>
    intro hwf
    have hbits : bits ≠ 0 := by rw [WF] at hwf; exact hwf
    have hsk : someKey (.tip pfx bits) >>> 5 = pfx := someKey_tip_shiftRight5 pfx bits hbits
    have hkne5 : k >>> 5 ≠ someKey (.tip pfx bits) >>> 5 := by
      rw [hsk]; intro h; exact hmatch (by rw [h]; exact beq_self_eq_true pfx)
    have hkne : k ≠ someKey (.tip pfx bits) := fun h => hkne5 (by rw [h])
    rw [insert, if_neg hmatch,
        show ((pfx <<< 5) ||| (lowestSetIdx bits).toNat) = someKey (.tip pfx bits) from rfl,
        contains_join_eq j k (someKey (.tip pfx bits)) (singleton k) (.tip pfx bits) hkne ?ha ?hb,
        contains_singleton_eq]
    case ha =>
      intro k' hk'; rw [show k' = k from (contains_singleton k' k).mp hk']; exact ⟨rfl, rfl⟩
    case hb =>
      rw [prefixAbove_branchLevel_eq k (someKey (.tip pfx bits))]
      exact aligned_tip pfx bits hbits _ (branchLevel_pos k _ hkne5)
  | case4 pfx level mask kids hpfx htb h IH =>
    intro hwf
    rw [WF] at hwf
    obtain ⟨_, hsize, _, hkidswf, _⟩ := hwf
    have hwfchild : WF kids[arrayIndex mask (chunk k level)] := hkidswf _ (Array.getElem_mem h)
    have hclt : chunk k level < 32 := chunk_lt k level
    have hcjlt : chunk j level < 32 := chunk_lt j level
    have hcAc : childAt mask kids (chunk k level) = kids[arrayIndex mask (chunk k level)] := by
      unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
    rw [insert, if_pos hpfx, if_pos htb, dif_pos h, contains_bin, contains_bin]
    by_cases hcjc : chunk j level = chunk k level
    · rw [hcjc,
          childAt_setIfInBounds mask (chunk k level) (chunk k level) kids _ hclt hclt htb htb hsize,
          if_pos rfl, IH hwfchild, hcAc]
      simp only [htb, Bool.true_and]
    · have hjkf : (j == k) = false := beq_eq_false_iff_ne.mpr (fun he => hcjc (by rw [he]))
      rw [hjkf, Bool.false_or]
      by_cases htcj : testBit mask (chunk j level) = true
      · rw [childAt_setIfInBounds mask (chunk k level) (chunk j level) kids _ hclt hcjlt htb htcj hsize,
            if_neg hcjc]
      · rw [show testBit mask (chunk j level) = false from by simpa using htcj,
            Bool.false_and, Bool.false_and]
  | case5 pfx level mask kids hpfx htb hnh =>
    intro hwf
    exfalso
    rw [WF] at hwf
    obtain ⟨_, hsize, _, _, _, _⟩ := hwf
    exact hnh (by rw [hsize]; exact arrayIndex_lt mask (chunk k level) htb)
  | case6 pfx level mask kids hpfx htb =>
    intro hwf
    have hsize : kids.size = popCount mask := by rw [WF] at hwf; exact hwf.2.1
    have hclt : chunk k level < 32 := chunk_lt k level
    have hcjlt : chunk j level < 32 := chunk_lt j level
    have htbf : testBit mask (chunk k level) = false := by simpa using htb
    rw [insert, if_pos hpfx, if_neg htb, contains_bin, contains_bin]
    by_cases hcjc : chunk j level = chunk k level
    · rw [hcjc, testBit_setBit mask (chunk k level) (chunk k level) hclt hclt, beq_self_eq_true,
          Bool.or_true, Bool.true_and,
          childAt_insertIdx_self mask (chunk k level) kids (singleton k) hsize,
          contains_singleton_eq, htbf, Bool.false_and, Bool.or_false]
    · have hjkf : (j == k) = false := beq_eq_false_iff_ne.mpr (fun he => hcjc (by rw [he]))
      rw [testBit_setBit mask (chunk k level) (chunk j level) hclt hcjlt,
          beq_eq_false_iff_ne.mpr (Ne.symm hcjc), Bool.or_false, hjkf, Bool.false_or]
      by_cases htcj : testBit mask (chunk j level) = true
      · rw [childAt_insertIdx_of_ne mask (chunk k level) (chunk j level) kids (singleton k)
              hclt hcjlt hcjc htbf htcj hsize]
      · rw [show testBit mask (chunk j level) = false from by simpa using htcj,
            Bool.false_and, Bool.false_and]
  | case7 pfx level mask kids hpfx =>
    intro hwf
    have hmne : mask ≠ 0 := by
      have h2 := hwf; rw [WF] at h2; obtain ⟨_, _, hpc, _, _, _⟩ := h2
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hsk : prefixAbove (someKey (.bin pfx level mask kids)) level = pfx :=
      someKey_bin_prefixAbove pfx level mask kids hmne
    have hkne5 :
        k >>> (5 * (level + 1)) ≠ someKey (.bin pfx level mask kids) >>> (5 * (level + 1)) := by
      show prefixAbove k level ≠ prefixAbove (someKey (.bin pfx level mask kids)) level
      rw [hsk]; intro h; exact hpfx (by rw [h]; exact beq_self_eq_true pfx)
    have hkne : k ≠ someKey (.bin pfx level mask kids) := fun h => hkne5 (by rw [h])
    rw [insert, if_neg hpfx,
        contains_join_eq j k (someKey (.bin pfx level mask kids)) (singleton k)
          (.bin pfx level mask kids) hkne ?ha ?hb, contains_singleton_eq]
    case ha =>
      intro k' hk'; rw [show k' = k from (contains_singleton k' k).mp hk']; exact ⟨rfl, rfl⟩
    case hb =>
      rw [prefixAbove_branchLevel_eq k (someKey (.bin pfx level mask kids))]
      exact aligned_bin pfx level mask kids hwf _ (lt_branchLevel k _ level hkne5)

set_option linter.unusedVariables false in
/-- `insert` preserves the canonical shape. The routing invariant for a modified or freshly-spliced
slot is discharged by `contains_insert`: the new child holds exactly the old keys plus `k`, all of
which align under that slot's chunk and the branch prefix. -/
theorem WF_insert (k : Nat) : ∀ (t : PTree), WF t → WF (insert k t) := by
  intro t
  induction t using insert.induct (k := k) with
  | case1 => intro _; rw [insert]; exact WF_singleton k
  | case2 pfx bits hmatch =>
    intro _; rw [insert, if_pos hmatch, WF]; exact setBit_ne_zero bits (chunk k 0)
  | case3 pfx bits hmatch =>
    intro hwf
    have hbits : bits ≠ 0 := by rw [WF] at hwf; exact hwf
    have hsk : someKey (.tip pfx bits) >>> 5 = pfx := someKey_tip_shiftRight5 pfx bits hbits
    have hkne5 : k >>> 5 ≠ someKey (.tip pfx bits) >>> 5 := by
      rw [hsk]; intro h; exact hmatch (by rw [h]; exact beq_self_eq_true pfx)
    have hkne : k ≠ someKey (.tip pfx bits) := fun h => hkne5 (by rw [h])
    have hl0 : 0 < branchLevel k (someKey (.tip pfx bits)) := branchLevel_pos k _ hkne5
    rw [insert, if_neg hmatch,
        show ((pfx <<< 5) ||| (lowestSetIdx bits).toNat) = someKey (.tip pfx bits) from rfl, join]
    refine WF_join _ _ _ _ (singleton k) (.tip pfx bits) hl0 (chunk_lt _ _) (chunk_lt _ _)
      (chunk_branchLevel_ne k _ hkne) ?ha ?hb (WF_singleton k) hwf (singleton_ne_nil k) (by simp)
    case ha =>
      intro k' hk'; rw [show k' = k from (contains_singleton k' k).mp hk']; exact ⟨rfl, rfl⟩
    case hb =>
      rw [prefixAbove_branchLevel_eq k (someKey (.tip pfx bits))]
      exact aligned_tip pfx bits hbits _ hl0
  | case4 pfx level mask kids hpfx htb h IH =>
    intro hwf
    rw [WF] at hwf
    obtain ⟨hlvl, hsize, hpc, hkidswf, hnonnil, hrout⟩ := hwf
    have hwfchild : WF kids[arrayIndex mask (chunk k level)] := hkidswf _ (Array.getElem_mem h)
    have hclt : chunk k level < 32 := chunk_lt k level
    have hpfxeq : prefixAbove k level = pfx := by simpa using hpfx
    have hcAc : childAt mask kids (chunk k level) = kids[arrayIndex mask (chunk k level)] := by
      unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
    have halignChild : AlignedAt level (chunk k level) pfx kids[arrayIndex mask (chunk k level)] := by
      have := hrout (chunk k level) hclt htb; rwa [hcAc] at this
    have halignNew : AlignedAt level (chunk k level) pfx
        (insert k kids[arrayIndex mask (chunk k level)]) := by
      intro j hj
      rw [contains_insert k j _ hwfchild, Bool.or_eq_true, beq_iff_eq] at hj
      rcases hj with rfl | hjc
      · exact ⟨rfl, hpfxeq⟩
      · exact halignChild j hjc
    rw [insert, if_pos hpfx, if_pos htb, dif_pos h, WF]
    refine ⟨hlvl, ?_, hpc, ?_, ?_, ?_⟩
    · rw [Array.size_setIfInBounds]; exact hsize
    · intro c' hc'
      rcases Array.mem_or_eq_of_mem_setIfInBounds hc' with hmem | heq
      · exact hkidswf c' hmem
      · rw [heq]; exact IH hwfchild
    · intro c' hc'
      rcases Array.mem_or_eq_of_mem_setIfInBounds hc' with hmem | heq
      · exact hnonnil c' hmem
      · rw [heq]; exact insert_ne_nil k _
    · intro c' hc'lt htc'
      by_cases hc'c : c' = chunk k level
      · subst hc'c
        rw [childAt_setIfInBounds mask (chunk k level) (chunk k level) kids _ hclt hclt htb htc' hsize,
            if_pos rfl]
        exact halignNew
      · rw [childAt_setIfInBounds mask (chunk k level) c' kids _ hclt hc'lt htb htc' hsize,
            if_neg hc'c]
        exact hrout c' hc'lt htc'
  | case5 pfx level mask kids hpfx htb hnh =>
    intro hwf
    exfalso
    rw [WF] at hwf
    obtain ⟨_, hsize, _, _, _, _⟩ := hwf
    exact hnh (by rw [hsize]; exact arrayIndex_lt mask (chunk k level) htb)
  | case6 pfx level mask kids hpfx htb =>
    intro hwf
    rw [WF] at hwf
    obtain ⟨hlvl, hsize, hpc, hkidswf, hnonnil, hrout⟩ := hwf
    have hclt : chunk k level < 32 := chunk_lt k level
    have htbf : testBit mask (chunk k level) = false := by simpa using htb
    have hpfxeq : prefixAbove k level = pfx := by simpa using hpfx
    have hpcnew : popCount (setBit mask (chunk k level)) = popCount mask + 1 :=
      popCount_setBit mask (chunk k level) htbf
    have hle : arrayIndex mask (chunk k level) ≤ kids.size := by rw [hsize]; exact arrayIndex_le _ _
    have hidx : kids.insertIdx! (arrayIndex mask (chunk k level)) (singleton k)
        = kids.insertIdx (arrayIndex mask (chunk k level)) (singleton k) hle := dif_pos hle
    rw [insert, if_pos hpfx, if_neg htb, WF]
    refine ⟨hlvl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hidx, Array.size_insertIdx, hsize, hpcnew]
    · rw [hpcnew]; omega
    · intro c' hc'
      rw [hidx] at hc'
      rcases Array.mem_insertIdx.mp hc' with heq | hmem
      · rw [heq]; exact WF_singleton k
      · exact hkidswf c' hmem
    · intro c' hc'
      rw [hidx] at hc'
      rcases Array.mem_insertIdx.mp hc' with heq | hmem
      · rw [heq]; exact singleton_ne_nil k
      · exact hnonnil c' hmem
    · intro c' hc'lt htc'
      by_cases hc'c : c' = chunk k level
      · subst hc'c
        rw [childAt_insertIdx_self mask (chunk k level) kids (singleton k) hsize]
        intro j hj
        rw [contains_singleton] at hj; subst hj
        exact ⟨rfl, hpfxeq⟩
      · have htcm : testBit mask c' = true := by
          rw [testBit_setBit mask (chunk k level) c' hclt hc'lt,
              beq_eq_false_iff_ne.mpr (Ne.symm hc'c), Bool.or_false] at htc'
          exact htc'
        rw [childAt_insertIdx_of_ne mask (chunk k level) c' kids (singleton k)
              hclt hc'lt hc'c htbf htcm hsize]
        exact hrout c' hc'lt htcm
  | case7 pfx level mask kids hpfx =>
    intro hwf
    have hmne : mask ≠ 0 := by
      have h2 := hwf; rw [WF] at h2; obtain ⟨_, _, hpc, _, _, _⟩ := h2
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hsk : prefixAbove (someKey (.bin pfx level mask kids)) level = pfx :=
      someKey_bin_prefixAbove pfx level mask kids hmne
    have hkne5 :
        k >>> (5 * (level + 1)) ≠ someKey (.bin pfx level mask kids) >>> (5 * (level + 1)) := by
      show prefixAbove k level ≠ prefixAbove (someKey (.bin pfx level mask kids)) level
      rw [hsk]; intro h; exact hpfx (by rw [h]; exact beq_self_eq_true pfx)
    have hkne : k ≠ someKey (.bin pfx level mask kids) := fun h => hkne5 (by rw [h])
    have hlvl0 : 0 < level := by rw [WF] at hwf; exact hwf.1
    have hl0 : 0 < branchLevel k (someKey (.bin pfx level mask kids)) :=
      Nat.lt_trans hlvl0 (lt_branchLevel k _ level hkne5)
    rw [insert, if_neg hpfx, join]
    refine WF_join _ _ _ _ (singleton k) (.bin pfx level mask kids) hl0 (chunk_lt _ _)
      (chunk_lt _ _) (chunk_branchLevel_ne k _ hkne) ?ha ?hb (WF_singleton k) hwf
      (singleton_ne_nil k) (by simp)
    case ha =>
      intro k' hk'; rw [show k' = k from (contains_singleton k' k).mp hk']; exact ⟨rfl, rfl⟩
    case hb =>
      rw [prefixAbove_branchLevel_eq k (someKey (.bin pfx level mask kids))]
      exact aligned_bin pfx level mask kids hwf _ (lt_branchLevel k _ level hkne5)

/-- Building from a list keeps the trie canonical (repeated `insert` from the empty trie). -/
theorem WF_ofList (ks : List Nat) : WF (ofList ks) := by
  unfold ofList
  suffices h : ∀ (l : List Nat) (s : PTree), WF s → WF (l.foldl (fun s k => s.insert k) s) by
    exact h ks .nil WF_empty
  intro l
  induction l with
  | nil => intro s hs; exact hs
  | cons a t ih => intro s hs; exact ih (s.insert a) (WF_insert a s hs)

/-! ### The `union` present-slot fold

The aligned-`bin` case of `unionU` rebuilds the child array with `mergeKids`, a present-slot fold
over the combined mask `m1 ||| m2` that appends one `mergeChild` per set bit (lowest first). These
structural facts characterize that array independently of `mergeChild`'s contents: its size, and
that reading slot `c` back (via `childAt` on the merged mask) recovers `mergeChild … c`. They are
the bridge the union membership/`WF` seams cross to reach the per-slot `mergeChild` reasoning. -/

/-- The fold's running invariant: starting from `acc`, processing `rem`'s set bits lowest-first
appends one child per bit. Stated by strong induction on `rem.toNat` (each step clears the lowest
bit): the result keeps `acc` as a prefix, grows by `popCount rem`, and lands each remaining set
bit's `mergeChild` at its compact index past `acc`. -/
private theorem mergeKids_spec (m1 : UInt32) (k1 : Array PTree) (m2 : UInt32) (k2 : Array PTree) :
    ∀ (n : Nat) (rem : UInt32), rem.toNat = n → ∀ (acc : Array PTree),
      (mergeKids m1 k1 m2 k2 rem acc).size = acc.size + popCount rem
      ∧ (∀ i, i < acc.size → (mergeKids m1 k1 m2 k2 rem acc)[i]? = acc[i]?)
      ∧ (∀ c, c < 32 → testBit rem c = true →
           (mergeKids m1 k1 m2 k2 rem acc)[acc.size + arrayIndex rem c]?
             = some (mergeChild m1 k1 m2 k2 c)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro rem hrem acc
    by_cases h0 : (rem == 0) = true
    · have hr0 : rem = 0 := by simpa using h0
      rw [mergeKids, dif_pos h0]
      refine ⟨?_, ?_, ?_⟩
      · rw [hr0, show popCount (0 : UInt32) = 0 from rfl, Nat.add_zero]
      · intro i hi; rfl
      · intro c hc htb; rw [hr0, testBit_zero] at htb; exact absurd htb (by decide)
    · have hrem0 : rem ≠ 0 := by intro h; exact h0 (by rw [h]; rfl)
      have hstep : mergeKids m1 k1 m2 k2 rem acc
          = mergeKids m1 k1 m2 k2 (clearLowest rem)
              (acc.push (mergeChild m1 k1 m2 k2 (lowestSetIdx rem))) := by
        rw [mergeKids, dif_neg h0]
      have hlt : (clearLowest rem).toNat < n := by
        rw [← hrem]; exact UInt32.lt_iff_toNat_lt.mp (clearLowest_lt rem hrem0)
      obtain ⟨ihsize, ihpref, ihthird⟩ :=
        IH (clearLowest rem).toNat hlt (clearLowest rem) rfl
          (acc.push (mergeChild m1 k1 m2 k2 (lowestSetIdx rem)))
      have hpc : popCount (clearLowest rem) + 1 = popCount rem := popCount_clearLowest rem hrem0
      have haccsz : (acc.push (mergeChild m1 k1 m2 k2 (lowestSetIdx rem))).size = acc.size + 1 :=
        Array.size_push ..
      refine ⟨?_, ?_, ?_⟩
      · rw [hstep, ihsize, haccsz]; omega
      · intro i hi
        rw [hstep, ihpref i (by omega), Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]
      · intro c hc htb
        rw [hstep]
        by_cases hclo : c = lowestSetIdx rem
        · subst hclo
          rw [arrayIndex_lowestSetIdx rem hrem0, Nat.add_zero,
              ihpref acc.size (by omega), Array.getElem?_push_size]
        · have htb' : testBit (clearLowest rem) c = true := by
            rw [testBit_clearLowest_of_ne rem c hc hclo]; exact htb
          have hidx : arrayIndex rem c = arrayIndex (clearLowest rem) c + 1 :=
            arrayIndex_clearLowest_of_ne rem c hc htb hclo
          have key := ihthird c hc htb'
          rw [haccsz] at key
          rw [hidx, show acc.size + (arrayIndex (clearLowest rem) c + 1)
                = acc.size + 1 + arrayIndex (clearLowest rem) c from by omega]
          exact key

/-- Reading slot `c` (present in the merged mask) of the rebuilt child array recovers that slot's
`mergeChild`. The structural half of the aligned-`bin` union seam: it reduces `childAt` on the
merged `bin` to per-slot `mergeChild`, where the membership/`WF` reasoning then takes over. -/
theorem childAt_mergeKids (m1 : UInt32) (k1 : Array PTree) (m2 : UInt32) (k2 : Array PTree)
    (c : UInt32) (hc : c < 32) (htb : testBit (m1 ||| m2) c = true) :
    childAt (m1 ||| m2) (mergeKids m1 k1 m2 k2 (m1 ||| m2) #[]) c = mergeChild m1 k1 m2 k2 c := by
  obtain ⟨_, _, hthird⟩ := mergeKids_spec m1 k1 m2 k2 (m1 ||| m2).toNat (m1 ||| m2) rfl #[]
  have hc' := hthird c hc htb
  unfold childAt
  rw [show (#[] : Array PTree).size = 0 from rfl, Nat.zero_add] at hc'
  rw [hc', Option.getD_some]

/-- The rebuilt child array has exactly one slot per present bit of the merged mask — the compact
size invariant the merged `bin` needs to stay well-formed. -/
theorem size_mergeKids (m1 : UInt32) (k1 : Array PTree) (m2 : UInt32) (k2 : Array PTree) :
    (mergeKids m1 k1 m2 k2 (m1 ||| m2) #[]).size = popCount (m1 ||| m2) := by
  obtain ⟨hsize, _, _⟩ := mergeKids_spec m1 k1 m2 k2 (m1 ||| m2).toNat (m1 ||| m2) rfl #[]
  rw [hsize, show (#[] : Array PTree).size = 0 from rfl, Nat.zero_add]

/-- Every child the fold produces comes from either the seed `acc` or some present slot's
`mergeChild`. The membership companion to `mergeKids_spec`; feeds the non-`nil` clause of
`WF_unionU`'s aligned-`bin` case. -/
private theorem mergeKids_mem (m1 : UInt32) (k1 : Array PTree) (m2 : UInt32) (k2 : Array PTree) :
    ∀ (n : Nat) (rem : UInt32), rem.toNat = n → ∀ (acc : Array PTree) (x : PTree),
      x ∈ mergeKids m1 k1 m2 k2 rem acc →
        x ∈ acc ∨ ∃ c, testBit rem c = true ∧ x = mergeChild m1 k1 m2 k2 c := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro rem hrem acc x hx
    by_cases h0 : (rem == 0) = true
    · rw [mergeKids, dif_pos h0] at hx; exact Or.inl hx
    · have hrem0 : rem ≠ 0 := by intro h; exact h0 (by rw [h]; rfl)
      rw [mergeKids, dif_neg h0] at hx
      have hlt : (clearLowest rem).toNat < n := by
        rw [← hrem]; exact UInt32.lt_iff_toNat_lt.mp (clearLowest_lt rem hrem0)
      rcases IH (clearLowest rem).toNat hlt (clearLowest rem) rfl
          (acc.push (mergeChild m1 k1 m2 k2 (lowestSetIdx rem))) x hx with hacc | hex
      · rcases Array.mem_push.mp hacc with hin | heq
        · exact Or.inl hin
        · exact Or.inr ⟨lowestSetIdx rem, testBit_lowestSetIdx rem hrem0, heq⟩
      · obtain ⟨c, htb, hxc⟩ := hex
        exact Or.inr ⟨c, testBit_of_clearLowest rem c htb, hxc⟩

/-- A `bin`'s children, well-formed, non-`nil`, and compactly stored — the part of `WF` the per-slot
union reasoning (`mergeChild`/`mergeKids`) consumes, abstracted so the motives can carry it. -/
def KidsWF (mask : UInt32) (kids : Array PTree) : Prop :=
  kids.size = popCount mask ∧ (∀ c ∈ kids, WF c) ∧ (∀ c ∈ kids, c ≠ .nil)

/-- A key routing to a slot other than the one a subtree is aligned under is not in that subtree. -/
theorem contains_false_of_aligned {j : Nat} (l : Nat) (c : UInt32) (p : Nat) (t : PTree)
    (h : AlignedAt l c p t) (hj : chunk j l ≠ c) : contains j t = false := by
  cases hcon : contains j t with
  | true => exact absurd (h j hcon).1 hj
  | false => rfl

/-- Descend case shared by all four `unionU` quadrants: when an operand `op` routes to a *present*
slot `c` of a well-formed `bin`, the result overwrites that slot's child with `unionU child op`.
Membership splits on whether `j` routes to `c`; off-slot keys of `op` are killed by its alignment. -/
private theorem contains_descend (j : Nat) (op : PTree) (bp bl : Nat) (bm : UInt32) (bk : Array PTree)
    (c : UInt32) (hc : c < 32) (hbin : WF (.bin bp bl bm bk)) (halign : AlignedAt bl c bp op)
    (htb : testBit bm c = true) (hidx : arrayIndex bm c < bk.size)
    (IH : contains j (unionU (bk[arrayIndex bm c]'hidx) op)
            = (contains j (bk[arrayIndex bm c]'hidx) || contains j op)) :
    contains j (.bin bp bl bm (bk.setIfInBounds (arrayIndex bm c) (unionU (bk[arrayIndex bm c]'hidx) op)))
      = (contains j op || contains j (.bin bp bl bm bk)) := by
  have hsize : bk.size = popCount bm := by rw [WF] at hbin; exact hbin.2.1
  have hcAc : childAt bm bk c = bk[arrayIndex bm c]'hidx := by
    unfold childAt; rw [Array.getElem?_eq_getElem hidx, Option.getD_some]
  rw [contains_bin, contains_bin]
  by_cases hcj : chunk j bl = c
  · rw [hcj, childAt_setIfInBounds bm c c bk _ hc hc htb htb hsize, if_pos rfl, IH, htb,
        Bool.true_and, hcAc, Bool.true_and, Bool.or_comm]
  · by_cases htcj : testBit bm (chunk j bl) = true
    · rw [childAt_setIfInBounds bm c (chunk j bl) bk _ hc (chunk_lt j bl) htb htcj hsize, if_neg hcj,
          contains_false_of_aligned bl c bp op halign hcj, Bool.false_or]
    · simp only [Bool.not_eq_true] at htcj
      rw [htcj, contains_false_of_aligned bl c bp op halign hcj]
      simp only [Bool.false_and, Bool.or_false]

/-- Splice case shared by all four `unionU` quadrants: when an operand `op` routes to an *absent*
slot `c` of a well-formed `bin`, the result inserts `op` whole at the freshly-set slot. -/
private theorem contains_splice (j : Nat) (op : PTree) (bp bl : Nat) (bm : UInt32) (bk : Array PTree)
    (c : UInt32) (hc : c < 32) (hbin : WF (.bin bp bl bm bk)) (halign : AlignedAt bl c bp op)
    (htb : testBit bm c = false) :
    contains j (.bin bp bl (setBit bm c) (bk.insertIdx! (arrayIndex bm c) op))
      = (contains j op || contains j (.bin bp bl bm bk)) := by
  have hsize : bk.size = popCount bm := by rw [WF] at hbin; exact hbin.2.1
  rw [contains_bin, contains_bin]
  by_cases hcj : chunk j bl = c
  · subst hcj
    rw [testBit_setBit bm (chunk j bl) (chunk j bl) (chunk_lt j bl) (chunk_lt j bl), beq_self_eq_true,
        Bool.or_true, Bool.true_and, childAt_insertIdx_self bm (chunk j bl) bk op hsize, htb,
        Bool.false_and, Bool.or_false]
  · by_cases htcj : testBit bm (chunk j bl) = true
    · rw [testBit_setBit bm c (chunk j bl) hc (chunk_lt j bl), beq_eq_false_iff_ne.mpr (Ne.symm hcj),
          Bool.or_false, childAt_insertIdx_of_ne bm c (chunk j bl) bk op hc (chunk_lt j bl) hcj htb
            htcj hsize, contains_false_of_aligned bl c bp op halign hcj, Bool.false_or]
    · simp only [Bool.not_eq_true] at htcj
      rw [testBit_setBit bm c (chunk j bl) hc (chunk_lt j bl), htcj,
          beq_eq_false_iff_ne.mpr (Ne.symm hcj), contains_false_of_aligned bl c bp op halign hcj]
      simp only [Bool.or_self, Bool.false_and]

theorem contains_unionU (j : Nat) : ∀ (a b : PTree), WF a → WF b →
    contains j (unionU a b) = (contains j a || contains j b) := by
  intro a b
  induction a, b using unionU.induct
    (motive2 := fun m1 k1 m2 k2 rem _ =>
      KidsWF m1 k1 → KidsWF m2 k2 →
      (∀ c, c < 32 → testBit rem c = true → testBit (m1 ||| m2) c = true) →
      ∀ c, c < 32 → testBit rem c = true →
        contains j (mergeChild m1 k1 m2 k2 c)
          = ((testBit m1 c && contains j (childAt m1 k1 c))
              || (testBit m2 c && contains j (childAt m2 k2 c))))
    (motive3 := fun m1 k1 m2 k2 i =>
      KidsWF m1 k1 → KidsWF m2 k2 → i < 32 → (testBit m1 i || testBit m2 i) = true →
        contains j (mergeChild m1 k1 m2 k2 i)
          = ((testBit m1 i && contains j (childAt m1 k1 i))
              || (testBit m2 i && contains j (childAt m2 k2 i)))) with
  | case1 t => intro _ _; rw [unionU, contains_nil, Bool.false_or]
  | case2 s hs => intro _ _; rw [unionU, contains_nil, Bool.or_false]; exact hs
  | case3 p1 b1 p2 b2 heq =>
    intro _ _
    have hp : p1 = p2 := by simpa using heq
    rw [unionU, if_pos heq, contains_tip, contains_tip, contains_tip, ← hp, testBit_or,
        Bool.and_or_distrib_left]
  | case4 p1 b1 p2 b2 hne =>
    intro hwf1 hwf2
    have hb1 : b1 ≠ 0 := by rw [WF] at hwf1; exact hwf1
    have hb2 : b2 ≠ 0 := by rw [WF] at hwf2; exact hwf2
    have hpne : p1 ≠ p2 := fun h => hne (by rw [h]; exact beq_self_eq_true p2)
    have hsk1 : someKey (.tip p1 b1) >>> 5 = p1 := someKey_tip_shiftRight5 p1 b1 hb1
    have hsk2 : someKey (.tip p2 b2) >>> 5 = p2 := someKey_tip_shiftRight5 p2 b2 hb2
    have hkne : someKey (.tip p1 b1) ≠ someKey (.tip p2 b2) := by
      intro h; apply hpne; rw [← hsk1, ← hsk2, h]
    have hkne5 : someKey (.tip p1 b1) >>> 5 ≠ someKey (.tip p2 b2) >>> 5 := by
      rw [hsk1, hsk2]; exact hpne
    rw [unionU, if_neg hne,
        contains_join_eq j (someKey (.tip p1 b1)) (someKey (.tip p2 b2)) (.tip p1 b1) (.tip p2 b2)
          hkne ?ha ?hb]
    case ha => exact aligned_tip p1 b1 hb1 _ (branchLevel_pos _ _ hkne5)
    case hb =>
      rw [prefixAbove_branchLevel_eq (someKey (.tip p1 b1)) (someKey (.tip p2 b2))]
      exact aligned_tip p2 b2 hb2 _ (branchLevel_pos _ _ hkne5)
  | case5 p1 b1 bp bl bm bk hpfx htb h IH =>
    intro hwf1 hwf2
    have hb1 : b1 ≠ 0 := by rw [WF] at hwf1; exact hwf1
    have hbl0 : 0 < bl := by rw [WF] at hwf2; exact hwf2.1
    have hwfchild : WF (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h) := by
      rw [WF] at hwf2; exact hwf2.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.tip p1 b1)) bl = bp := by simpa using hpfx
    have halign : AlignedAt bl (chunk (someKey (.tip p1 b1)) bl) bp (.tip p1 b1) :=
      hpfxeq ▸ aligned_tip p1 b1 hb1 bl hbl0
    rw [unionU, if_pos hpfx, if_pos htb, dif_pos h]
    exact contains_descend j (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl)
      (chunk_lt _ _) hwf2 halign htb h (IH hwfchild hwf1)
  | case6 p1 b1 bp bl bm bk hpfx htb hnh =>
    intro _ hwf2
    have hsize : bk.size = popCount bm := by rw [WF] at hwf2; exact hwf2.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt bm _ htb) hnh
  | case7 p1 b1 bp bl bm bk hpfx hntb =>
    intro hwf1 hwf2
    have hb1 : b1 ≠ 0 := by rw [WF] at hwf1; exact hwf1
    have hbl0 : 0 < bl := by rw [WF] at hwf2; exact hwf2.1
    have hpfxeq : prefixAbove (someKey (.tip p1 b1)) bl = bp := by simpa using hpfx
    have halign : AlignedAt bl (chunk (someKey (.tip p1 b1)) bl) bp (.tip p1 b1) :=
      hpfxeq ▸ aligned_tip p1 b1 hb1 bl hbl0
    have htbf : testBit bm (chunk (someKey (.tip p1 b1)) bl) = false := by simpa using hntb
    rw [unionU, if_pos hpfx, if_neg hntb]
    exact contains_splice j (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl)
      (chunk_lt _ _) hwf2 halign htbf
  | case8 p1 b1 bp bl bm bk hnpfx =>
    intro hwf1 hwf2
    have hb1 : b1 ≠ 0 := by rw [WF] at hwf1; exact hwf1
    have hbl0 : 0 < bl := by rw [WF] at hwf2; exact hwf2.1
    have hmne : bm ≠ 0 := by
      rw [WF] at hwf2; obtain ⟨_, _, hpc, _, _, _⟩ := hwf2
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hskbin : prefixAbove (someKey (.bin bp bl bm bk)) bl = bp :=
      someKey_bin_prefixAbove bp bl bm bk hmne
    have hpfxne : prefixAbove (someKey (.tip p1 b1)) bl ≠ bp := by
      intro h; exact hnpfx (by rw [h]; exact beq_self_eq_true bp)
    have hdiv : someKey (.bin bp bl bm bk) >>> (5 * (bl + 1))
        ≠ someKey (.tip p1 b1) >>> (5 * (bl + 1)) := by
      show prefixAbove (someKey (.bin bp bl bm bk)) bl ≠ prefixAbove (someKey (.tip p1 b1)) bl
      rw [hskbin]; exact fun h => hpfxne h.symm
    have hkne : someKey (.bin bp bl bm bk) ≠ someKey (.tip p1 b1) := fun h => hdiv (by rw [h])
    have hbl_lt : bl < branchLevel (someKey (.bin bp bl bm bk)) (someKey (.tip p1 b1)) :=
      lt_branchLevel _ _ bl hdiv
    rw [unionU, if_neg hnpfx,
        contains_join_eq j (someKey (.bin bp bl bm bk)) (someKey (.tip p1 b1)) (.bin bp bl bm bk)
          (.tip p1 b1) hkne ?ha ?hb]
    · exact Bool.or_comm _ _
    case ha => exact aligned_bin bp bl bm bk hwf2 _ hbl_lt
    case hb =>
      rw [prefixAbove_branchLevel_eq (someKey (.bin bp bl bm bk)) (someKey (.tip p1 b1))]
      exact aligned_tip p1 b1 hb1 _ (Nat.lt_trans hbl0 hbl_lt)
  | case9 bp bl bm bk p2 b2 hpfx htb h IH =>
    intro hwfbin hwftip
    have hb2 : b2 ≠ 0 := by rw [WF] at hwftip; exact hwftip
    have hbl0 : 0 < bl := by rw [WF] at hwfbin; exact hwfbin.1
    have hwfchild : WF (bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h) := by
      rw [WF] at hwfbin; exact hwfbin.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.tip p2 b2)) bl = bp := by simpa using hpfx
    have halign : AlignedAt bl (chunk (someKey (.tip p2 b2)) bl) bp (.tip p2 b2) :=
      hpfxeq ▸ aligned_tip p2 b2 hb2 bl hbl0
    rw [unionU, if_pos hpfx, if_pos htb, dif_pos h,
        contains_descend j (.tip p2 b2) bp bl bm bk (chunk (someKey (.tip p2 b2)) bl)
          (chunk_lt _ _) hwfbin halign htb h (IH hwfchild hwftip)]
    exact Bool.or_comm _ _
  | case10 bp bl bm bk p2 b2 hpfx htb hnh =>
    intro hwfbin _
    have hsize : bk.size = popCount bm := by rw [WF] at hwfbin; exact hwfbin.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt bm _ htb) hnh
  | case11 bp bl bm bk p2 b2 hpfx hntb =>
    intro hwfbin hwftip
    have hb2 : b2 ≠ 0 := by rw [WF] at hwftip; exact hwftip
    have hbl0 : 0 < bl := by rw [WF] at hwfbin; exact hwfbin.1
    have hpfxeq : prefixAbove (someKey (.tip p2 b2)) bl = bp := by simpa using hpfx
    have halign : AlignedAt bl (chunk (someKey (.tip p2 b2)) bl) bp (.tip p2 b2) :=
      hpfxeq ▸ aligned_tip p2 b2 hb2 bl hbl0
    have htbf : testBit bm (chunk (someKey (.tip p2 b2)) bl) = false := by simpa using hntb
    rw [unionU, if_pos hpfx, if_neg hntb,
        contains_splice j (.tip p2 b2) bp bl bm bk (chunk (someKey (.tip p2 b2)) bl)
          (chunk_lt _ _) hwfbin halign htbf]
    exact Bool.or_comm _ _
  | case12 bp bl bm bk p2 b2 hnpfx =>
    intro hwfbin hwftip
    have hb2 : b2 ≠ 0 := by rw [WF] at hwftip; exact hwftip
    have hbl0 : 0 < bl := by rw [WF] at hwfbin; exact hwfbin.1
    have hmne : bm ≠ 0 := by
      rw [WF] at hwfbin; obtain ⟨_, _, hpc, _, _, _⟩ := hwfbin
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hskbin : prefixAbove (someKey (.bin bp bl bm bk)) bl = bp :=
      someKey_bin_prefixAbove bp bl bm bk hmne
    have hpfxne : prefixAbove (someKey (.tip p2 b2)) bl ≠ bp := by
      intro h; exact hnpfx (by rw [h]; exact beq_self_eq_true bp)
    have hdiv : someKey (.bin bp bl bm bk) >>> (5 * (bl + 1))
        ≠ someKey (.tip p2 b2) >>> (5 * (bl + 1)) := by
      show prefixAbove (someKey (.bin bp bl bm bk)) bl ≠ prefixAbove (someKey (.tip p2 b2)) bl
      rw [hskbin]; exact fun h => hpfxne h.symm
    have hkne : someKey (.bin bp bl bm bk) ≠ someKey (.tip p2 b2) := fun h => hdiv (by rw [h])
    have hbl_lt : bl < branchLevel (someKey (.bin bp bl bm bk)) (someKey (.tip p2 b2)) :=
      lt_branchLevel _ _ bl hdiv
    rw [unionU, if_neg hnpfx,
        contains_join_eq j (someKey (.bin bp bl bm bk)) (someKey (.tip p2 b2)) (.bin bp bl bm bk)
          (.tip p2 b2) hkne ?ha ?hb]
    case ha => exact aligned_bin bp bl bm bk hwfbin _ hbl_lt
    case hb =>
      rw [prefixAbove_branchLevel_eq (someKey (.bin bp bl bm bk)) (someKey (.tip p2 b2))]
      exact aligned_tip p2 b2 hb2 _ (Nat.lt_trans hbl0 hbl_lt)
  | case13 p1 l1 m1 k1 p2 l2 m2 k2 heq IH =>
    intro hwf1 hwf2
    obtain ⟨hl, hp⟩ : l1 = l2 ∧ p1 = p2 := by
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at heq; exact heq
    subst hl; subst hp
    have hkw1 : KidsWF m1 k1 := by rw [WF] at hwf1; exact ⟨hwf1.2.1, hwf1.2.2.2.1, hwf1.2.2.2.2.1⟩
    have hkw2 : KidsWF m2 k2 := by rw [WF] at hwf2; exact ⟨hwf2.2.1, hwf2.2.2.2.1, hwf2.2.2.2.2.1⟩
    have hmc := IH hkw1 hkw2 (fun c _ h => h)
    rw [unionU, if_pos heq, contains_bin, contains_bin, contains_bin]
    by_cases hM : testBit (m1 ||| m2) (chunk j l1) = true
    · rw [hM, Bool.true_and, childAt_mergeKids m1 k1 m2 k2 (chunk j l1) (chunk_lt j l1) hM,
          hmc (chunk j l1) (chunk_lt j l1) hM]
    · simp only [Bool.not_eq_true] at hM
      have hor : (testBit m1 (chunk j l1) || testBit m2 (chunk j l1)) = false := by
        rw [← testBit_or]; exact hM
      rw [Bool.or_eq_false_iff] at hor
      rw [hM, hor.1, hor.2]
      simp only [Bool.false_and, Bool.or_self]
  | case14 p1 l1 m1 k1 p2 l2 m2 k2 hne hleq =>
    intro hwf1 hwf2
    have hl : l1 = l2 := by simpa using hleq
    subst hl
    have hpne : p1 ≠ p2 := by
      intro h; apply hne; rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]; exact ⟨rfl, h⟩
    have hm1ne : m1 ≠ 0 := by
      rw [WF] at hwf1; obtain ⟨_, _, hpc, _, _, _⟩ := hwf1
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hm2ne : m2 ≠ 0 := by
      rw [WF] at hwf2; obtain ⟨_, _, hpc, _, _, _⟩ := hwf2
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hsk1 : prefixAbove (someKey (.bin p1 l1 m1 k1)) l1 = p1 :=
      someKey_bin_prefixAbove p1 l1 m1 k1 hm1ne
    have hsk2 : prefixAbove (someKey (.bin p2 l1 m2 k2)) l1 = p2 :=
      someKey_bin_prefixAbove p2 l1 m2 k2 hm2ne
    have hdiv : someKey (.bin p1 l1 m1 k1) >>> (5 * (l1 + 1))
        ≠ someKey (.bin p2 l1 m2 k2) >>> (5 * (l1 + 1)) := by
      show prefixAbove (someKey (.bin p1 l1 m1 k1)) l1 ≠ prefixAbove (someKey (.bin p2 l1 m2 k2)) l1
      rw [hsk1, hsk2]; exact hpne
    have hkne : someKey (.bin p1 l1 m1 k1) ≠ someKey (.bin p2 l1 m2 k2) := fun h => hdiv (by rw [h])
    have hbl_lt : l1 < branchLevel (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l1 m2 k2)) :=
      lt_branchLevel _ _ l1 hdiv
    rw [unionU, if_neg hne, if_pos hleq,
        contains_join_eq j (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l1 m2 k2))
          (.bin p1 l1 m1 k1) (.bin p2 l1 m2 k2) hkne ?ha ?hb]
    case ha => exact aligned_bin p1 l1 m1 k1 hwf1 _ hbl_lt
    case hb =>
      rw [prefixAbove_branchLevel_eq (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l1 m2 k2))]
      exact aligned_bin p2 l1 m2 k2 hwf2 _ hbl_lt
  | case15 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hlt hpfx htb h IH =>
    intro hwf1 hwf2
    have hwfchild : WF (k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h) := by
      rw [WF] at hwf1; exact hwf1.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 = p1 := by simpa using hpfx
    have halign : AlignedAt l1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) p1 (.bin p2 l2 m2 k2) :=
      hpfxeq ▸ aligned_bin p2 l2 m2 k2 hwf2 l1 hlt
    rw [unionU, if_neg hne, if_neg hlne, if_pos hlt, if_pos hpfx, if_pos htb, dif_pos h,
        contains_descend j (.bin p2 l2 m2 k2) p1 l1 m1 k1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)
          (chunk_lt _ _) hwf1 halign htb h (IH hwfchild hwf2)]
    exact Bool.or_comm _ _
  | case16 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hlt hpfx htb hnh =>
    intro hwf1 _
    have hsize : k1.size = popCount m1 := by rw [WF] at hwf1; exact hwf1.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt m1 _ htb) hnh
  | case17 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hlt hpfx hntb =>
    intro hwf1 hwf2
    have hpfxeq : prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 = p1 := by simpa using hpfx
    have halign : AlignedAt l1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) p1 (.bin p2 l2 m2 k2) :=
      hpfxeq ▸ aligned_bin p2 l2 m2 k2 hwf2 l1 hlt
    have htbf : testBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) = false := by simpa using hntb
    rw [unionU, if_neg hne, if_neg hlne, if_pos hlt, if_pos hpfx, if_neg hntb,
        contains_splice j (.bin p2 l2 m2 k2) p1 l1 m1 k1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)
          (chunk_lt _ _) hwf1 halign htbf]
    exact Bool.or_comm _ _
  | case18 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hlt hnpfx =>
    intro hwf1 hwf2
    have hm1ne : m1 ≠ 0 := by
      rw [WF] at hwf1; obtain ⟨_, _, hpc, _, _, _⟩ := hwf1
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hsk1 : prefixAbove (someKey (.bin p1 l1 m1 k1)) l1 = p1 :=
      someKey_bin_prefixAbove p1 l1 m1 k1 hm1ne
    have hpfxne : prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 ≠ p1 := by
      intro h; exact hnpfx (by rw [h]; exact beq_self_eq_true p1)
    have hdiv : someKey (.bin p1 l1 m1 k1) >>> (5 * (l1 + 1))
        ≠ someKey (.bin p2 l2 m2 k2) >>> (5 * (l1 + 1)) := by
      show prefixAbove (someKey (.bin p1 l1 m1 k1)) l1 ≠ prefixAbove (someKey (.bin p2 l2 m2 k2)) l1
      rw [hsk1]; exact fun h => hpfxne h.symm
    have hkne : someKey (.bin p1 l1 m1 k1) ≠ someKey (.bin p2 l2 m2 k2) := fun h => hdiv (by rw [h])
    have hbl_lt : l1 < branchLevel (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l2 m2 k2)) :=
      lt_branchLevel _ _ l1 hdiv
    rw [unionU, if_neg hne, if_neg hlne, if_pos hlt, if_neg hnpfx,
        contains_join_eq j (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l2 m2 k2))
          (.bin p1 l1 m1 k1) (.bin p2 l2 m2 k2) hkne ?ha ?hb]
    case ha => exact aligned_bin p1 l1 m1 k1 hwf1 _ hbl_lt
    case hb =>
      rw [prefixAbove_branchLevel_eq (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l2 m2 k2))]
      exact aligned_bin p2 l2 m2 k2 hwf2 _ (Nat.lt_trans hlt hbl_lt)
  | case19 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hnlt hpfx htb h IH =>
    intro hwf1 hwf2
    have hl12 : l1 < l2 := by
      have h1 : l1 ≠ l2 := by simpa using hlne
      omega
    have hwfchild : WF (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h) := by
      rw [WF] at hwf2; exact hwf2.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 = p2 := by simpa using hpfx
    have halign : AlignedAt l2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) p2 (.bin p1 l1 m1 k1) :=
      hpfxeq ▸ aligned_bin p1 l1 m1 k1 hwf1 l2 hl12
    rw [unionU, if_neg hne, if_neg hlne, if_neg hnlt, if_pos hpfx, if_pos htb, dif_pos h]
    exact contains_descend j (.bin p1 l1 m1 k1) p2 l2 m2 k2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)
      (chunk_lt _ _) hwf2 halign htb h (IH hwfchild hwf1)
  | case20 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hnlt hpfx htb hnh =>
    intro _ hwf2
    have hsize : k2.size = popCount m2 := by rw [WF] at hwf2; exact hwf2.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt m2 _ htb) hnh
  | case21 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hnlt hpfx hntb =>
    intro hwf1 hwf2
    have hl12 : l1 < l2 := by
      have h1 : l1 ≠ l2 := by simpa using hlne
      omega
    have hpfxeq : prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 = p2 := by simpa using hpfx
    have halign : AlignedAt l2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) p2 (.bin p1 l1 m1 k1) :=
      hpfxeq ▸ aligned_bin p1 l1 m1 k1 hwf1 l2 hl12
    have htbf : testBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) = false := by simpa using hntb
    rw [unionU, if_neg hne, if_neg hlne, if_neg hnlt, if_pos hpfx, if_neg hntb]
    exact contains_splice j (.bin p1 l1 m1 k1) p2 l2 m2 k2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)
      (chunk_lt _ _) hwf2 halign htbf
  | case22 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hnlt hnpfx =>
    intro hwf1 hwf2
    have hl12 : l1 < l2 := by
      have h1 : l1 ≠ l2 := by simpa using hlne
      omega
    have hm2ne : m2 ≠ 0 := by
      rw [WF] at hwf2; obtain ⟨_, _, hpc, _, _, _⟩ := hwf2
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hsk2 : prefixAbove (someKey (.bin p2 l2 m2 k2)) l2 = p2 :=
      someKey_bin_prefixAbove p2 l2 m2 k2 hm2ne
    have hpfxne : prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 ≠ p2 := by
      intro h; exact hnpfx (by rw [h]; exact beq_self_eq_true p2)
    have hdiv : someKey (.bin p2 l2 m2 k2) >>> (5 * (l2 + 1))
        ≠ someKey (.bin p1 l1 m1 k1) >>> (5 * (l2 + 1)) := by
      show prefixAbove (someKey (.bin p2 l2 m2 k2)) l2 ≠ prefixAbove (someKey (.bin p1 l1 m1 k1)) l2
      rw [hsk2]; exact fun h => hpfxne h.symm
    have hkne : someKey (.bin p2 l2 m2 k2) ≠ someKey (.bin p1 l1 m1 k1) := fun h => hdiv (by rw [h])
    have hbl_lt : l2 < branchLevel (someKey (.bin p2 l2 m2 k2)) (someKey (.bin p1 l1 m1 k1)) :=
      lt_branchLevel _ _ l2 hdiv
    rw [unionU, if_neg hne, if_neg hlne, if_neg hnlt, if_neg hnpfx,
        contains_join_eq j (someKey (.bin p2 l2 m2 k2)) (someKey (.bin p1 l1 m1 k1))
          (.bin p2 l2 m2 k2) (.bin p1 l1 m1 k1) hkne ?ha ?hb]
    · exact Bool.or_comm _ _
    case ha => exact aligned_bin p2 l2 m2 k2 hwf2 _ hbl_lt
    case hb =>
      rw [prefixAbove_branchLevel_eq (someKey (.bin p2 l2 m2 k2)) (someKey (.bin p1 l1 m1 k1))]
      exact aligned_bin p1 l1 m1 k1 hwf1 _ (Nat.lt_trans hl12 hbl_lt)
  | case23 m1 k1 m2 k2 rem acc hrem =>
    rename_i _ _ _ _ _ htb
    have hr0 : rem = 0 := by simpa using hrem
    rw [hr0, testBit_zero] at htb; exact absurd htb (by decide)
  | case24 m1 k1 m2 k2 rem acc hrem IHchild IHrec =>
    rename_i hkw1 hkw2 hsub c hc htb
    have hrem0 : rem ≠ 0 := by intro h; exact hrem (by rw [h]; rfl)
    by_cases hclo : c = lowestSetIdx rem
    · subst hclo
      exact IHchild hkw1 hkw2 (lowestSetIdx_lt rem hrem0)
        (by rw [← testBit_or]
            exact hsub (lowestSetIdx rem) (lowestSetIdx_lt rem hrem0) (testBit_lowestSetIdx rem hrem0))
    · have htb' : testBit (clearLowest rem) c = true := by
        rw [testBit_clearLowest_of_ne rem c hc hclo]; exact htb
      exact IHrec hkw1 hkw2
        (fun c' hc' h' => hsub c' hc' (testBit_of_clearLowest rem c' h')) c hc htb'
  | case25 m1 k1 m2 k2 i ht1 ht2 h1 h2 IH =>
    rename_i hkw1 hkw2 _ _
    have hwf1 : WF (k1[arrayIndex m1 i]'h1) := hkw1.2.1 _ (Array.getElem_mem h1)
    have hwf2 : WF (k2[arrayIndex m2 i]'h2) := hkw2.2.1 _ (Array.getElem_mem h2)
    have hc1 : childAt m1 k1 i = k1[arrayIndex m1 i]'h1 := by
      unfold childAt; rw [Array.getElem?_eq_getElem h1, Option.getD_some]
    have hc2 : childAt m2 k2 i = k2[arrayIndex m2 i]'h2 := by
      unfold childAt; rw [Array.getElem?_eq_getElem h2, Option.getD_some]
    rw [mergeChild, if_pos ht1, if_pos ht2, dif_pos h1, dif_pos h2, IH hwf1 hwf2, ht1, ht2,
        Bool.true_and, Bool.true_and, hc1, hc2]
  | case26 m1 k1 m2 k2 i ht1 ht2 h1 hnh2 =>
    rename_i _ hkw2 _ _
    exact absurd (by rw [hkw2.1]; exact arrayIndex_lt m2 i ht2) hnh2
  | case27 m1 k1 m2 k2 i ht1 ht2 hnh1 =>
    rename_i hkw1 _ _ _
    exact absurd (by rw [hkw1.1]; exact arrayIndex_lt m1 i ht1) hnh1
  | case28 m1 k1 m2 k2 i ht1 hnt2 h1 =>
    have hc1 : childAt m1 k1 i = k1[arrayIndex m1 i]'h1 := by
      unfold childAt; rw [Array.getElem?_eq_getElem h1, Option.getD_some]
    have hf2 : testBit m2 i = false := by simpa using hnt2
    rw [mergeChild, if_pos ht1, if_neg hnt2, dif_pos h1, ht1, hf2,
        Bool.true_and, Bool.false_and, Bool.or_false, hc1]
  | case29 m1 k1 m2 k2 i ht1 hnt2 hnh1 =>
    rename_i hkw1 _ _ _
    exact absurd (by rw [hkw1.1]; exact arrayIndex_lt m1 i ht1) hnh1
  | case30 m1 k1 m2 k2 i hnt1 h2 =>
    rename_i _ _ _ hor
    have hc2 : childAt m2 k2 i = k2[arrayIndex m2 i]'h2 := by
      unfold childAt; rw [Array.getElem?_eq_getElem h2, Option.getD_some]
    have hf1 : testBit m1 i = false := by simpa using hnt1
    have ht2 : testBit m2 i = true := by
      rw [hf1, Bool.false_or] at hor; exact hor
    rw [mergeChild, if_neg hnt1, dif_pos h2, hf1, ht2, Bool.false_and,
        Bool.true_and, Bool.false_or, hc2]
  | case31 m1 k1 m2 k2 i hnt1 hnh2 =>
    rename_i _ hkw2 _ hor
    have hf1 : testBit m1 i = false := by simpa using hnt1
    have ht2 : testBit m2 i = true := by
      rw [hf1, Bool.false_or] at hor; exact hor
    exact absurd (by rw [hkw2.1]; exact arrayIndex_lt m2 i ht2) hnh2

/-- `get?_join` for the set: membership after `union` is membership in either operand — the seam the
lattice/order suite (commutativity, associativity, idempotence, LUB, distributivity) routes through.
Stated on `union`; the work is in `contains_unionU`. -/
theorem contains_union (j : Nat) (a b : PTree) (hwa : WF a) (hwb : WF b) :
    contains j (union a b) = (contains j a || contains j b) := by
  rw [union]; exact contains_unionU j a b hwa hwb

/-- Membership in a merged slot is membership in either operand's slot child — the per-slot form of
`contains_union`, now standalone (the `unionU` recursion it rests on is closed). Drives the routing
clause of `WF_union`: a merged child's keys come from one operand's child, so they stay aligned. -/
theorem contains_mergeChild (j : Nat) (m1 : UInt32) (k1 : Array PTree) (m2 : UInt32)
    (k2 : Array PTree) (i : UInt32) (hkw1 : KidsWF m1 k1) (hkw2 : KidsWF m2 k2)
    (hpre : (testBit m1 i || testBit m2 i) = true) :
    contains j (mergeChild m1 k1 m2 k2 i)
      = ((testBit m1 i && contains j (childAt m1 k1 i))
          || (testBit m2 i && contains j (childAt m2 k2 i))) := by
  have hc1 : ∀ (h : arrayIndex m1 i < k1.size), childAt m1 k1 i = k1[arrayIndex m1 i]'h := fun h => by
    unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
  have hc2 : ∀ (h : arrayIndex m2 i < k2.size), childAt m2 k2 i = k2[arrayIndex m2 i]'h := fun h => by
    unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
  rw [mergeChild]
  by_cases ht1 : testBit m1 i = true
  · have h1 : arrayIndex m1 i < k1.size := by rw [hkw1.1]; exact arrayIndex_lt m1 i ht1
    by_cases ht2 : testBit m2 i = true
    · have h2 : arrayIndex m2 i < k2.size := by rw [hkw2.1]; exact arrayIndex_lt m2 i ht2
      rw [if_pos ht1, if_pos ht2, dif_pos h1, dif_pos h2,
          contains_unionU j _ _ (hkw1.2.1 _ (Array.getElem_mem h1)) (hkw2.2.1 _ (Array.getElem_mem h2)),
          ht1, ht2, Bool.true_and, Bool.true_and, hc1 h1, hc2 h2]
    · have hf2 : testBit m2 i = false := by simpa using ht2
      rw [if_pos ht1, if_neg ht2, dif_pos h1, ht1, hf2, Bool.true_and, Bool.false_and,
          Bool.or_false, hc1 h1]
  · have hf1 : testBit m1 i = false := by simpa using ht1
    have ht2 : testBit m2 i = true := by rw [hf1, Bool.false_or] at hpre; exact hpre
    have h2 : arrayIndex m2 i < k2.size := by rw [hkw2.1]; exact arrayIndex_lt m2 i ht2
    rw [if_neg ht1, dif_pos h2, hf1, ht2, Bool.false_and, Bool.true_and, Bool.false_or, hc2 h2]

/-- A *present* slot's `mergeChild` is never `nil`: it is a real (non-`nil`) child of an operand or
their `unionU` (which inherits a non-`nil` left child). Discharges `WF_unionU`'s non-`nil` clause. -/
theorem mergeChild_ne_nil (m1 : UInt32) (k1 : Array PTree) (m2 : UInt32) (k2 : Array PTree)
    (i : UInt32) (hkw1 : KidsWF m1 k1) (hkw2 : KidsWF m2 k2)
    (hpre : (testBit m1 i || testBit m2 i) = true) :
    mergeChild m1 k1 m2 k2 i ≠ .nil := by
  rw [mergeChild]
  by_cases ht1 : testBit m1 i = true
  · have h1 : arrayIndex m1 i < k1.size := by rw [hkw1.1]; exact arrayIndex_lt m1 i ht1
    by_cases ht2 : testBit m2 i = true
    · have h2 : arrayIndex m2 i < k2.size := by rw [hkw2.1]; exact arrayIndex_lt m2 i ht2
      rw [if_pos ht1, if_pos ht2, dif_pos h1, dif_pos h2]
      exact unionU_ne_nil_of_left _ _ (hkw1.2.2 _ (Array.getElem_mem h1))
    · rw [if_pos ht1, if_neg ht2, dif_pos h1]
      exact hkw1.2.2 _ (Array.getElem_mem h1)
  · have hf1 : testBit m1 i = false := by simpa using ht1
    have ht2 : testBit m2 i = true := by rw [hf1, Bool.false_or] at hpre; exact hpre
    have h2 : arrayIndex m2 i < k2.size := by rw [hkw2.1]; exact arrayIndex_lt m2 i ht2
    rw [if_neg ht1, dif_pos h2]
    exact hkw2.2.2 _ (Array.getElem_mem h2)

/-- `WF` descend case: overwriting a present slot of a well-formed `bin` with `unionU child op`
keeps it canonical. Size/minimality are preserved; the new child is well-formed by the recursive
`WF`, and its keys stay aligned because (via `contains_union`) they are the old child's keys plus
`op`'s, both routed to slot `c`. -/
private theorem WF_descend (op : PTree) (bp bl : Nat) (bm : UInt32) (bk : Array PTree)
    (c : UInt32) (hc : c < 32) (hbin : WF (.bin bp bl bm bk)) (halign : AlignedAt bl c bp op)
    (hwop : WF op) (htb : testBit bm c = true) (hidx : arrayIndex bm c < bk.size)
    (hwu : WF (unionU (bk[arrayIndex bm c]'hidx) op)) :
    WF (.bin bp bl bm (bk.setIfInBounds (arrayIndex bm c) (unionU (bk[arrayIndex bm c]'hidx) op))) := by
  rw [WF] at hbin ⊢
  obtain ⟨hlvl, hsize, hpc, hkidswf, hnonnil, hrout⟩ := hbin
  have hcAc : childAt bm bk c = bk[arrayIndex bm c]'hidx := by
    unfold childAt; rw [Array.getElem?_eq_getElem hidx, Option.getD_some]
  refine ⟨hlvl, ?_, hpc, ?_, ?_, ?_⟩
  · rw [Array.size_setIfInBounds]; exact hsize
  · intro c' hc'
    rcases Array.mem_or_eq_of_mem_setIfInBounds hc' with hmem | heq
    · exact hkidswf c' hmem
    · rw [heq]; exact hwu
  · intro c' hc'
    rcases Array.mem_or_eq_of_mem_setIfInBounds hc' with hmem | heq
    · exact hnonnil c' hmem
    · rw [heq]; exact unionU_ne_nil_of_left _ op (hnonnil _ (Array.getElem_mem hidx))
  · intro c'' hc''lt htc''
    by_cases hc''c : c'' = c
    · rw [hc''c, childAt_setIfInBounds bm c c bk _ hc hc htb htb hsize, if_pos rfl]
      intro k hk
      rw [contains_unionU k _ op (hkidswf _ (Array.getElem_mem hidx)) hwop, Bool.or_eq_true] at hk
      rcases hk with hkc | hko
      · have := hrout c hc htb; rw [hcAc] at this; exact this k hkc
      · exact halign k hko
    · rw [childAt_setIfInBounds bm c c'' bk _ hc hc''lt htb htc'' hsize, if_neg hc''c]
      exact hrout c'' hc''lt htc''

/-- `WF` splice case: inserting an aligned, well-formed operand `op` whole at an absent slot keeps
the `bin` canonical (one more child, mask gains its bit, the new slot's keys align by `op`). -/
private theorem WF_splice (op : PTree) (bp bl : Nat) (bm : UInt32) (bk : Array PTree)
    (c : UInt32) (hc : c < 32) (hbin : WF (.bin bp bl bm bk)) (halign : AlignedAt bl c bp op)
    (hwop : WF op) (hopne : op ≠ .nil) (htb : testBit bm c = false) :
    WF (.bin bp bl (setBit bm c) (bk.insertIdx! (arrayIndex bm c) op)) := by
  rw [WF] at hbin ⊢
  obtain ⟨hlvl, hsize, hpc, hkidswf, hnonnil, hrout⟩ := hbin
  have hpcnew : popCount (setBit bm c) = popCount bm + 1 := popCount_setBit bm c htb
  have hle : arrayIndex bm c ≤ bk.size := by rw [hsize]; exact arrayIndex_le _ _
  have hidx : bk.insertIdx! (arrayIndex bm c) op = bk.insertIdx (arrayIndex bm c) op hle := dif_pos hle
  refine ⟨hlvl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hidx, Array.size_insertIdx, hsize, hpcnew]
  · rw [hpcnew]; omega
  · intro c' hc'
    rw [hidx] at hc'
    rcases Array.mem_insertIdx.mp hc' with heq | hmem
    · rw [heq]; exact hwop
    · exact hkidswf c' hmem
  · intro c' hc'
    rw [hidx] at hc'
    rcases Array.mem_insertIdx.mp hc' with heq | hmem
    · rw [heq]; exact hopne
    · exact hnonnil c' hmem
  · intro c'' hc''lt htc''
    by_cases hc''c : c'' = c
    · rw [hc''c, childAt_insertIdx_self bm c bk op hsize]
      exact halign
    · have htcm : testBit bm c'' = true := by
        rw [testBit_setBit bm c c'' hc hc''lt, beq_eq_false_iff_ne.mpr (Ne.symm hc''c),
            Bool.or_false] at htc''
        exact htc''
      rw [childAt_insertIdx_of_ne bm c c'' bk op hc hc''lt hc''c htb htcm hsize]
      exact hrout c'' hc''lt htcm

/-- `union` preserves the canonical shape. Mirrors `contains_unionU` over the same mutual induction:
the merge quadrants reuse `WF_descend`/`WF_splice`/`WF_join`; the aligned-`bin` case rebuilds a
2-or-more-child node whose size is `size_mergeKids`, whose children are each well-formed
(`motive2`/`motive3`), and whose routing holds because each merged child's keys come from an
operand's aligned child (`contains_mergeChild`). -/
theorem WF_unionU : ∀ (a b : PTree), WF a → WF b → WF (unionU a b) := by
  intro a b
  induction a, b using unionU.induct
    (motive2 := fun m1 k1 m2 k2 rem acc =>
      KidsWF m1 k1 → KidsWF m2 k2 → (∀ c ∈ acc, WF c) →
        ∀ c ∈ mergeKids m1 k1 m2 k2 rem acc, WF c)
    (motive3 := fun m1 k1 m2 k2 i =>
      KidsWF m1 k1 → KidsWF m2 k2 → WF (mergeChild m1 k1 m2 k2 i)) with
  | case1 t => intro _ hwft; rw [unionU]; exact hwft
  | case2 s hs =>
    intro hwfs _
    rw [unionU]
    · exact hwfs
    · exact hs
  | case3 p1 b1 p2 b2 heq =>
    intro hwf1 _
    have hb1 : b1 ≠ 0 := by rw [WF] at hwf1; exact hwf1
    rw [unionU, if_pos heq, WF]
    exact or_ne_zero_left b1 b2 hb1
  | case4 p1 b1 p2 b2 hne =>
    intro hwf1 hwf2
    have hb1 : b1 ≠ 0 := by rw [WF] at hwf1; exact hwf1
    have hb2 : b2 ≠ 0 := by rw [WF] at hwf2; exact hwf2
    have hpne : p1 ≠ p2 := fun h => hne (by rw [h]; exact beq_self_eq_true p2)
    have hsk1 : someKey (.tip p1 b1) >>> 5 = p1 := someKey_tip_shiftRight5 p1 b1 hb1
    have hsk2 : someKey (.tip p2 b2) >>> 5 = p2 := someKey_tip_shiftRight5 p2 b2 hb2
    have hkne : someKey (.tip p1 b1) ≠ someKey (.tip p2 b2) := by
      intro h; apply hpne; rw [← hsk1, ← hsk2, h]
    have hkne5 : someKey (.tip p1 b1) >>> 5 ≠ someKey (.tip p2 b2) >>> 5 := by
      rw [hsk1, hsk2]; exact hpne
    have hl0 : 0 < branchLevel (someKey (.tip p1 b1)) (someKey (.tip p2 b2)) :=
      branchLevel_pos _ _ hkne5
    rw [unionU, if_neg hne, join]
    refine WF_join _ _ _ _ (.tip p1 b1) (.tip p2 b2) hl0 (chunk_lt _ _) (chunk_lt _ _)
      (chunk_branchLevel_ne _ _ hkne) ?ha ?hb hwf1 hwf2 (by simp) (by simp)
    case ha => exact aligned_tip p1 b1 hb1 _ hl0
    case hb =>
      rw [prefixAbove_branchLevel_eq (someKey (.tip p1 b1)) (someKey (.tip p2 b2))]
      exact aligned_tip p2 b2 hb2 _ hl0
  | case5 p1 b1 bp bl bm bk hpfx htb h IH =>
    intro hwf1 hwf2
    have hb1 : b1 ≠ 0 := by rw [WF] at hwf1; exact hwf1
    have hbl0 : 0 < bl := by rw [WF] at hwf2; exact hwf2.1
    have hwfchild : WF (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h) := by
      rw [WF] at hwf2; exact hwf2.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.tip p1 b1)) bl = bp := by simpa using hpfx
    have halign : AlignedAt bl (chunk (someKey (.tip p1 b1)) bl) bp (.tip p1 b1) :=
      hpfxeq ▸ aligned_tip p1 b1 hb1 bl hbl0
    rw [unionU, if_pos hpfx, if_pos htb, dif_pos h]
    exact WF_descend (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl) (chunk_lt _ _)
      hwf2 halign hwf1 htb h (IH hwfchild hwf1)
  | case6 p1 b1 bp bl bm bk hpfx htb hnh =>
    intro _ hwf2
    have hsize : bk.size = popCount bm := by rw [WF] at hwf2; exact hwf2.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt bm _ htb) hnh
  | case7 p1 b1 bp bl bm bk hpfx hntb =>
    intro hwf1 hwf2
    have hb1 : b1 ≠ 0 := by rw [WF] at hwf1; exact hwf1
    have hbl0 : 0 < bl := by rw [WF] at hwf2; exact hwf2.1
    have hpfxeq : prefixAbove (someKey (.tip p1 b1)) bl = bp := by simpa using hpfx
    have halign : AlignedAt bl (chunk (someKey (.tip p1 b1)) bl) bp (.tip p1 b1) :=
      hpfxeq ▸ aligned_tip p1 b1 hb1 bl hbl0
    have htbf : testBit bm (chunk (someKey (.tip p1 b1)) bl) = false := by simpa using hntb
    rw [unionU, if_pos hpfx, if_neg hntb]
    exact WF_splice (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl)
      (chunk_lt _ _) hwf2 halign hwf1 (by simp) htbf
  | case8 p1 b1 bp bl bm bk hnpfx =>
    intro hwf1 hwf2
    have hb1 : b1 ≠ 0 := by rw [WF] at hwf1; exact hwf1
    have hbl0 : 0 < bl := by rw [WF] at hwf2; exact hwf2.1
    have hmne : bm ≠ 0 := by
      rw [WF] at hwf2; obtain ⟨_, _, hpc, _, _, _⟩ := hwf2
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hskbin : prefixAbove (someKey (.bin bp bl bm bk)) bl = bp :=
      someKey_bin_prefixAbove bp bl bm bk hmne
    have hpfxne : prefixAbove (someKey (.tip p1 b1)) bl ≠ bp := by
      intro h; exact hnpfx (by rw [h]; exact beq_self_eq_true bp)
    have hdiv : someKey (.bin bp bl bm bk) >>> (5 * (bl + 1))
        ≠ someKey (.tip p1 b1) >>> (5 * (bl + 1)) := by
      show prefixAbove (someKey (.bin bp bl bm bk)) bl ≠ prefixAbove (someKey (.tip p1 b1)) bl
      rw [hskbin]; exact fun h => hpfxne h.symm
    have hkne : someKey (.bin bp bl bm bk) ≠ someKey (.tip p1 b1) := fun h => hdiv (by rw [h])
    have hbl_lt : bl < branchLevel (someKey (.bin bp bl bm bk)) (someKey (.tip p1 b1)) :=
      lt_branchLevel _ _ bl hdiv
    have hl0 : 0 < branchLevel (someKey (.bin bp bl bm bk)) (someKey (.tip p1 b1)) :=
      Nat.lt_trans hbl0 hbl_lt
    rw [unionU, if_neg hnpfx, join]
    refine WF_join _ _ _ _ (.bin bp bl bm bk) (.tip p1 b1) hl0 (chunk_lt _ _) (chunk_lt _ _)
      (chunk_branchLevel_ne _ _ hkne) ?ha ?hb hwf2 hwf1 (by simp) (by simp)
    case ha => exact aligned_bin bp bl bm bk hwf2 _ hbl_lt
    case hb =>
      rw [prefixAbove_branchLevel_eq (someKey (.bin bp bl bm bk)) (someKey (.tip p1 b1))]
      exact aligned_tip p1 b1 hb1 _ hl0
  | case9 bp bl bm bk p2 b2 hpfx htb h IH =>
    intro hwfbin hwftip
    have hb2 : b2 ≠ 0 := by rw [WF] at hwftip; exact hwftip
    have hbl0 : 0 < bl := by rw [WF] at hwfbin; exact hwfbin.1
    have hwfchild : WF (bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h) := by
      rw [WF] at hwfbin; exact hwfbin.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.tip p2 b2)) bl = bp := by simpa using hpfx
    have halign : AlignedAt bl (chunk (someKey (.tip p2 b2)) bl) bp (.tip p2 b2) :=
      hpfxeq ▸ aligned_tip p2 b2 hb2 bl hbl0
    rw [unionU, if_pos hpfx, if_pos htb, dif_pos h]
    exact WF_descend (.tip p2 b2) bp bl bm bk (chunk (someKey (.tip p2 b2)) bl) (chunk_lt _ _)
      hwfbin halign hwftip htb h (IH hwfchild hwftip)
  | case10 bp bl bm bk p2 b2 hpfx htb hnh =>
    intro hwfbin _
    have hsize : bk.size = popCount bm := by rw [WF] at hwfbin; exact hwfbin.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt bm _ htb) hnh
  | case11 bp bl bm bk p2 b2 hpfx hntb =>
    intro hwfbin hwftip
    have hb2 : b2 ≠ 0 := by rw [WF] at hwftip; exact hwftip
    have hbl0 : 0 < bl := by rw [WF] at hwfbin; exact hwfbin.1
    have hpfxeq : prefixAbove (someKey (.tip p2 b2)) bl = bp := by simpa using hpfx
    have halign : AlignedAt bl (chunk (someKey (.tip p2 b2)) bl) bp (.tip p2 b2) :=
      hpfxeq ▸ aligned_tip p2 b2 hb2 bl hbl0
    have htbf : testBit bm (chunk (someKey (.tip p2 b2)) bl) = false := by simpa using hntb
    rw [unionU, if_pos hpfx, if_neg hntb]
    exact WF_splice (.tip p2 b2) bp bl bm bk (chunk (someKey (.tip p2 b2)) bl)
      (chunk_lt _ _) hwfbin halign hwftip (by simp) htbf
  | case12 bp bl bm bk p2 b2 hnpfx =>
    intro hwfbin hwftip
    have hb2 : b2 ≠ 0 := by rw [WF] at hwftip; exact hwftip
    have hbl0 : 0 < bl := by rw [WF] at hwfbin; exact hwfbin.1
    have hmne : bm ≠ 0 := by
      rw [WF] at hwfbin; obtain ⟨_, _, hpc, _, _, _⟩ := hwfbin
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hskbin : prefixAbove (someKey (.bin bp bl bm bk)) bl = bp :=
      someKey_bin_prefixAbove bp bl bm bk hmne
    have hpfxne : prefixAbove (someKey (.tip p2 b2)) bl ≠ bp := by
      intro h; exact hnpfx (by rw [h]; exact beq_self_eq_true bp)
    have hdiv : someKey (.bin bp bl bm bk) >>> (5 * (bl + 1))
        ≠ someKey (.tip p2 b2) >>> (5 * (bl + 1)) := by
      show prefixAbove (someKey (.bin bp bl bm bk)) bl ≠ prefixAbove (someKey (.tip p2 b2)) bl
      rw [hskbin]; exact fun h => hpfxne h.symm
    have hkne : someKey (.bin bp bl bm bk) ≠ someKey (.tip p2 b2) := fun h => hdiv (by rw [h])
    have hbl_lt : bl < branchLevel (someKey (.bin bp bl bm bk)) (someKey (.tip p2 b2)) :=
      lt_branchLevel _ _ bl hdiv
    have hl0 : 0 < branchLevel (someKey (.bin bp bl bm bk)) (someKey (.tip p2 b2)) :=
      Nat.lt_trans hbl0 hbl_lt
    rw [unionU, if_neg hnpfx, join]
    refine WF_join _ _ _ _ (.bin bp bl bm bk) (.tip p2 b2) hl0 (chunk_lt _ _) (chunk_lt _ _)
      (chunk_branchLevel_ne _ _ hkne) ?ha ?hb hwfbin hwftip (by simp) (by simp)
    case ha => exact aligned_bin bp bl bm bk hwfbin _ hbl_lt
    case hb =>
      rw [prefixAbove_branchLevel_eq (someKey (.bin bp bl bm bk)) (someKey (.tip p2 b2))]
      exact aligned_tip p2 b2 hb2 _ hl0
  | case13 p1 l1 m1 k1 p2 l2 m2 k2 heq IH =>
    intro hwf1 hwf2
    obtain ⟨hl, hp⟩ : l1 = l2 ∧ p1 = p2 := by
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at heq; exact heq
    subst hl; subst hp
    have hkw1 : KidsWF m1 k1 := by rw [WF] at hwf1; exact ⟨hwf1.2.1, hwf1.2.2.2.1, hwf1.2.2.2.2.1⟩
    have hkw2 : KidsWF m2 k2 := by rw [WF] at hwf2; exact ⟨hwf2.2.1, hwf2.2.2.2.1, hwf2.2.2.2.2.1⟩
    have hl0 : 0 < l1 := by rw [WF] at hwf1; exact hwf1.1
    have hpc1 : 2 ≤ popCount m1 := by rw [WF] at hwf1; exact hwf1.2.2.1
    have hrout1 : ∀ c, c < 32 → testBit m1 c = true → AlignedAt l1 c p1 (childAt m1 k1 c) := by
      rw [WF] at hwf1; exact hwf1.2.2.2.2.2
    have hrout2 : ∀ c, c < 32 → testBit m2 c = true → AlignedAt l1 c p1 (childAt m2 k2 c) := by
      rw [WF] at hwf2; exact hwf2.2.2.2.2.2
    rw [unionU, if_pos heq, WF]
    refine ⟨hl0, size_mergeKids m1 k1 m2 k2, Nat.le_trans hpc1 (popCount_or_left m1 m2),
      IH hkw1 hkw2 (by intro c hc; simp at hc), ?_, ?_⟩
    · intro x hx
      rcases mergeKids_mem m1 k1 m2 k2 (m1 ||| m2).toNat (m1 ||| m2) rfl #[] x hx with hin | hex
      · simp at hin
      · obtain ⟨c, htb, hxc⟩ := hex
        rw [hxc]
        exact mergeChild_ne_nil m1 k1 m2 k2 c hkw1 hkw2 (by rw [← testBit_or]; exact htb)
    · intro c hclt htc
      rw [childAt_mergeKids m1 k1 m2 k2 c hclt htc]
      intro k hk
      rw [contains_mergeChild k m1 k1 m2 k2 c hkw1 hkw2 (by rw [← testBit_or]; exact htc),
          Bool.or_eq_true] at hk
      rcases hk with h1 | h2
      · rw [Bool.and_eq_true] at h1; exact hrout1 c hclt h1.1 k h1.2
      · rw [Bool.and_eq_true] at h2; exact hrout2 c hclt h2.1 k h2.2
  | case14 p1 l1 m1 k1 p2 l2 m2 k2 hne hleq =>
    intro hwf1 hwf2
    have hl : l1 = l2 := by simpa using hleq
    subst hl
    have hpne : p1 ≠ p2 := by
      intro h; apply hne; rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]; exact ⟨rfl, h⟩
    have hl0 : 0 < l1 := by rw [WF] at hwf1; exact hwf1.1
    have hm1ne : m1 ≠ 0 := by
      rw [WF] at hwf1; obtain ⟨_, _, hpc, _, _, _⟩ := hwf1
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hm2ne : m2 ≠ 0 := by
      rw [WF] at hwf2; obtain ⟨_, _, hpc, _, _, _⟩ := hwf2
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hsk1 : prefixAbove (someKey (.bin p1 l1 m1 k1)) l1 = p1 :=
      someKey_bin_prefixAbove p1 l1 m1 k1 hm1ne
    have hsk2 : prefixAbove (someKey (.bin p2 l1 m2 k2)) l1 = p2 :=
      someKey_bin_prefixAbove p2 l1 m2 k2 hm2ne
    have hdiv : someKey (.bin p1 l1 m1 k1) >>> (5 * (l1 + 1))
        ≠ someKey (.bin p2 l1 m2 k2) >>> (5 * (l1 + 1)) := by
      show prefixAbove (someKey (.bin p1 l1 m1 k1)) l1 ≠ prefixAbove (someKey (.bin p2 l1 m2 k2)) l1
      rw [hsk1, hsk2]; exact hpne
    have hkne : someKey (.bin p1 l1 m1 k1) ≠ someKey (.bin p2 l1 m2 k2) := fun h => hdiv (by rw [h])
    have hbl_lt : l1 < branchLevel (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l1 m2 k2)) :=
      lt_branchLevel _ _ l1 hdiv
    have hl0' : 0 < branchLevel (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l1 m2 k2)) :=
      Nat.lt_trans hl0 hbl_lt
    rw [unionU, if_neg hne, if_pos hleq, join]
    refine WF_join _ _ _ _ (.bin p1 l1 m1 k1) (.bin p2 l1 m2 k2) hl0' (chunk_lt _ _) (chunk_lt _ _)
      (chunk_branchLevel_ne _ _ hkne) ?ha ?hb hwf1 hwf2 (by simp) (by simp)
    case ha => exact aligned_bin p1 l1 m1 k1 hwf1 _ hbl_lt
    case hb =>
      rw [prefixAbove_branchLevel_eq (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l1 m2 k2))]
      exact aligned_bin p2 l1 m2 k2 hwf2 _ hbl_lt
  | case15 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hlt hpfx htb h IH =>
    intro hwf1 hwf2
    have hwfchild : WF (k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h) := by
      rw [WF] at hwf1; exact hwf1.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 = p1 := by simpa using hpfx
    have halign : AlignedAt l1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) p1 (.bin p2 l2 m2 k2) :=
      hpfxeq ▸ aligned_bin p2 l2 m2 k2 hwf2 l1 hlt
    rw [unionU, if_neg hne, if_neg hlne, if_pos hlt, if_pos hpfx, if_pos htb, dif_pos h]
    exact WF_descend (.bin p2 l2 m2 k2) p1 l1 m1 k1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)
      (chunk_lt _ _) hwf1 halign hwf2 htb h (IH hwfchild hwf2)
  | case16 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hlt hpfx htb hnh =>
    intro hwf1 _
    have hsize : k1.size = popCount m1 := by rw [WF] at hwf1; exact hwf1.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt m1 _ htb) hnh
  | case17 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hlt hpfx hntb =>
    intro hwf1 hwf2
    have hpfxeq : prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 = p1 := by simpa using hpfx
    have halign : AlignedAt l1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) p1 (.bin p2 l2 m2 k2) :=
      hpfxeq ▸ aligned_bin p2 l2 m2 k2 hwf2 l1 hlt
    have htbf : testBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) = false := by simpa using hntb
    rw [unionU, if_neg hne, if_neg hlne, if_pos hlt, if_pos hpfx, if_neg hntb]
    exact WF_splice (.bin p2 l2 m2 k2) p1 l1 m1 k1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)
      (chunk_lt _ _) hwf1 halign hwf2 (by simp) htbf
  | case18 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hlt hnpfx =>
    intro hwf1 hwf2
    have hl0 : 0 < l1 := by rw [WF] at hwf1; exact hwf1.1
    have hm1ne : m1 ≠ 0 := by
      rw [WF] at hwf1; obtain ⟨_, _, hpc, _, _, _⟩ := hwf1
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hsk1 : prefixAbove (someKey (.bin p1 l1 m1 k1)) l1 = p1 :=
      someKey_bin_prefixAbove p1 l1 m1 k1 hm1ne
    have hpfxne : prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 ≠ p1 := by
      intro h; exact hnpfx (by rw [h]; exact beq_self_eq_true p1)
    have hdiv : someKey (.bin p1 l1 m1 k1) >>> (5 * (l1 + 1))
        ≠ someKey (.bin p2 l2 m2 k2) >>> (5 * (l1 + 1)) := by
      show prefixAbove (someKey (.bin p1 l1 m1 k1)) l1 ≠ prefixAbove (someKey (.bin p2 l2 m2 k2)) l1
      rw [hsk1]; exact fun h => hpfxne h.symm
    have hkne : someKey (.bin p1 l1 m1 k1) ≠ someKey (.bin p2 l2 m2 k2) := fun h => hdiv (by rw [h])
    have hbl_lt : l1 < branchLevel (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l2 m2 k2)) :=
      lt_branchLevel _ _ l1 hdiv
    have hl0' : 0 < branchLevel (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l2 m2 k2)) :=
      Nat.lt_trans hl0 hbl_lt
    rw [unionU, if_neg hne, if_neg hlne, if_pos hlt, if_neg hnpfx, join]
    refine WF_join _ _ _ _ (.bin p1 l1 m1 k1) (.bin p2 l2 m2 k2) hl0' (chunk_lt _ _) (chunk_lt _ _)
      (chunk_branchLevel_ne _ _ hkne) ?ha ?hb hwf1 hwf2 (by simp) (by simp)
    case ha => exact aligned_bin p1 l1 m1 k1 hwf1 _ hbl_lt
    case hb =>
      rw [prefixAbove_branchLevel_eq (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l2 m2 k2))]
      exact aligned_bin p2 l2 m2 k2 hwf2 _ (Nat.lt_trans hlt hbl_lt)
  | case19 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hnlt hpfx htb h IH =>
    intro hwf1 hwf2
    have hl12 : l1 < l2 := by
      have h1 : l1 ≠ l2 := by simpa using hlne
      omega
    have hwfchild : WF (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h) := by
      rw [WF] at hwf2; exact hwf2.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 = p2 := by simpa using hpfx
    have halign : AlignedAt l2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) p2 (.bin p1 l1 m1 k1) :=
      hpfxeq ▸ aligned_bin p1 l1 m1 k1 hwf1 l2 hl12
    rw [unionU, if_neg hne, if_neg hlne, if_neg hnlt, if_pos hpfx, if_pos htb, dif_pos h]
    exact WF_descend (.bin p1 l1 m1 k1) p2 l2 m2 k2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)
      (chunk_lt _ _) hwf2 halign hwf1 htb h (IH hwfchild hwf1)
  | case20 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hnlt hpfx htb hnh =>
    intro _ hwf2
    have hsize : k2.size = popCount m2 := by rw [WF] at hwf2; exact hwf2.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt m2 _ htb) hnh
  | case21 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hnlt hpfx hntb =>
    intro hwf1 hwf2
    have hl12 : l1 < l2 := by
      have h1 : l1 ≠ l2 := by simpa using hlne
      omega
    have hpfxeq : prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 = p2 := by simpa using hpfx
    have halign : AlignedAt l2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) p2 (.bin p1 l1 m1 k1) :=
      hpfxeq ▸ aligned_bin p1 l1 m1 k1 hwf1 l2 hl12
    have htbf : testBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) = false := by simpa using hntb
    rw [unionU, if_neg hne, if_neg hlne, if_neg hnlt, if_pos hpfx, if_neg hntb]
    exact WF_splice (.bin p1 l1 m1 k1) p2 l2 m2 k2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)
      (chunk_lt _ _) hwf2 halign hwf1 (by simp) htbf
  | case22 p1 l1 m1 k1 p2 l2 m2 k2 hne hlne hnlt hnpfx =>
    intro hwf1 hwf2
    have hl12 : l1 < l2 := by
      have h1 : l1 ≠ l2 := by simpa using hlne
      omega
    have hl20 : 0 < l2 := by rw [WF] at hwf2; exact hwf2.1
    have hm2ne : m2 ≠ 0 := by
      rw [WF] at hwf2; obtain ⟨_, _, hpc, _, _, _⟩ := hwf2
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hsk2 : prefixAbove (someKey (.bin p2 l2 m2 k2)) l2 = p2 :=
      someKey_bin_prefixAbove p2 l2 m2 k2 hm2ne
    have hpfxne : prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 ≠ p2 := by
      intro h; exact hnpfx (by rw [h]; exact beq_self_eq_true p2)
    have hdiv : someKey (.bin p2 l2 m2 k2) >>> (5 * (l2 + 1))
        ≠ someKey (.bin p1 l1 m1 k1) >>> (5 * (l2 + 1)) := by
      show prefixAbove (someKey (.bin p2 l2 m2 k2)) l2 ≠ prefixAbove (someKey (.bin p1 l1 m1 k1)) l2
      rw [hsk2]; exact fun h => hpfxne h.symm
    have hkne : someKey (.bin p2 l2 m2 k2) ≠ someKey (.bin p1 l1 m1 k1) := fun h => hdiv (by rw [h])
    have hbl_lt : l2 < branchLevel (someKey (.bin p2 l2 m2 k2)) (someKey (.bin p1 l1 m1 k1)) :=
      lt_branchLevel _ _ l2 hdiv
    have hl0' : 0 < branchLevel (someKey (.bin p2 l2 m2 k2)) (someKey (.bin p1 l1 m1 k1)) :=
      Nat.lt_trans hl20 hbl_lt
    rw [unionU, if_neg hne, if_neg hlne, if_neg hnlt, if_neg hnpfx, join]
    refine WF_join _ _ _ _ (.bin p2 l2 m2 k2) (.bin p1 l1 m1 k1) hl0' (chunk_lt _ _) (chunk_lt _ _)
      (chunk_branchLevel_ne _ _ hkne) ?ha ?hb hwf2 hwf1 (by simp) (by simp)
    case ha => exact aligned_bin p2 l2 m2 k2 hwf2 _ hbl_lt
    case hb =>
      rw [prefixAbove_branchLevel_eq (someKey (.bin p2 l2 m2 k2)) (someKey (.bin p1 l1 m1 k1))]
      exact aligned_bin p1 l1 m1 k1 hwf1 _ (Nat.lt_trans hl12 hbl_lt)
  | case23 m1 k1 m2 k2 rem acc hrem =>
    rename_i _ _ hacc c hmem
    rw [mergeKids, dif_pos hrem] at hmem
    exact hacc c hmem
  | case24 m1 k1 m2 k2 rem acc hrem IHchild IHrec =>
    rename_i hkw1 hkw2 hacc c hmem
    rw [mergeKids, dif_neg hrem] at hmem
    have hacc' : ∀ c' ∈ acc.push (mergeChild m1 k1 m2 k2 (lowestSetIdx rem)), WF c' := by
      intro c' hc'
      rcases Array.mem_push.mp hc' with hmemacc | heqx
      · exact hacc c' hmemacc
      · rw [heqx]; exact IHchild hkw1 hkw2
    exact IHrec hkw1 hkw2 hacc' c hmem
  | case25 m1 k1 m2 k2 i ht1 ht2 h1 h2 IH =>
    rename_i hkw1 hkw2
    rw [mergeChild, if_pos ht1, if_pos ht2, dif_pos h1, dif_pos h2]
    exact IH (hkw1.2.1 _ (Array.getElem_mem h1)) (hkw2.2.1 _ (Array.getElem_mem h2))
  | case26 m1 k1 m2 k2 i ht1 ht2 h1 hnh2 =>
    rename_i _ hkw2
    exact absurd (by rw [hkw2.1]; exact arrayIndex_lt m2 i ht2) hnh2
  | case27 m1 k1 m2 k2 i ht1 ht2 hnh1 =>
    rename_i hkw1 _
    exact absurd (by rw [hkw1.1]; exact arrayIndex_lt m1 i ht1) hnh1
  | case28 m1 k1 m2 k2 i ht1 hnt2 h1 =>
    rename_i hkw1 _
    rw [mergeChild, if_pos ht1, if_neg hnt2, dif_pos h1]
    exact hkw1.2.1 _ (Array.getElem_mem h1)
  | case29 m1 k1 m2 k2 i ht1 hnt2 hnh1 =>
    rename_i hkw1 _
    exact absurd (by rw [hkw1.1]; exact arrayIndex_lt m1 i ht1) hnh1
  | case30 m1 k1 m2 k2 i hnt1 h2 =>
    rename_i _ hkw2
    rw [mergeChild, if_neg hnt1, dif_pos h2]
    exact hkw2.2.1 _ (Array.getElem_mem h2)
  | case31 m1 k1 m2 k2 i hnt1 hnh2 =>
    rw [mergeChild, if_neg hnt1, dif_neg hnh2, WF]; trivial

/-- `WF_join` for the set: `union` keeps the canonical shape. The `WF` companion to `contains_union`;
together they make `union` a verified operation the lattice/order layer can build on. -/
theorem WF_union (a b : PTree) (hwa : WF a) (hwb : WF b) : WF (union a b) := by
  rw [union]; exact WF_unionU a b hwa hwb

/-! ### Extensionality

`contains` determines a well-formed tree uniquely: two `WF` trees with the same membership are equal
(`ext`). This lifts the `contains_*` seams to structural equalities, the bridge the lattice/order
laws cross (`union_comm` etc. follow from `ext` after matching membership pointwise). The proof rests
on `exists_mem` (a non-empty `WF` tree has a witness key) plus the routing invariant, which together
pin a `bin`'s level, prefix, mask, and children from its key set. -/

/-- A concrete member key: descend to the first child of every `bin`, then read a tip's lowest set
bit. Unlike `someKey` (which zeroes the bits below a node's level — only a prefix probe), this
follows a real path to a leaf, so a `WF` tree genuinely contains it. -/
private def witnessKey : PTree → Nat
  | .nil => 0
  | .tip pfx bits => (lowestSetIdx bits).toNat + 32 * pfx
  | .bin _ _ _ kids => if h : 0 < kids.size then witnessKey (kids[0]'h) else 0
decreasing_by
  simp_wf
  rename_i h
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem h)
  omega

/-- Adding a multiple of 32 leaves the bottom chunk unchanged. -/
private theorem chunk_zero_add_mul (a b : Nat) : chunk (a + 32 * b) 0 = chunk a 0 := by
  rw [chunk0_eq, chunk0_eq, Nat.add_mul_mod_self_left]

/-- `witnessKey` names a real member of any well-formed non-empty tree: a tip's lowest set bit, or
(recursively) a member of a `bin`'s first child — which routes back to that child by alignment. -/
private theorem contains_witnessKey :
    ∀ (t : PTree), WF t → t ≠ .nil → contains (witnessKey t) t = true := by
  intro t
  induction t using witnessKey.induct with
  | case1 => intro _ hne; exact absurd rfl hne
  | case2 pfx bits =>
    intro hwf _
    have hb : bits ≠ 0 := by rw [WF] at hwf; exact hwf
    have hlo : (lowestSetIdx bits).toNat < 32 := by
      have h := UInt32.lt_iff_toNat_lt.mp (lowestSetIdx_lt bits hb)
      rwa [show (32 : UInt32).toNat = 32 from by decide] at h
    rw [contains_tip, Bool.and_eq_true, beq_iff_eq, witnessKey]
    refine ⟨?_, ?_⟩
    · rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 5 = 32 from rfl,
          Nat.add_mul_div_left _ _ (by decide : 0 < 32), Nat.div_eq_of_lt hlo, Nat.zero_add]
    · rw [chunk_zero_add_mul, chunk_toNat_zero _ (lowestSetIdx_lt bits hb)]
      exact testBit_lowestSetIdx bits hb
  | case3 pfx level mask kids h IH =>
    intro hwf _
    rw [WF] at hwf
    obtain ⟨hlvl, hsize, hpc, hkidswf, hnonnil, hrout⟩ := hwf
    have hm : mask ≠ 0 := by
      intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    have hwf0 : WF (kids[0]'h) := hkidswf _ (Array.getElem_mem h)
    have hne0 : kids[0]'h ≠ .nil := hnonnil _ (Array.getElem_mem h)
    have hmem0 : contains (witnessKey (kids[0]'h)) (kids[0]'h) = true := IH hwf0 hne0
    have harr : arrayIndex mask (lowestSetIdx mask) = 0 := arrayIndex_lowestSetIdx mask hm
    have hc0tb : testBit mask (lowestSetIdx mask) = true := testBit_lowestSetIdx mask hm
    have hc0lt : lowestSetIdx mask < 32 := lowestSetIdx_lt mask hm
    have hchild0 : childAt mask kids (lowestSetIdx mask) = kids[0]'h := by
      unfold childAt; rw [harr, Array.getElem?_eq_getElem h, Option.getD_some]
    have halign : AlignedAt level (lowestSetIdx mask) pfx (kids[0]'h) := by
      have := hrout (lowestSetIdx mask) hc0lt hc0tb; rwa [hchild0] at this
    have hcj : chunk (witnessKey (kids[0]'h)) level = lowestSetIdx mask := (halign _ hmem0).1
    rw [show witnessKey (.bin pfx level mask kids) = witnessKey (kids[0]'h) from by
          rw [witnessKey, dif_pos h],
        contains_bin, hcj, hc0tb, Bool.true_and, hchild0]
    exact hmem0
  | case4 pfx level mask kids hns =>
    intro hwf _
    rw [WF] at hwf
    obtain ⟨_, hsize, hpc, _, _, _⟩ := hwf
    exact absurd (show 0 < kids.size by rw [hsize]; omega) hns

/-- A non-empty well-formed tree has a member: `contains` is not identically `false`. -/
theorem exists_mem (t : PTree) (hwf : WF t) (hne : t ≠ .nil) : ∃ j, contains j t = true :=
  ⟨witnessKey t, contains_witnessKey t hwf hne⟩

/-- The converse: a well-formed tree with no members is `nil`. The `nil` half of `ext`. -/
theorem eq_nil_of_no_member (t : PTree) (hwf : WF t) (h : ∀ j, contains j t = false) : t = .nil := by
  cases t with
  | nil => rfl
  | tip pfx bits =>
    have hpos := contains_witnessKey _ hwf (fun hc => PTree.noConfusion hc)
    rw [h] at hpos; exact absurd hpos (by decide)
  | bin pfx level mask kids =>
    have hpos := contains_witnessKey _ hwf (fun hc => PTree.noConfusion hc)
    rw [h] at hpos; exact absurd hpos (by decide)

/-- A present slot's child sits in the `kids` array (it is read at an in-range compact index). -/
private theorem childAt_mem (mask : UInt32) (kids : Array PTree) (c : UInt32)
    (hsize : kids.size = popCount mask) (htb : testBit mask c = true) :
    childAt mask kids c ∈ kids := by
  have hidx : arrayIndex mask c < kids.size := by rw [hsize]; exact arrayIndex_lt mask c htb
  have he : childAt mask kids c = kids[arrayIndex mask c]'hidx := by
    unfold childAt; rw [Array.getElem?_eq_getElem hidx, Option.getD_some]
  rw [he]; exact Array.getElem_mem hidx

/-- Every key in a well-formed `bin` carries the branch prefix. -/
private theorem prefixAbove_eq_of_mem (p l : Nat) (m : UInt32) (k : Array PTree)
    (hwf : WF (.bin p l m k)) (j : Nat) (hj : contains j (.bin p l m k) = true) :
    prefixAbove j l = p := by
  rw [WF] at hwf
  obtain ⟨_, _, _, _, _, hrout⟩ := hwf
  rw [contains_bin, Bool.and_eq_true] at hj
  obtain ⟨htb, hcc⟩ := hj
  exact (hrout (chunk j l) (chunk_lt _ _) htb j hcc).2

/-- A key contained in a present slot's child is contained in the `bin`: it routes back to that
slot (its chunk equals `c` by alignment). -/
private theorem mem_child_imp_mem_bin (p l : Nat) (m : UInt32) (k : Array PTree)
    (hwf : WF (.bin p l m k)) (c : UInt32) (hc : c < 32) (htb : testBit m c = true)
    (j : Nat) (hj : contains j (childAt m k c) = true) : contains j (.bin p l m k) = true := by
  rw [WF] at hwf
  obtain ⟨_, _, _, _, _, hrout⟩ := hwf
  have hcj : chunk j l = c := (hrout c hc htb j hj).1
  rw [contains_bin, hcj, htb, Bool.true_and]; exact hj

/-- Two keys whose prefixes agree above level `l2` agree on any chunk above `l2`. -/
private theorem chunk_eq_of_prefixAbove_lt {j1 j2 l1 l2 : Nat}
    (h : prefixAbove j1 l2 = prefixAbove j2 l2) (hlt : l2 < l1) : chunk j1 l1 = chunk j2 l1 := by
  have h' : j1 >>> (5 * (l2 + 1)) = j2 >>> (5 * (l2 + 1)) := h
  exact chunk_eq_of_shiftRight_eq (shiftRight_mono_eq h' (by omega))

/-- A "probe" key targeting slot `c`: prefix `p`, bottom chunk `c`. It is in `tip p bits` exactly
when bit `c` is set — the per-slot lever that recovers a tip's bitset from its membership. -/
private theorem contains_tip_probe (p : Nat) (bits : UInt32) (c : UInt32) (hc : c < 32) :
    contains (c.toNat + 32 * p) (.tip p bits) = testBit bits c := by
  have hclt : c.toNat < 32 := by
    have := UInt32.lt_iff_toNat_lt.mp hc; rwa [show (32 : UInt32).toNat = 32 from by decide] at this
  rw [contains_tip]
  have hpre : (c.toNat + 32 * p) >>> 5 = p := by
    rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 5 = 32 from rfl,
        Nat.add_mul_div_left _ _ (by decide : 0 < 32), Nat.div_eq_of_lt hclt, Nat.zero_add]
  have hch : chunk (c.toNat + 32 * p) 0 = c := by rw [chunk_zero_add_mul, chunk_toNat_zero _ hc]
  rw [hpre, hch, beq_self_eq_true, Bool.true_and]

/-- Compact indices cover `0..popCount mask`: every position `i` below the count is the compact
index of some present slot. The inverse of `arrayIndex` on present bits, needed to read a `bin`'s
children back by array index. -/
private theorem arrayIndex_surj : ∀ (n : Nat) (m : UInt32), popCount m = n →
    ∀ i, i < n → ∃ c, c < 32 ∧ testBit m c = true ∧ arrayIndex m c = i := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro m hpc i hi
    have hm : m ≠ 0 := by intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
    by_cases hi0 : i = 0
    · exact ⟨lowestSetIdx m, lowestSetIdx_lt m hm, testBit_lowestSetIdx m hm,
             by rw [arrayIndex_lowestSetIdx m hm, hi0]⟩
    · have hcl : popCount (clearLowest m) = n - 1 := by
        have := popCount_clearLowest m hm; omega
      have hclt : popCount (clearLowest m) < n := by omega
      obtain ⟨c, hc32, hctb, hcidx⟩ :=
        IH (popCount (clearLowest m)) hclt (clearLowest m) rfl (i - 1) (by omega)
      have htbm : testBit m c = true := testBit_of_clearLowest m c hctb
      have hcne : c ≠ lowestSetIdx m := by
        intro he
        rw [he, testBit_clearLowest_self m hm] at hctb; exact absurd hctb (by decide)
      refine ⟨c, hc32, htbm, ?_⟩
      rw [arrayIndex_clearLowest_of_ne m c hc32 htbm hcne, hcidx]; omega

/-- A well-formed `bin` (≥ 2 children) holds two keys that route to different slots at its level —
the divergence that pins down its branch level. -/
private theorem exists_two_divergent (p l : Nat) (m : UInt32) (k : Array PTree)
    (hwf : WF (.bin p l m k)) :
    ∃ j1 j2, contains j1 (.bin p l m k) = true ∧ contains j2 (.bin p l m k) = true
      ∧ chunk j1 l ≠ chunk j2 l := by
  have hwf' := hwf
  rw [WF] at hwf'
  obtain ⟨hlvl, hsize, hpc, hkidswf, hnonnil, hrout⟩ := hwf'
  have hm : m ≠ 0 := by intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
  have hclne : clearLowest m ≠ 0 := by
    intro h0
    have := popCount_clearLowest m hm
    rw [h0, show popCount 0 = 0 from rfl] at this; omega
  have hc1lt : lowestSetIdx m < 32 := lowestSetIdx_lt m hm
  have hc2lt : lowestSetIdx (clearLowest m) < 32 := lowestSetIdx_lt (clearLowest m) hclne
  have hc1tb : testBit m (lowestSetIdx m) = true := testBit_lowestSetIdx m hm
  have hc2tb : testBit m (lowestSetIdx (clearLowest m)) = true :=
    testBit_of_clearLowest m _ (testBit_lowestSetIdx (clearLowest m) hclne)
  have hcne : lowestSetIdx m ≠ lowestSetIdx (clearLowest m) := by
    intro he
    have h1 : testBit (clearLowest m) (lowestSetIdx m) = false := testBit_clearLowest_self m hm
    have h2 : testBit (clearLowest m) (lowestSetIdx (clearLowest m)) = true :=
      testBit_lowestSetIdx (clearLowest m) hclne
    rw [← he] at h2; rw [h1] at h2; exact absurd h2 (by decide)
  have hwfc1 : WF (childAt m k (lowestSetIdx m)) := hkidswf _ (childAt_mem m k _ hsize hc1tb)
  have hnec1 : childAt m k (lowestSetIdx m) ≠ .nil := hnonnil _ (childAt_mem m k _ hsize hc1tb)
  have hwfc2 : WF (childAt m k (lowestSetIdx (clearLowest m))) :=
    hkidswf _ (childAt_mem m k _ hsize hc2tb)
  have hnec2 : childAt m k (lowestSetIdx (clearLowest m)) ≠ .nil :=
    hnonnil _ (childAt_mem m k _ hsize hc2tb)
  obtain ⟨j1, hj1⟩ := exists_mem _ hwfc1 hnec1
  obtain ⟨j2, hj2⟩ := exists_mem _ hwfc2 hnec2
  refine ⟨j1, j2, mem_child_imp_mem_bin p l m k hwf _ hc1lt hc1tb j1 hj1,
          mem_child_imp_mem_bin p l m k hwf _ hc2lt hc2tb j2 hj2, ?_⟩
  have ha1 : chunk j1 l = lowestSetIdx m := (hrout _ hc1lt hc1tb j1 hj1).1
  have ha2 : chunk j2 l = lowestSetIdx (clearLowest m) := (hrout _ hc2lt hc2tb j2 hj2).1
  rw [ha1, ha2]; exact hcne

/-- Two `bin`s with the same key set cannot have `lA < lB`: `b`'s keys diverge at `lB`, but being in
`a` they agree above `lA`, hence (as `lA < lB`) agree at `lB` — contradiction. Pins the level. -/
private theorem not_lt_level (pA lA : Nat) (mA : UInt32) (kA : Array PTree)
    (pB lB : Nat) (mB : UInt32) (kB : Array PTree)
    (hwa : WF (.bin pA lA mA kA)) (hwb : WF (.bin pB lB mB kB))
    (h : ∀ j, contains j (.bin pA lA mA kA) = contains j (.bin pB lB mB kB)) : ¬ lA < lB := by
  intro hlt
  obtain ⟨j1, j2, hj1, hj2, hne⟩ := exists_two_divergent pB lB mB kB hwb
  have hj1a : contains j1 (.bin pA lA mA kA) = true := by rw [h]; exact hj1
  have hj2a : contains j2 (.bin pA lA mA kA) = true := by rw [h]; exact hj2
  have hp1 : prefixAbove j1 lA = pA := prefixAbove_eq_of_mem pA lA mA kA hwa j1 hj1a
  have hp2 : prefixAbove j2 lA = pA := prefixAbove_eq_of_mem pA lA mA kA hwa j2 hj2a
  exact hne (chunk_eq_of_prefixAbove_lt (hp1.trans hp2.symm) hlt)

/-- Same key set + same level ⇒ same present slots: a slot present in `mA` holds a key (by
`exists_mem`) that, being in `b`, forces the matching slot of `mB`. Pins the mask (with its mirror). -/
private theorem mask_testBit_imp (pA l : Nat) (mA : UInt32) (kA : Array PTree)
    (pB : Nat) (mB : UInt32) (kB : Array PTree)
    (hwa : WF (.bin pA l mA kA)) (hwb : WF (.bin pB l mB kB))
    (h : ∀ j, contains j (.bin pA l mA kA) = contains j (.bin pB l mB kB))
    (c : UInt32) (hc : c < 32) (htb : testBit mA c = true) : testBit mB c = true := by
  have hwa' := hwa
  rw [WF] at hwa'
  obtain ⟨_, hsizeA, _, hkidswfA, hnonnilA, hroutA⟩ := hwa'
  have hwfc : WF (childAt mA kA c) := hkidswfA _ (childAt_mem mA kA c hsizeA htb)
  have hnec : childAt mA kA c ≠ .nil := hnonnilA _ (childAt_mem mA kA c hsizeA htb)
  obtain ⟨j, hj⟩ := exists_mem _ hwfc hnec
  have hcj : chunk j l = c := (hroutA c hc htb j hj).1
  have hjA : contains j (.bin pA l mA kA) = true := mem_child_imp_mem_bin pA l mA kA hwa c hc htb j hj
  have hjB : contains j (.bin pB l mB kB) = true := by rw [← h]; exact hjA
  rw [contains_bin, Bool.and_eq_true] at hjB
  rw [← hcj]; exact hjB.1

/-- Same key set + same level/prefix/mask ⇒ matching present children have the same key set: a key
routes to slot `c` in both, or to neither (alignment kills it). Drives the per-child recursion. -/
private theorem child_mem_eq (p l : Nat) (m : UInt32) (kA kB : Array PTree)
    (hwa : WF (.bin p l m kA)) (hwb : WF (.bin p l m kB))
    (h : ∀ j, contains j (.bin p l m kA) = contains j (.bin p l m kB))
    (c : UInt32) (hc : c < 32) (htb : testBit m c = true) (x : Nat) :
    contains x (childAt m kA c) = contains x (childAt m kB c) := by
  by_cases hcx : chunk x l = c
  · have eA : contains x (.bin p l m kA) = contains x (childAt m kA c) := by
      rw [contains_bin, hcx, htb, Bool.true_and]
    have eB : contains x (.bin p l m kB) = contains x (childAt m kB c) := by
      rw [contains_bin, hcx, htb, Bool.true_and]
    rw [← eA, ← eB, h]
  · have hwa' := hwa; rw [WF] at hwa'
    have hwb' := hwb; rw [WF] at hwb'
    obtain ⟨_, _, _, _, _, hroutA⟩ := hwa'
    obtain ⟨_, _, _, _, _, hroutB⟩ := hwb'
    rw [contains_false_of_aligned l c p _ (hroutA c hc htb) hcx,
        contains_false_of_aligned l c p _ (hroutB c hc htb) hcx]

/-- **Extensionality**: two well-formed trees with the same membership are equal. The keystone that
lifts the `contains_*` seams to structural equalities, so the lattice/order laws reduce to matching
membership pointwise. By recursion on `a`: `nil` pins by `eq_nil_of_no_member`; a `tip` vs a `bin`
is impossible (a `bin` diverges, a `tip` does not); two `tip`s share prefix and bitset (probe keys);
two `bin`s share level, prefix, mask (`not_lt_level`/`mask_testBit_imp`) and then, child by child,
recurse. -/
theorem ext (a b : PTree) (hwa : WF a) (hwb : WF b)
    (h : ∀ j, contains j a = contains j b) : a = b := by
  match a, b, hwa, hwb, h with
  | .nil, b, _, hwb, h =>
    exact (eq_nil_of_no_member b hwb (fun j => by rw [← h j, contains_nil])).symm
  | .tip p1 b1, .nil, hwa, _, h =>
    exact eq_nil_of_no_member _ hwa (fun j => by rw [h j, contains_nil])
  | .bin p1 l1 m1 k1, .nil, hwa, _, h =>
    exact eq_nil_of_no_member _ hwa (fun j => by rw [h j, contains_nil])
  | .tip p1 b1, .bin p2 l2 m2 k2, hwa, hwb, h =>
    exfalso
    obtain ⟨j1, j2, hj1, hj2, hne⟩ := exists_two_divergent p2 l2 m2 k2 hwb
    have hj1a : contains j1 (.tip p1 b1) = true := by rw [h]; exact hj1
    have hj2a : contains j2 (.tip p1 b1) = true := by rw [h]; exact hj2
    rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hj1a hj2a
    have hbl0 : 0 < l2 := by rw [WF] at hwb; exact hwb.1
    apply hne
    apply chunk_eq_of_shiftRight_eq
    exact shiftRight_mono_eq (hj1a.1.trans hj2a.1.symm) (by omega)
  | .bin p1 l1 m1 k1, .tip p2 b2, hwa, hwb, h =>
    exfalso
    obtain ⟨j1, j2, hj1, hj2, hne⟩ := exists_two_divergent p1 l1 m1 k1 hwa
    have hj1b : contains j1 (.tip p2 b2) = true := by rw [← h]; exact hj1
    have hj2b : contains j2 (.tip p2 b2) = true := by rw [← h]; exact hj2
    rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hj1b hj2b
    have hbl0 : 0 < l1 := by rw [WF] at hwa; exact hwa.1
    apply hne
    apply chunk_eq_of_shiftRight_eq
    exact shiftRight_mono_eq (hj1b.1.trans hj2b.1.symm) (by omega)
  | .tip p1 b1, .tip p2 b2, hwa, hwb, h =>
    have hp : p1 = p2 := by
      obtain ⟨j, hj⟩ := exists_mem (.tip p1 b1) hwa (fun hc => PTree.noConfusion hc)
      have hjb : contains j (.tip p2 b2) = true := by rw [← h]; exact hj
      rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hj hjb
      rw [← hj.1, ← hjb.1]
    subst hp
    have hbits : b1 = b2 := by
      apply eq_of_testBit_eq
      intro c hc
      rw [← contains_tip_probe p1 b1 c hc, ← contains_tip_probe p1 b2 c hc, h]
    rw [hbits]
  | .bin p1 l1 m1 k1, .bin p2 l2 m2 k2, hwa, hwb, h =>
    have hl : l1 = l2 := by
      have h1 := not_lt_level p1 l1 m1 k1 p2 l2 m2 k2 hwa hwb h
      have h2 := not_lt_level p2 l2 m2 k2 p1 l1 m1 k1 hwb hwa (fun j => (h j).symm)
      omega
    subst hl
    have hp : p1 = p2 := by
      obtain ⟨j, hj⟩ := exists_mem (.bin p1 l1 m1 k1) hwa (fun hc => PTree.noConfusion hc)
      have hjb : contains j (.bin p2 l1 m2 k2) = true := by rw [← h]; exact hj
      rw [← prefixAbove_eq_of_mem p1 l1 m1 k1 hwa j hj,
          ← prefixAbove_eq_of_mem p2 l1 m2 k2 hwb j hjb]
    subst hp
    have hm : m1 = m2 := by
      apply eq_of_testBit_eq
      intro c hc
      have d1 := mask_testBit_imp p1 l1 m1 k1 p1 m2 k2 hwa hwb h c hc
      have d2 := mask_testBit_imp p1 l1 m2 k2 p1 m1 k1 hwb hwa (fun j => (h j).symm) c hc
      by_cases hb1 : testBit m1 c = true
      · rw [hb1, d1 hb1]
      · have hb1f : testBit m1 c = false := by simpa using hb1
        by_cases hb2 : testBit m2 c = true
        · exact absurd (d2 hb2) hb1
        · have hb2f : testBit m2 c = false := by simpa using hb2
          rw [hb1f, hb2f]
    subst hm
    have hsizeA : k1.size = popCount m1 := by rw [WF] at hwa; exact hwa.2.1
    have hsizeB : k2.size = popCount m1 := by rw [WF] at hwb; exact hwb.2.1
    have hwa' := hwa; rw [WF] at hwa'
    have hwb' := hwb; rw [WF] at hwb'
    obtain ⟨_, _, _, hkidswfA, _, _⟩ := hwa'
    obtain ⟨_, _, _, hkidswfB, _, _⟩ := hwb'
    have hk : k1 = k2 := by
      apply Array.ext
      · rw [hsizeA, hsizeB]
      · intro i hi1 hi2
        obtain ⟨c, hc, htb, hac⟩ :=
          arrayIndex_surj (popCount m1) m1 rfl i (by rw [← hsizeA]; exact hi1)
        have hk1 : k1[i]'hi1 = childAt m1 k1 c := by
          unfold childAt; rw [hac, Array.getElem?_eq_getElem hi1, Option.getD_some]
        have hk2 : k2[i]'hi2 = childAt m1 k2 c := by
          unfold childAt; rw [hac, Array.getElem?_eq_getElem hi2, Option.getD_some]
        refine ext (k1[i]'hi1) (k2[i]'hi2) (hkidswfA _ (Array.getElem_mem hi1))
          (hkidswfB _ (Array.getElem_mem hi2)) ?_
        intro x
        rw [hk1, hk2]
        exact child_mem_eq p1 l1 m1 k1 k2 hwa hwb h c hc htb x
    rw [hk]
termination_by sizeOf a
decreasing_by
  simp_wf
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem hi1)
  omega

/-! ### Lattice laws for `union`

With `ext` and `contains_union` in hand, the set-algebra laws reduce to Boolean identities on
membership. These are the `NatSet`-facing contract the order/lattice layer will export. -/

/-- Union is commutative. -/
theorem union_comm (a b : PTree) (hwa : WF a) (hwb : WF b) : union a b = union b a := by
  refine ext _ _ (WF_union a b hwa hwb) (WF_union b a hwb hwa) (fun j => ?_)
  rw [contains_union j a b hwa hwb, contains_union j b a hwb hwa, Bool.or_comm]

/-- Union is associative. -/
theorem union_assoc (a b c : PTree) (hwa : WF a) (hwb : WF b) (hwc : WF c) :
    union (union a b) c = union a (union b c) := by
  refine ext _ _ (WF_union _ c (WF_union a b hwa hwb) hwc)
    (WF_union a _ hwa (WF_union b c hwb hwc)) (fun j => ?_)
  rw [contains_union j _ c (WF_union a b hwa hwb) hwc, contains_union j a b hwa hwb,
      contains_union j a _ hwa (WF_union b c hwb hwc), contains_union j b c hwb hwc, Bool.or_assoc]

/-- Union is idempotent. -/
theorem union_self (a : PTree) (hwa : WF a) : union a a = a := by
  refine ext _ _ (WF_union a a hwa hwa) hwa (fun j => ?_)
  rw [contains_union j a a hwa hwa, Bool.or_self]

/-- `empty` is a right identity for union. -/
theorem union_empty (a : PTree) (hwa : WF a) : union a empty = a := by
  refine ext _ _ (WF_union a empty hwa WF_empty) hwa (fun j => ?_)
  rw [contains_union j a empty hwa WF_empty]
  simp only [empty, contains_nil, Bool.or_false]

/-- `empty` is a left identity for union. -/
theorem empty_union (a : PTree) (hwa : WF a) : union empty a = a := by
  refine ext _ _ (WF_union empty a WF_empty hwa) hwa (fun j => ?_)
  rw [contains_union j empty a WF_empty hwa]
  simp only [empty, contains_nil, Bool.false_or]

/-- Inserting two keys commutes. -/
theorem insert_comm (a b : Nat) (t : PTree) (hwt : WF t) :
    insert a (insert b t) = insert b (insert a t) := by
  refine ext _ _ (WF_insert a _ (WF_insert b t hwt)) (WF_insert b _ (WF_insert a t hwt)) (fun j => ?_)
  rw [contains_insert a j _ (WF_insert b t hwt), contains_insert b j t hwt,
      contains_insert b j _ (WF_insert a t hwt), contains_insert a j t hwt,
      ← Bool.or_assoc, ← Bool.or_assoc, Bool.or_comm (j == a) (j == b)]

/-- Re-inserting a key is idempotent. -/
theorem insert_idem (a : Nat) (t : PTree) (hwt : WF t) : insert a (insert a t) = insert a t := by
  refine ext _ _ (WF_insert a _ (WF_insert a t hwt)) (WF_insert a t hwt) (fun j => ?_)
  rw [contains_insert a j _ (WF_insert a t hwt), contains_insert a j t hwt, ← Bool.or_assoc,
      Bool.or_self]

end PTree
end NatCol
