-- Path-compressed (Patricia) trie — the height-erased successor to `NatCol.Tree`.
--
-- `Tree leaf : Nat → Type` (Tree.lean) indexes height in the TYPE, so a single sparse key
-- forces a chain of single-child `Node`s up to that height (≈13 for a 63-bit key). This module
-- replaces it with a height-ERASED trie where a single-child run creates no node at all: a `tip`
-- carries its whole prefix, a `bin` branches only where ≥2 keys actually diverge. That removes the
-- chains the benchmark showed cost ~6× memory and a cache-missing pointer per level.
--
-- Like `Tree`, the trie is generic over the leaf via `LeafOps L V` (`V` the value type — `Unit`
-- for sets, `α` for maps), so `NatSet`/`NatMap` will be thin instantiations: a `tip` carries a leaf
-- `L` over the low 5 bits. Because children of a `bin` have non-uniform depth, there is no height
-- index to recurse on, so every operation is TOTAL via well-founded recursion on `sizeOf` (see
-- `~/.claude/.../path-compression-termination-recipe.md`). This iteration is implementation +
-- `#guard` cross-checks against the verified `NatSet` (at the set instance); the well-formedness
-- predicate and the denotational/lattice proofs are layered on top in later stages.
import NatCol

namespace NatCol

/-- A 32-way, big-endian, path-compressed collection keyed by `Nat`, generic over the leaf `L`
(`LeafOps L V`, `V` the value type).
* `tip pfx leaf` — a leaf holding every key `k` with `k >>> 5 = pfx`; the leaf `L` maps the bottom
  5 bits to values (a `UInt32` bitset for sets, a `Node α` for maps).
* `bin pfx level mask kids` — a path-compressed branch on the 5-bit `chunk` at `level` (always
  `≥ 1`); `pfx` is the common prefix above `level` (`k >>> 5*(level+1)`), `kids` holds the present
  children compactly (`kids.size = popCount mask`, maintained by construction). -/
inductive PTree (L : Type u) where
  | nil
  | tip (pfx : Nat) (leaf : L)
  | bin (pfx : Nat) (level : Nat) (mask : UInt32) (kids : Array (PTree L))
  deriving Inhabited

namespace PTree

variable {L : Type u} {V : Type u} [LeafOps L V]

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
`branchLevel`/prefix comparisons need). A `tip`'s representative slot comes from the leaf
(`LeafOps.someSlot`). -/
def someKey : PTree L → Nat
  | .nil                  => 0
  | .tip pfx leaf         => (pfx <<< 5) ||| (LeafOps.someSlot leaf).toNat
  | .bin pfx level mask _ => (pfx <<< (5 * (level + 1))) ||| ((lowestSetIdx mask).toNat <<< (5 * level))

/-- The empty collection. -/
@[inline] def empty : PTree L := .nil

/-- The singleton `{k ↦ v}` — a single `tip`, no interior nodes. -/
@[inline] def singleton (k : Nat) (v : V) : PTree L :=
  .tip (k >>> 5) (LeafOps.insert LeafOps.empty (chunk k 0) v)

/-- Combine two subtrees with **disjoint** prefixes (representative keys `ka ≠ kb`) under a fresh
`bin` branching at their first differing chunk. -/
@[inline] def join (ka : Nat) (a : PTree L) (kb : Nat) (b : PTree L) : PTree L :=
  let l := branchLevel ka kb
  let ca := chunk ka l
  let cb := chunk kb l
  .bin (prefixAbove ka l) l (setBit (setBit 0 ca) cb) (if ca < cb then #[a, b] else #[b, a])

-- `hb` is consumed by the `'hb` term-level array access; the linter doesn't track that through `dite`.
set_option linter.unusedVariables false in
/-- Membership (classic Patricia: route by chunk through the bins, verify the prefix at the tip).
Total: the present child is reached with the in-bounds proof `hb` (a `dite`, never an
`Option`-match — the latter trips the kernel's deep-recursion check inside well-founded recursion). -/
def contains (k : Nat) : PTree L → Bool
  | .nil          => false
  | .tip pfx leaf => k >>> 5 == pfx && LeafOps.contains leaf (chunk k 0)
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
/-- Lookup (the map denotation): route by chunk, then read the leaf at the bottom chunk. For a set
this is the `isSome` shadow of `contains`. -/
def get? (k : Nat) : PTree L → Option V
  | .nil          => none
  | .tip pfx leaf => if k >>> 5 == pfx then LeafOps.get? leaf (chunk k 0) else none
  | .bin _ level mask kids =>
    if testBit mask (chunk k level) then
      if hb : arrayIndex mask (chunk k level) < kids.size then
        get? k (kids[arrayIndex mask (chunk k level)]'hb)
      else none
    else none
decreasing_by
  simp_wf
  rename_i hb
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb)
  omega

set_option linter.unusedVariables false in
/-- Insert `k ↦ v`. Descends by chunk while the prefix matches; a prefix mismatch (divergence at a
compressed level) `join`s a fresh singleton in. -/
def insert (k : Nat) (v : V) : PTree L → PTree L
  | .nil          => singleton k v
  | .tip pfx leaf =>
    if k >>> 5 == pfx then .tip pfx (LeafOps.insert leaf (chunk k 0) v)
    else join k (singleton k v) ((pfx <<< 5) ||| (LeafOps.someSlot leaf).toNat) (.tip pfx leaf)
  | .bin pfx level mask kids =>
    if prefixAbove k level == pfx then
      if testBit mask (chunk k level) then
        if hb : arrayIndex mask (chunk k level) < kids.size then
          .bin pfx level mask (kids.setIfInBounds (arrayIndex mask (chunk k level))
            (insert k v (kids[arrayIndex mask (chunk k level)]'hb)))
        else .bin pfx level mask kids
      else
        .bin pfx level (setBit mask (chunk k level))
          (kids.insertIdx! (arrayIndex mask (chunk k level)) (singleton k v))
    else join k (singleton k v) (someKey (.bin pfx level mask kids)) (.bin pfx level mask kids)
decreasing_by
  simp_wf
  rename_i hb
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb)
  omega

/-- Number of keys, summing each `tip`'s leaf size over children (`attach` carries the membership
the well-founded recursion needs). -/
def size : PTree L → Nat
  | .nil           => 0
  | .tip _ leaf    => LeafOps.size leaf
  | .bin _ _ _ kids => kids.attach.foldl (fun acc ⟨c, _⟩ => acc + c.size) 0
decreasing_by
  simp_wf
  rename_i c hc
  have := Array.sizeOf_lt_of_mem hc
  omega

/-- Total child accessor: the subtree a `bin`'s mask routes slot `c` to, `nil` when the slot is
absent (or the compact index is out of range). Gives every membership/merge proof one total
accessor in place of the raw `dite` bounds juggling. -/
@[inline] def childAt (mask : UInt32) (kids : Array (PTree L)) (c : UInt32) : PTree L :=
  (kids[arrayIndex mask c]?).getD .nil

-- Union — three mutually-recursive pieces, total via a shared lexicographic measure on combined
-- subtree size. `mergeChild` is split out of `mergeKids` only to keep the latter's body shallow: a
-- deeply-nested `let` under a well-founded recursion trips the kernel's deep-recursion check. The
-- `+1` on `mergeKids`'s measure orders its (equal-size) hand-off to `mergeChild` as a strict
-- decrease; `mergeKids`'s own recursion shrinks the leftover mask `rem` in the second component.
-- Coinciding keys are resolved at the leaf with `c` (`LeafOps.join`).
set_option linter.unusedVariables false in
mutual
/-- Union driver: merge matching `tip`/`bin` shapes in place, `join` mismatched prefixes under a
fresh branch, and combine two aligned `bin`s child-by-child through `mergeKids`. -/
def unionU (c : V → V → V) : PTree L → PTree L → PTree L
  | .nil, t => t
  | s, .nil => s
  | .tip p1 b1, .tip p2 b2 =>
    if p1 == p2 then .tip p1 (LeafOps.join c b1 b2)
    else join (someKey (.tip p1 b1)) (.tip p1 b1) (someKey (.tip p2 b2)) (.tip p2 b2)
  | .tip p1 b1, .bin bp bl bm bk =>
      if prefixAbove (someKey (.tip p1 b1)) bl == bp then
        if testBit bm (chunk (someKey (.tip p1 b1)) bl) then
          if h : arrayIndex bm (chunk (someKey (.tip p1 b1)) bl) < bk.size then
            .bin bp bl bm (bk.setIfInBounds (arrayIndex bm (chunk (someKey (.tip p1 b1)) bl))
              (unionU c (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h) (.tip p1 b1)))
          else .bin bp bl bm bk
        else .bin bp bl (setBit bm (chunk (someKey (.tip p1 b1)) bl))
          (bk.insertIdx! (arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)) (.tip p1 b1))
      else join (someKey (.bin bp bl bm bk)) (.bin bp bl bm bk) (someKey (.tip p1 b1)) (.tip p1 b1)
  | .bin bp bl bm bk, .tip p2 b2 =>
      if prefixAbove (someKey (.tip p2 b2)) bl == bp then
        if testBit bm (chunk (someKey (.tip p2 b2)) bl) then
          if h : arrayIndex bm (chunk (someKey (.tip p2 b2)) bl) < bk.size then
            .bin bp bl bm (bk.setIfInBounds (arrayIndex bm (chunk (someKey (.tip p2 b2)) bl))
              (unionU c (bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h) (.tip p2 b2)))
          else .bin bp bl bm bk
        else .bin bp bl (setBit bm (chunk (someKey (.tip p2 b2)) bl))
          (bk.insertIdx! (arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)) (.tip p2 b2))
      else join (someKey (.bin bp bl bm bk)) (.bin bp bl bm bk) (someKey (.tip p2 b2)) (.tip p2 b2)
  | .bin p1 l1 m1 k1, .bin p2 l2 m2 k2 =>
    if l1 == l2 && p1 == p2 then
      .bin p1 l1 (m1 ||| m2) (mergeKids c m1 k1 m2 k2 (m1 ||| m2) #[])
    else if l1 == l2 then
      join (someKey (.bin p1 l1 m1 k1)) (.bin p1 l1 m1 k1) (someKey (.bin p2 l2 m2 k2)) (.bin p2 l2 m2 k2)
    else if l2 < l1 then
      if prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 == p1 then
        if testBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) then
          if h : arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) < k1.size then
            .bin p1 l1 m1 (k1.setIfInBounds (arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1))
              (unionU c (k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h) (.bin p2 l2 m2 k2)))
          else .bin p1 l1 m1 k1
        else .bin p1 l1 (setBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1))
          (k1.insertIdx! (arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)) (.bin p2 l2 m2 k2))
      else join (someKey (.bin p1 l1 m1 k1)) (.bin p1 l1 m1 k1) (someKey (.bin p2 l2 m2 k2)) (.bin p2 l2 m2 k2)
    else
      if prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 == p2 then
        if testBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) then
          if h : arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) < k2.size then
            .bin p2 l2 m2 (k2.setIfInBounds (arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2))
              (unionU c (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h) (.bin p1 l1 m1 k1)))
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
def mergeChild (c : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32) (k2 : Array (PTree L)) (i : UInt32) : PTree L :=
  if testBit m1 i then
    if testBit m2 i then
      if h1 : arrayIndex m1 i < k1.size then
        if h2 : arrayIndex m2 i < k2.size then
          unionU c (k1[arrayIndex m1 i]'h1) (k2[arrayIndex m2 i]'h2)
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
def mergeKids (c : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32) (k2 : Array (PTree L))
    (rem : UInt32) (acc : Array (PTree L)) : Array (PTree L) :=
  if hrem : rem == 0 then acc
  else
    mergeKids c m1 k1 m2 k2 (clearLowest rem) (acc.push (mergeChild c m1 k1 m2 k2 (lowestSetIdx rem)))
termination_by (sizeOf k1 + sizeOf k2 + 1, rem.toNat)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have : (clearLowest rem).toNat < rem.toNat :=
         UInt32.lt_iff_toNat_lt.mp (clearLowest_lt rem (by simp_all)); omega)
end

/-- Union `a ∪ b`, resolving coinciding keys with `c`. -/
@[inline] def union (c : V → V → V) (a b : PTree L) : PTree L := unionU c a b

/-- Build from a list of key/value pairs, by repeated insertion (later pairs win at a key). -/
def ofList (kvs : List (Nat × V)) : PTree L := kvs.foldl (fun s kv => s.insert kv.1 kv.2) .nil

-- Structural subset `a ⊆ b` — a Patricia walk that aligns the two trees by branch level and
-- short-circuits on the masks (replacing a naive O(|a|) per-key membership walk). Route the
-- narrower-span operand into the wider, compare leaves with `rel` (`LeafOps.restricts`), bail the
-- moment a slot is missing.
set_option linter.unusedVariables false in
mutual
/-- Subset driver: `nil ⊆ _`; a `bin` never fits a single `tip`; two `tip`s compare leaves; a `tip`
or narrower `bin` routes into the matching child of the wider `bin`; equal-level `bin`s need
`m1 ⊆ m2` plus every shared child (`subsetKids`). -/
def subsetU (rel : V → V → Bool) : PTree L → PTree L → Bool
  | .nil, _ => true
  | .tip _ _, .nil => false
  | .bin _ _ _ _, .nil => false
  | .tip p1 b1, .tip p2 b2 => p1 == p2 && LeafOps.restricts rel b1 b2
  | .tip p1 b1, .bin bp bl bm bk =>
    prefixAbove (someKey (.tip p1 b1)) bl == bp
      && testBit bm (chunk (someKey (.tip p1 b1)) bl)
      && (if h : arrayIndex bm (chunk (someKey (.tip p1 b1)) bl) < bk.size then
            subsetU rel (.tip p1 b1) (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h)
          else false)
  | .bin _ _ _ _, .tip _ _ => false
  | .bin p1 l1 m1 k1, .bin p2 l2 m2 k2 =>
    if l1 == l2 then
      prefixAbove (someKey (.bin p1 l1 m1 k1)) l1 == prefixAbove (someKey (.bin p2 l2 m2 k2)) l1
        && (m1 &&& m2) == m1 && subsetKids rel m1 k1 m2 k2 m1
    else if l1 < l2 then
      prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 == prefixAbove (someKey (.bin p2 l2 m2 k2)) l2
        && testBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)
        && (if h : arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) < k2.size then
              subsetU rel (.bin p1 l1 m1 k1)
                (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h)
            else false)
    else false
termination_by a b => (sizeOf a + sizeOf b, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := Array.sizeOf_lt_of_mem (Array.getElem_mem h); omega)

/-- Confirm every `a`-child is a subset of the aligned `b`-child for two equal-level/prefix bins
with `m1 ⊆ m2` checked, bit-scanning the shared mask `rem` (= `m1`) lowest-first. -/
def subsetKids (rel : V → V → Bool) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32) (k2 : Array (PTree L)) (rem : UInt32) :
    Bool :=
  if hrem : rem == 0 then true
  else
    (if h1 : arrayIndex m1 (lowestSetIdx rem) < k1.size then
      if h2 : arrayIndex m2 (lowestSetIdx rem) < k2.size then
        subsetU rel (k1[arrayIndex m1 (lowestSetIdx rem)]'h1) (k2[arrayIndex m2 (lowestSetIdx rem)]'h2)
      else false
    else false)
      && subsetKids rel m1 k1 m2 k2 (clearLowest rem)
termination_by (sizeOf k1 + sizeOf k2 + 1, rem.toNat)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := Array.sizeOf_lt_of_mem (Array.getElem_mem h1)
       have := Array.sizeOf_lt_of_mem (Array.getElem_mem h2); omega)
    | (have : (clearLowest rem).toNat < rem.toNat :=
         UInt32.lt_iff_toNat_lt.mp (clearLowest_lt rem (by simp_all)); omega)
    | omega
end

/-- `a ⊆ b`: every key of `a` is in `b` (with values related by `rel` at coinciding keys), via the
structural Patricia walk. -/
@[inline] def subset (rel : V → V → Bool) (a b : PTree L) : Bool := subsetU rel a b

-- Intersection — like union, three mutually-recursive pieces over a shared lexicographic measure,
-- but intersection only ever shrinks: it touches just the shared mask `m1 &&& m2` and can leave a
-- branch with fewer than two surviving children, so the equal-level `bin`/`bin` case re-compresses
-- via `compactify` (drop the now-empty children, recompute the mask) + `finalize` (0 survivors →
-- `nil`, 1 → lift the lone child, ≥ 2 → `bin`). The routing cases just descend. Coinciding keys are
-- resolved at the leaf with `c` (`LeafOps.meet`); a leaf whose intersection empties is dropped.

/-- `nil`-test as a `Bool`, for the re-compression fold (keeps it off the `Option`-match path that
trips the kernel inside a well-founded recursion). -/
@[inline] def isNil : PTree L → Bool
  | .nil => true
  | _    => false

/-- Drop the empty (`nil`) children from a mask-compact array and recompute the surviving mask: fold
the mask `rem` lowest-first, keeping each non-empty child and setting its bit. Re-establishes the
"no nil children" / "compact" invariants after an intersection thins a branch. -/
def compactify (mask : UInt32) (kids : Array (PTree L)) (rem : UInt32) (accM : UInt32)
    (acc : Array (PTree L)) : UInt32 × Array (PTree L) :=
  if hrem : rem == 0 then (accM, acc)
  else
    if isNil (childAt mask kids (lowestSetIdx rem)) then
      compactify mask kids (clearLowest rem) accM acc
    else
      compactify mask kids (clearLowest rem) (setBit accM (lowestSetIdx rem))
        (acc.push (childAt mask kids (lowestSetIdx rem)))
termination_by rem.toNat
decreasing_by
  all_goals
    have : (clearLowest rem).toNat < rem.toNat :=
      UInt32.lt_iff_toNat_lt.mp (clearLowest_lt rem (by simp_all))
    omega

/-- Re-wrap a re-compressed branch: empty → `nil`, a single survivor → that child (lift the
collapsed level — the path-compression step), otherwise a `bin`. -/
def finalize (p l : Nat) (mask : UInt32) (kids : Array (PTree L)) : PTree L :=
  match compactify mask kids mask 0 #[] with
  | (m, ks) =>
    if m == 0 then .nil
    else if popCount m == 1 then (ks[0]?).getD .nil
    else .bin p l m ks

set_option linter.unusedVariables false in
mutual
/-- Intersection driver: empty on either `nil`; two `tip`s meet their leaves (drop if disjoint or
empty); a `tip` or off-level `bin` descends into the one matching child; two equal-level `bin`s
intersect the shared mask child-by-child (`meetKids`) then re-compress (`finalize`). -/
def meetU (c : V → V → V) : PTree L → PTree L → PTree L
  | .nil, _ => .nil
  | .tip _ _, .nil => .nil
  | .bin _ _ _ _, .nil => .nil
  | .tip p1 b1, .tip p2 b2 =>
    if p1 == p2 then
      (if LeafOps.isEmpty (LeafOps.meet c b1 b2) then .nil else .tip p1 (LeafOps.meet c b1 b2))
    else .nil
  | .tip p1 b1, .bin bp bl bm bk =>
    if prefixAbove (someKey (.tip p1 b1)) bl == bp
        && testBit bm (chunk (someKey (.tip p1 b1)) bl) then
      if h : arrayIndex bm (chunk (someKey (.tip p1 b1)) bl) < bk.size then
        meetU c (.tip p1 b1) (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h)
      else .nil
    else .nil
  | .bin bp bl bm bk, .tip p2 b2 =>
    if prefixAbove (someKey (.tip p2 b2)) bl == bp
        && testBit bm (chunk (someKey (.tip p2 b2)) bl) then
      if h : arrayIndex bm (chunk (someKey (.tip p2 b2)) bl) < bk.size then
        meetU c (bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h) (.tip p2 b2)
      else .nil
    else .nil
  | .bin p1 l1 m1 k1, .bin p2 l2 m2 k2 =>
    if l1 == l2 then
      if prefixAbove (someKey (.bin p1 l1 m1 k1)) l1
          == prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 then
        finalize p1 l1 (m1 &&& m2) (meetKids c m1 k1 m2 k2 (m1 &&& m2) #[])
      else .nil
    else if l2 < l1 then
      if prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 == p1
          && testBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) then
        if h : arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) < k1.size then
          meetU c (k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h) (.bin p2 l2 m2 k2)
        else .nil
      else .nil
    else
      if prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 == p2
          && testBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) then
        if h : arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) < k2.size then
          meetU c (.bin p1 l1 m1 k1) (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h)
        else .nil
      else .nil
termination_by s t => (sizeOf s + sizeOf t, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := Array.sizeOf_lt_of_mem (Array.getElem_mem h); omega)

/-- The intersected child at a shared slot `i`: recurse with `meetU` on the two children (the `nil`
fallbacks never fire for a slot actually present in both masks). -/
def meetChild (c : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32) (k2 : Array (PTree L)) (i : UInt32) :
    PTree L :=
  if h1 : arrayIndex m1 i < k1.size then
    if h2 : arrayIndex m2 i < k2.size then
      meetU c (k1[arrayIndex m1 i]'h1) (k2[arrayIndex m2 i]'h2)
    else .nil
  else .nil
termination_by (sizeOf k1 + sizeOf k2, 0)
decreasing_by
  all_goals simp_wf
  all_goals (have := Array.sizeOf_lt_of_mem (Array.getElem_mem h1)
             have := Array.sizeOf_lt_of_mem (Array.getElem_mem h2); omega)

/-- Fold over the shared mask `rem` (= `m1 &&& m2`), appending each slot's `meetChild` to `acc`
(lowest first); the result is compact under the shared mask, `nil` where the intersection is empty
(those are pruned later by `compactify`). -/
def meetKids (c : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32) (k2 : Array (PTree L))
    (rem : UInt32) (acc : Array (PTree L)) : Array (PTree L) :=
  if hrem : rem == 0 then acc
  else
    meetKids c m1 k1 m2 k2 (clearLowest rem) (acc.push (meetChild c m1 k1 m2 k2 (lowestSetIdx rem)))
termination_by (sizeOf k1 + sizeOf k2 + 1, rem.toNat)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have : (clearLowest rem).toNat < rem.toNat :=
         UInt32.lt_iff_toNat_lt.mp (clearLowest_lt rem (by simp_all)); omega)
end

/-- Intersection `a ∩ b`, resolving coinciding keys with `c`. -/
@[inline] def meet (c : V → V → V) (a b : PTree L) : PTree L := meetU c a b

----------------------------------------------------------------------------------------------------
-- Validation: `PTree` must agree with the verified `NatSet` (implementation-level cross-checks at
-- the `UInt32`/`Unit` set instance; proofs are added in later stages). The set-specialized helpers
-- below fix the trivial `Unit` combine/relation so the checks read like the original set ops.
----------------------------------------------------------------------------------------------------

private def ofSet (ks : List Nat) : PTree UInt32 := ks.foldl (fun s k => s.insert k ()) .nil
private def unionSet (a b : PTree UInt32) : PTree UInt32 := union (fun _ _ => ()) a b
private def meetSet (a b : PTree UInt32) : PTree UInt32 := meet (fun _ _ => ()) a b
private def subsetSet (a b : PTree UInt32) : Bool := subset (fun _ _ => true) a b

private def seqK : List Nat := List.range 1000
private def sparseK : List Nat :=
  [0, 31, 32, 1023, 1024, 42, 1000000, 999999999, 4294967296, 9223372036854775807, 7]

#guard (ofSet seqK).size == (NatSet.ofList seqK).size
#guard (ofSet seqK).size == 1000
#guard (ofSet sparseK).size == (NatSet.ofList sparseK).size
-- membership agrees for present keys
#guard sparseK.all fun k => (ofSet sparseK).contains k == (NatSet.ofList sparseK).contains k
-- …and for absent keys (incl. a near-miss of the 63-bit key)
#guard [1, 33, 1025, 5, 123456, 8, 12345, 9223372036854775806].all fun k =>
  (ofSet sparseK).contains k == (NatSet.ofList sparseK).contains k
-- idempotent re-insert
#guard (((empty : PTree UInt32).insert 42 ()).insert 42 ()).size == 1

private def evenK : List Nat := (List.range 400).map (2 * ·)
private def oddK : List Nat := (List.range 400).map (2 * · + 1)

-- union sizes agree with `NatSet.union` across dense/overlapping/sparse mixes
#guard (unionSet (ofSet evenK) (ofSet oddK)).size == (NatSet.ofList (evenK ++ oddK)).size
#guard (unionSet (ofSet sparseK) (ofSet (List.range 50))).size == (NatSet.ofList (sparseK ++ List.range 50)).size
#guard (unionSet (ofSet sparseK) (ofSet sparseK)).size == (ofSet sparseK).size       -- idempotent
#guard (unionSet (ofSet (List.range 500)) (ofSet ((List.range 500).map (· + 250)))).size == 750
#guard (unionSet (ofSet sparseK) (ofSet evenK)).size == (NatSet.ofList (sparseK ++ evenK)).size
-- membership after union agrees with NatSet
#guard (sparseK ++ List.range 50).all fun k =>
  (unionSet (ofSet sparseK) (ofSet (List.range 50))).contains k == true

-- subset agrees with `NatSet.subset` across dense/sparse/overlapping mixes (both directions)
private def subsetCorpus : List (List Nat) :=
  [[], [0], List.range 500, seqK, sparseK, evenK, oddK, sparseK ++ List.range 50,
   (List.range 300).map (· + 1)]
#guard subsetCorpus.all fun a => subsetCorpus.all fun b =>
  subsetSet (ofSet a) (ofSet b) == (NatSet.ofList a).subset (NatSet.ofList b)
-- explicit anchors: dense reflexive (the prototype's regression cell), proper ⊆, and a near-miss
#guard subsetSet (ofSet seqK) (ofSet seqK)
#guard subsetSet (ofSet (List.range 500)) (ofSet seqK)
#guard !(subsetSet (ofSet seqK) (ofSet (List.range 500)))
#guard !(subsetSet (ofSet sparseK) (ofSet (List.range 50)))

-- intersection agrees with `NatSet.inter` across dense/sparse/overlapping mixes
#guard subsetCorpus.all fun a => subsetCorpus.all fun b =>
  (meetSet (ofSet a) (ofSet b)).size == (NatSet.inter (NatSet.ofList a) (NatSet.ofList b)).size
-- membership after intersection = membership in both operands
#guard subsetCorpus.all fun a => subsetCorpus.all fun b =>
  (a ++ b).all fun k =>
    (meetSet (ofSet a) (ofSet b)).contains k == ((ofSet a).contains k && (ofSet b).contains k)
-- re-compression anchors: disjoint → empty; self/subset idempotence; bin/bin collapse to one or none
#guard (meetSet (ofSet evenK) (ofSet oddK)).size == 0                 -- disjoint → nil
#guard (meetSet (ofSet seqK) (ofSet seqK)).size == seqK.length        -- idempotent
#guard (meetSet (ofSet (List.range 500)) (ofSet seqK)).size == 500    -- ⊆ → the smaller
#guard (meetSet (ofSet sparseK) (ofSet sparseK)).size == (ofSet sparseK).size
#guard (meetSet (ofSet [0, 32]) (ofSet [0, 64])).size == 1            -- finalize lifts the lone survivor
#guard (meetSet (ofSet [0, 32]) (ofSet [0, 64])).contains 0
#guard (meetSet (ofSet [0, 32]) (ofSet [64, 96])).size == 0           -- finalize collapses to nil

----------------------------------------------------------------------------------------------------
-- Theorems
--
-- The denotational layer. Two views, tied by `contains_eq_isSome`:
--  * `get? : Nat → PTree L → Option V` is the value denotation (a map's semantics); the lattice
--    laws route through its `get?_*` seams.
--  * `contains : Nat → PTree L → Bool` is key-presence (a set's semantics, the `isSome` shadow);
--    well-formedness and routing are stated on it, since alignment is about which keys exist and
--    where they route, not their values.
-- `WF` captures the canonical shape the operations maintain. The `*_nil/_tip/_bin` lemmas are the
-- structural rewrites every membership proof opens with, mirroring `Tree`'s `get?_*` seams over the
-- height-erased Patricia shape.
----------------------------------------------------------------------------------------------------

/-- The empty collection contains nothing. -/
theorem contains_nil (k : Nat) : contains k (.nil : PTree L) = false := by rw [contains]

/-- Lookup in the empty collection is `none`. -/
theorem get?_nil (k : Nat) : get? k (.nil : PTree L) = none := by rw [get?]

/-- Membership on a `tip`: the prefix must match and the leaf must hold the bottom chunk. -/
theorem contains_tip (j pfx : Nat) (leaf : L) :
    contains j (.tip pfx leaf) = (j >>> 5 == pfx && LeafOps.contains leaf (chunk j 0)) := by
  rw [contains]

/-- Lookup on a `tip`: read the leaf at the bottom chunk when the prefix matches. -/
theorem get?_tip (j pfx : Nat) (leaf : L) :
    get? j (.tip pfx leaf) = (if j >>> 5 == pfx then LeafOps.get? leaf (chunk j 0) else none) := by
  rw [get?]

/-- Membership on a `bin` factors through `childAt`: route by the level's chunk, then recurse.
Holds unconditionally — an absent slot and an out-of-range index both read `nil`, which contains
nothing — so it is the structural rewrite every `bin` membership proof opens with. -/
theorem contains_bin (k pfx level : Nat) (mask : UInt32) (kids : Array (PTree L)) :
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

/-- Lookup on a `bin` factors through `childAt` (the `get?` analogue of `contains_bin`). -/
theorem get?_bin (k pfx level : Nat) (mask : UInt32) (kids : Array (PTree L)) :
    get? k (.bin pfx level mask kids)
      = (if testBit mask (chunk k level) then get? k (childAt mask kids (chunk k level)) else none) := by
  rw [get?]; simp only [childAt]
  by_cases hb : testBit mask (chunk k level) = true
  · rw [if_pos hb, if_pos hb]
    by_cases hidx : arrayIndex mask (chunk k level) < kids.size
    · rw [dif_pos hidx, Array.getElem?_eq_getElem hidx, Option.getD_some]
    · rw [dif_neg hidx, Array.getElem?_eq_none (Nat.le_of_not_lt hidx), Option.getD_none, get?_nil]
  · rw [if_neg hb, if_neg hb]

/-- `contains` is the `isSome` shadow of `get?`: the key-presence fast path matches the value
denotation. The bridge that lets the set recover its `contains`-membership laws from the generic
`get?` laws. -/
theorem contains_eq_isSome (k : Nat) (t : PTree L) : contains k t = (get? k t).isSome := by
  induction t using contains.induct (k := k) with
  | case1 => simp [contains_nil, get?_nil]
  | case2 pfx leaf =>
    rw [contains_tip, get?_tip]
    by_cases hp : (k >>> 5 == pfx) = true
    · rw [if_pos hp, hp, Bool.true_and, LeafOps.contains_eq_isSome]
    · simp only [Bool.not_eq_true] at hp
      simp [hp]
  | case3 pfx level mask kids hb hidx ih =>
    rw [contains_bin, get?_bin, if_pos hb, hb, Bool.true_and, childAt,
        Array.getElem?_eq_getElem hidx, Option.getD_some]
    exact ih
  | case4 pfx level mask kids hb hidx =>
    rw [contains_bin, get?_bin, if_pos hb, hb, Bool.true_and, childAt,
        Array.getElem?_eq_none (Nat.le_of_not_lt hidx), Option.getD_none]
    simp [contains_nil, get?_nil]
  | case5 pfx level mask kids hb =>
    simp only [Bool.not_eq_true] at hb
    rw [contains_bin, get?_bin, hb, Bool.false_and]
    simp

/-- Every key a subtree holds hangs under slot `c` at level `l` and shares prefix `p`. The routing
content of `WF`'s `bin` clause, named so the merge proofs (`join`/`insert`/`union`) can carry it. -/
def AlignedAt (l : Nat) (c : UInt32) (p : Nat) (t : PTree L) : Prop :=
  ∀ k, contains k t = true → chunk k l = c ∧ prefixAbove k l = p

/-- Well-formedness: the canonical-shape invariant `contains` relies on.
* a `tip` carries a non-empty leaf;
* a `bin pfx level mask kids` branches at `level ≥ 1`, stores its present children compactly
  (`kids.size = popCount mask`), is path-compression-minimal (`≥ 2` children), every child is WF
  and non-empty (`≠ nil`), and — the routing invariant (`AlignedAt`) — every key a present child
  holds agrees with the slot it hangs under and the branch prefix. -/
def WF : PTree L → Prop
  | .nil => True
  | .tip _ leaf => LeafOps.isEmpty leaf = false
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

/-- The empty collection is well-formed. -/
theorem WF_empty : WF (empty : PTree L) := by rw [empty, WF]; trivial

/-- A singleton is well-formed (one non-empty `tip`). -/
theorem WF_singleton (k : Nat) (v : V) : WF (singleton k v : PTree L) := by
  rw [singleton, WF]; exact LeafOps.insert_ne_empty _ _ _

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

/-- The leaf of a singleton holds exactly the inserted slot. -/
private theorem leaf_contains_singleton (i j : UInt32) (v : V) (hi : i < 32) (hj : j < 32) :
    LeafOps.contains (LeafOps.insert (LeafOps.empty : L) i v) j = (j == i) := by
  rw [LeafOps.contains_eq_isSome, LeafOps.get?_insert LeafOps.empty i j v hi hj]
  by_cases h : j = i
  · rw [if_pos h, h]; simp
  · rw [if_neg h, LeafOps.get?_empty, beq_eq_false_iff_ne.mpr h]; rfl

/-- Membership in a singleton is key equality — the `get?_singleton` seam for the set. -/
theorem contains_singleton (k j : Nat) (v : V) : contains k (singleton j v : PTree L) = true ↔ k = j := by
  rw [singleton, contains_tip,
      leaf_contains_singleton (chunk j 0) (chunk k 0) v (chunk_lt _ _) (chunk_lt _ _),
      Bool.and_eq_true, beq_iff_eq, beq_iff_eq, key_eq_iff k j]

/-! ### Non-emptiness

The canonical invariant `WF` forbids `nil` children (a `nil` child at a present slot would carry no
keys, so it could be dropped without changing membership — exactly what would break `ext`). These
structural facts let the merge/insert proofs discharge that clause: the operations never produce a
`nil`. -/

/-- A singleton is a `tip`, never empty. -/
theorem singleton_ne_nil (k : Nat) (v : V) : (singleton k v : PTree L) ≠ .nil := by
  simp [singleton]

/-- `insert` always yields a `tip` or a `bin`, never `nil`. -/
theorem insert_ne_nil (k : Nat) (v : V) (t : PTree L) : insert k v t ≠ .nil := by
  cases t <;> simp only [insert] <;> (repeat' split) <;> simp [join, singleton]

/-- Union with a non-empty operand is non-empty: every non-`nil` shape feeds a `tip`/`bin`/`join`
result. -/
theorem unionU_ne_nil_of_left (c : V → V → V) (a b : PTree L) (h : a ≠ .nil) :
    unionU c a b ≠ .nil := by
  cases a with
  | nil => exact absurd rfl h
  | tip p1 b1 => cases b <;> simp only [unionU] <;> (repeat' split) <;> simp [join]
  | bin p1 l1 m1 k1 => cases b <;> simp only [unionU] <;> (repeat' split) <;> simp [join]

end PTree
end NatCol
