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

end PTree
end NatCol
