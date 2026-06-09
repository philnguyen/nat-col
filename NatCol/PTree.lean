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

/-! ### The `join` seams

`join ka a kb b` builds a fresh 2-slot `bin` over two subtrees with divergent prefixes. The two
slots `ca = chunk ka l`, `cb = chunk kb l` are distinct, so membership splits cleanly. These are the
`get?_join` analogues for the prefix-divergent case of `insert`/`union`; both are stated on the
constructed `bin` and parametrized by the slot alignments, keeping the `branchLevel` arithmetic at
the call sites. They are leaf-agnostic (about which keys route where, not their values). -/

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
private theorem childAt_join_ca (ca cb : UInt32) (a b : PTree L)
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
private theorem childAt_join_cb (ca cb : UInt32) (a b : PTree L)
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

private theorem mem_pair {c x y : PTree L} (h : c ∈ (#[x, y] : Array (PTree L))) : c = x ∨ c = y := by
  simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at h
  exact h

/-- Membership in a `join` of two slot-aligned subtrees is membership in either. The `get?_join`
seam for a prefix-divergent insert/union: the two subtrees route to distinct slots, so no key can
sit in both. -/
theorem contains_join (j p l : Nat) (ca cb : UInt32) (a b : PTree L)
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
theorem WF_join (p l : Nat) (ca cb : UInt32) (a b : PTree L)
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

/-- A non-empty `tip`'s representative key carries the prefix `pfx` above the bottom chunk. The
representative slot `LeafOps.someSlot leaf` is `< 32`, so it stays inside the bottom chunk. -/
private theorem someKey_tip_shiftRight5 (pfx : Nat) (leaf : L) (hb : LeafOps.isEmpty leaf = false) :
    someKey (.tip pfx leaf) >>> 5 = pfx := by
  show ((pfx <<< 5) ||| (LeafOps.someSlot leaf).toNat) >>> 5 = pfx
  apply shiftLeft_lor_shiftRight
  have h := UInt32.lt_iff_toNat_lt.mp (LeafOps.someSlot_lt leaf hb)
  rw [show (32 : UInt32).toNat = 32 from by decide] at h
  exact h

/-- A `bin`'s representative key carries the branch prefix `pfx` above `level`. -/
private theorem someKey_bin_prefixAbove (pfx level : Nat) (mask : UInt32) (kids : Array (PTree L))
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
theorem aligned_tip (pfx : Nat) (leaf : L) (hb : LeafOps.isEmpty leaf = false) (l : Nat) (hl : 0 < l) :
    AlignedAt l (chunk (someKey (.tip pfx leaf)) l) (prefixAbove (someKey (.tip pfx leaf)) l)
      (.tip pfx leaf) := by
  intro k hk
  rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hk
  have hk5 : k >>> 5 = someKey (.tip pfx leaf) >>> 5 := by
    rw [someKey_tip_shiftRight5 pfx leaf hb]; exact hk.1
  exact ⟨chunk_eq_of_shiftRight_eq (shiftRight_mono_eq hk5 (by omega)),
         prefixAbove_eq_of_shiftRight_eq (shiftRight_mono_eq hk5 (by omega))⟩

/-- A well-formed `bin` is aligned at every level strictly above its own: all its keys share the
branch prefix `pfx`, hence agree above `level`. -/
theorem aligned_bin (pfx level : Nat) (mask : UInt32) (kids : Array (PTree L))
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
the shared prefix is well-defined) and the level is high enough to sit above an existing subtree.
Pure `Nat` arithmetic — leaf-independent. -/

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

/-- Membership in a singleton, as a `Bool` (the `decide`-free form the extensionality proofs use). -/
theorem contains_singleton_eq (j k : Nat) (v : V) : contains j (singleton k v : PTree L) = (j == k) := by
  rw [Bool.eq_iff_iff, contains_singleton, beq_iff_eq]

/-- Membership in a `join` of two slot-aligned subtrees, stated directly on `join` (unfolds the
branch arithmetic once so the call sites need only supply the alignments). -/
theorem contains_join_eq (j ka kb : Nat) (a b : PTree L) (hne : ka ≠ kb)
    (ha : AlignedAt (branchLevel ka kb) (chunk ka (branchLevel ka kb))
            (prefixAbove ka (branchLevel ka kb)) a)
    (hb : AlignedAt (branchLevel ka kb) (chunk kb (branchLevel ka kb))
            (prefixAbove ka (branchLevel ka kb)) b) :
    contains j (join ka a kb b) = (contains j a || contains j b) := by
  rw [join]
  exact contains_join j (prefixAbove ka (branchLevel ka kb)) (branchLevel ka kb)
    (chunk ka (branchLevel ka kb)) (chunk kb (branchLevel ka kb)) a b
    (chunk_lt _ _) (chunk_lt _ _) (chunk_branchLevel_ne ka kb hne) ha hb

/-! ### The `insert` seams

`contains_insert` — the `get?_insert` analogue at the key-presence level — characterizes membership
after an insert. The leaf-level `leaf_contains_insert` lifts `LeafOps.get?_insert` to `contains`,
replacing the monomorphic `testBit_setBit` reasoning. The three `childAt_*` array lemmas (leaf-
agnostic) describe how a present slot's child, a freshly-spliced slot, and the other slots read
after the compact-array update `insert` performs. -/

/-- Overwriting present slot `c`'s child: any other present slot reads through unchanged. -/
private theorem childAt_setIfInBounds (mask c cj : UInt32) (kids : Array (PTree L)) (nc : PTree L)
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
private theorem childAt_insertIdx_self (mask c : UInt32) (kids : Array (PTree L)) (nc : PTree L)
    (hsize : kids.size = popCount mask) :
    childAt (setBit mask c) (kids.insertIdx! (arrayIndex mask c) nc) c = nc := by
  unfold childAt
  have hle : arrayIndex mask c ≤ kids.size := by rw [hsize]; exact arrayIndex_le mask c
  rw [arrayIndex_setBit_self, show kids.insertIdx! (arrayIndex mask c) nc
        = kids.insertIdx (arrayIndex mask c) nc hle from dif_pos hle,
      Array.getElem?_insertIdx_self hle, Option.getD_some]

/-- Splicing a fresh slot `c` leaves every other present slot's child reachable (its compact index
shifts with the insertion but still names the same element). -/
private theorem childAt_insertIdx_of_ne (mask c cj : UInt32) (kids : Array (PTree L)) (nc : PTree L)
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

/-- The leaf-level `contains`-after-`insert` fact (the `isSome` shadow of `LeafOps.get?_insert`):
inserting slot `i` adds exactly that slot's membership. -/
private theorem leaf_contains_insert (leaf : L) (i j : UInt32) (v : V) (hi : i < 32) (hj : j < 32) :
    LeafOps.contains (LeafOps.insert leaf i v) j = ((i == j) || LeafOps.contains leaf j) := by
  rw [LeafOps.contains_eq_isSome, LeafOps.get?_insert leaf i j v hi hj]
  by_cases h : j = i
  · rw [if_pos h, h]; simp
  · rw [if_neg h, beq_eq_false_iff_ne.mpr (Ne.symm h), Bool.false_or, LeafOps.contains_eq_isSome]

set_option linter.unusedVariables false in
/-- `get?_insert` for the set: membership after `insert k` adds exactly `k`. The key-presence point
of contact between the lattice/order proofs and `insert`'s structural code. -/
theorem contains_insert (k j : Nat) (v : V) :
    ∀ (t : PTree L), WF t → contains j (insert k v t) = ((j == k) || contains j t) := by
  intro t
  induction t using insert.induct (k := k) with
  | case1 =>
    intro _
    rw [insert, contains_singleton_eq, contains_nil, Bool.or_false]
  | case2 pfx leaf hmatch =>
    intro _
    rw [insert, if_pos hmatch, contains_tip, contains_tip,
        leaf_contains_insert leaf (chunk k 0) (chunk j 0) v (chunk_lt _ _) (chunk_lt _ _)]
    have hk5 : k >>> 5 = pfx := by simpa using hmatch
    have hdec : (j == k) = ((j >>> 5 == pfx) && (chunk k 0 == chunk j 0)) := by
      rw [Bool.eq_iff_iff, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq, key_eq_iff j k, hk5]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
    rw [hdec]
    cases (j >>> 5 == pfx) <;> cases LeafOps.contains leaf (chunk j 0) <;>
      cases (chunk k 0 == chunk j 0) <;> rfl
  | case3 pfx leaf hmatch =>
    intro hwf
    have hleaf : LeafOps.isEmpty leaf = false := by rw [WF] at hwf; exact hwf
    have hsk : someKey (.tip pfx leaf) >>> 5 = pfx := someKey_tip_shiftRight5 pfx leaf hleaf
    have hkne5 : k >>> 5 ≠ someKey (.tip pfx leaf) >>> 5 := by
      rw [hsk]; intro h; exact hmatch (by rw [h]; exact beq_self_eq_true pfx)
    have hkne : k ≠ someKey (.tip pfx leaf) := fun h => hkne5 (by rw [h])
    rw [insert, if_neg hmatch,
        show ((pfx <<< 5) ||| (LeafOps.someSlot leaf).toNat) = someKey (.tip pfx leaf) from rfl,
        contains_join_eq j k (someKey (.tip pfx leaf)) (singleton k v) (.tip pfx leaf) hkne ?ha ?hb,
        contains_singleton_eq]
    case ha =>
      intro k' hk'; rw [show k' = k from (contains_singleton k' k v).mp hk']; exact ⟨rfl, rfl⟩
    case hb =>
      rw [prefixAbove_branchLevel_eq k (someKey (.tip pfx leaf))]
      exact aligned_tip pfx leaf hleaf _ (branchLevel_pos k _ hkne5)
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
          childAt_insertIdx_self mask (chunk k level) kids (singleton k v) hsize,
          contains_singleton_eq, htbf, Bool.false_and, Bool.or_false]
    · have hjkf : (j == k) = false := beq_eq_false_iff_ne.mpr (fun he => hcjc (by rw [he]))
      rw [testBit_setBit mask (chunk k level) (chunk j level) hclt hcjlt,
          beq_eq_false_iff_ne.mpr (Ne.symm hcjc), Bool.or_false, hjkf, Bool.false_or]
      by_cases htcj : testBit mask (chunk j level) = true
      · rw [childAt_insertIdx_of_ne mask (chunk k level) (chunk j level) kids (singleton k v)
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
        contains_join_eq j k (someKey (.bin pfx level mask kids)) (singleton k v)
          (.bin pfx level mask kids) hkne ?ha ?hb, contains_singleton_eq]
    case ha =>
      intro k' hk'; rw [show k' = k from (contains_singleton k' k v).mp hk']; exact ⟨rfl, rfl⟩
    case hb =>
      rw [prefixAbove_branchLevel_eq k (someKey (.bin pfx level mask kids))]
      exact aligned_bin pfx level mask kids hwf _ (lt_branchLevel k _ level hkne5)

set_option linter.unusedVariables false in
/-- `insert` preserves the canonical shape. The routing invariant for a modified or freshly-spliced
slot is discharged by `contains_insert`: the new child holds exactly the old keys plus `k`, all of
which align under that slot's chunk and the branch prefix. -/
theorem WF_insert (k : Nat) (v : V) : ∀ (t : PTree L), WF t → WF (insert k v t) := by
  intro t
  induction t using insert.induct (k := k) with
  | case1 => intro _; rw [insert]; exact WF_singleton k v
  | case2 pfx leaf hmatch =>
    intro _; rw [insert, if_pos hmatch, WF]; exact LeafOps.insert_ne_empty leaf (chunk k 0) v
  | case3 pfx leaf hmatch =>
    intro hwf
    have hleaf : LeafOps.isEmpty leaf = false := by rw [WF] at hwf; exact hwf
    have hsk : someKey (.tip pfx leaf) >>> 5 = pfx := someKey_tip_shiftRight5 pfx leaf hleaf
    have hkne5 : k >>> 5 ≠ someKey (.tip pfx leaf) >>> 5 := by
      rw [hsk]; intro h; exact hmatch (by rw [h]; exact beq_self_eq_true pfx)
    have hkne : k ≠ someKey (.tip pfx leaf) := fun h => hkne5 (by rw [h])
    have hl0 : 0 < branchLevel k (someKey (.tip pfx leaf)) := branchLevel_pos k _ hkne5
    rw [insert, if_neg hmatch,
        show ((pfx <<< 5) ||| (LeafOps.someSlot leaf).toNat) = someKey (.tip pfx leaf) from rfl, join]
    refine WF_join _ _ _ _ (singleton k v) (.tip pfx leaf) hl0 (chunk_lt _ _) (chunk_lt _ _)
      (chunk_branchLevel_ne k _ hkne) ?ha ?hb (WF_singleton k v) hwf (singleton_ne_nil k v) (by simp)
    case ha =>
      intro k' hk'; rw [show k' = k from (contains_singleton k' k v).mp hk']; exact ⟨rfl, rfl⟩
    case hb =>
      rw [prefixAbove_branchLevel_eq k (someKey (.tip pfx leaf))]
      exact aligned_tip pfx leaf hleaf _ hl0
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
        (insert k v kids[arrayIndex mask (chunk k level)]) := by
      intro j hj
      rw [contains_insert k j v _ hwfchild, Bool.or_eq_true, beq_iff_eq] at hj
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
      · rw [heq]; exact insert_ne_nil k v _
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
    have hidx : kids.insertIdx! (arrayIndex mask (chunk k level)) (singleton k v)
        = kids.insertIdx (arrayIndex mask (chunk k level)) (singleton k v) hle := dif_pos hle
    rw [insert, if_pos hpfx, if_neg htb, WF]
    refine ⟨hlvl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hidx, Array.size_insertIdx, hsize, hpcnew]
    · rw [hpcnew]; omega
    · intro c' hc'
      rw [hidx] at hc'
      rcases Array.mem_insertIdx.mp hc' with heq | hmem
      · rw [heq]; exact WF_singleton k v
      · exact hkidswf c' hmem
    · intro c' hc'
      rw [hidx] at hc'
      rcases Array.mem_insertIdx.mp hc' with heq | hmem
      · rw [heq]; exact singleton_ne_nil k v
      · exact hnonnil c' hmem
    · intro c' hc'lt htc'
      by_cases hc'c : c' = chunk k level
      · subst hc'c
        rw [childAt_insertIdx_self mask (chunk k level) kids (singleton k v) hsize]
        intro j hj
        rw [contains_singleton] at hj; subst hj
        exact ⟨rfl, hpfxeq⟩
      · have htcm : testBit mask c' = true := by
          rw [testBit_setBit mask (chunk k level) c' hclt hc'lt,
              beq_eq_false_iff_ne.mpr (Ne.symm hc'c), Bool.or_false] at htc'
          exact htc'
        rw [childAt_insertIdx_of_ne mask (chunk k level) c' kids (singleton k v)
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
    refine WF_join _ _ _ _ (singleton k v) (.bin pfx level mask kids) hl0 (chunk_lt _ _)
      (chunk_lt _ _) (chunk_branchLevel_ne k _ hkne) ?ha ?hb (WF_singleton k v) hwf
      (singleton_ne_nil k v) (by simp)
    case ha =>
      intro k' hk'; rw [show k' = k from (contains_singleton k' k v).mp hk']; exact ⟨rfl, rfl⟩
    case hb =>
      rw [prefixAbove_branchLevel_eq k (someKey (.bin pfx level mask kids))]
      exact aligned_bin pfx level mask kids hwf _ (lt_branchLevel k _ level hkne5)

/-- Building from a list keeps the trie canonical (repeated `insert` from the empty trie). -/
theorem WF_ofList (kvs : List (Nat × V)) : WF (ofList kvs : PTree L) := by
  unfold ofList
  suffices h : ∀ (l : List (Nat × V)) (s : PTree L), WF s →
      WF (l.foldl (fun s kv => s.insert kv.1 kv.2) s) by
    exact h kvs .nil WF_empty
  intro l
  induction l with
  | nil => intro s hs; exact hs
  | cons a t ih => intro s hs; exact ih (s.insert a.1 a.2) (WF_insert a.1 a.2 s hs)

/-! ### Leaf-level `contains` bridges through `join`/`meet`

The `isSome` shadows of `LeafOps.get?_join`/`get?_meet`: at the leaf, a `join` holds the union of
two leaves' slots and a `meet` their intersection. These are the seams the key-presence union/meet
proofs cross at a `tip`, where the two leaves combine (the analogue of the monomorphic `testBit_or`/
`testBit_and`). -/

/-- A `join`ed leaf holds slot `i` iff either operand does. -/
private theorem leaf_contains_join (cf : V → V → V) (a b : L) (i : UInt32) (hi : i < 32) :
    LeafOps.contains (LeafOps.join cf a b) i = (LeafOps.contains a i || LeafOps.contains b i) := by
  rw [LeafOps.contains_eq_isSome, LeafOps.get?_join cf a b i hi, LeafOps.contains_eq_isSome,
      LeafOps.contains_eq_isSome]
  cases LeafOps.get? a i <;> cases LeafOps.get? b i <;> rfl

/-- A `meet`ed leaf holds slot `i` iff both operands do. -/
private theorem leaf_contains_meet (cf : V → V → V) (a b : L) (i : UInt32) (hi : i < 32) :
    LeafOps.contains (LeafOps.meet cf a b) i = (LeafOps.contains a i && LeafOps.contains b i) := by
  rw [LeafOps.contains_eq_isSome, LeafOps.get?_meet cf a b i hi, LeafOps.contains_eq_isSome,
      LeafOps.contains_eq_isSome]
  cases LeafOps.get? a i <;> cases LeafOps.get? b i <;> rfl

/-! ### The `union` present-slot fold

The aligned-`bin` case of `unionU` rebuilds the child array with `mergeKids`, a present-slot fold
over the combined mask `m1 ||| m2` that appends one `mergeChild` per set bit (lowest first). These
structural facts characterize that array independently of `mergeChild`'s contents: its size, and
that reading slot `c` back (via `childAt` on the merged mask) recovers `mergeChild … c`. The fold
shape is leaf-agnostic — the combine `cf` is just carried through. -/

/-- The fold's running invariant: starting from `acc`, processing `rem`'s set bits lowest-first
appends one child per bit. Stated by strong induction on `rem.toNat` (each step clears the lowest
bit): the result keeps `acc` as a prefix, grows by `popCount rem`, and lands each remaining set
bit's `mergeChild` at its compact index past `acc`. -/
private theorem mergeKids_spec (cf : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) :
    ∀ (n : Nat) (rem : UInt32), rem.toNat = n → ∀ (acc : Array (PTree L)),
      (mergeKids cf m1 k1 m2 k2 rem acc).size = acc.size + popCount rem
      ∧ (∀ i, i < acc.size → (mergeKids cf m1 k1 m2 k2 rem acc)[i]? = acc[i]?)
      ∧ (∀ c, c < 32 → testBit rem c = true →
           (mergeKids cf m1 k1 m2 k2 rem acc)[acc.size + arrayIndex rem c]?
             = some (mergeChild cf m1 k1 m2 k2 c)) := by
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
      have hstep : mergeKids cf m1 k1 m2 k2 rem acc
          = mergeKids cf m1 k1 m2 k2 (clearLowest rem)
              (acc.push (mergeChild cf m1 k1 m2 k2 (lowestSetIdx rem))) := by
        rw [mergeKids, dif_neg h0]
      have hlt : (clearLowest rem).toNat < n := by
        rw [← hrem]; exact UInt32.lt_iff_toNat_lt.mp (clearLowest_lt rem hrem0)
      obtain ⟨ihsize, ihpref, ihthird⟩ :=
        IH (clearLowest rem).toNat hlt (clearLowest rem) rfl
          (acc.push (mergeChild cf m1 k1 m2 k2 (lowestSetIdx rem)))
      have hpc : popCount (clearLowest rem) + 1 = popCount rem := popCount_clearLowest rem hrem0
      have haccsz : (acc.push (mergeChild cf m1 k1 m2 k2 (lowestSetIdx rem))).size = acc.size + 1 :=
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
theorem childAt_mergeKids (cf : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) (c : UInt32) (hc : c < 32) (htb : testBit (m1 ||| m2) c = true) :
    childAt (m1 ||| m2) (mergeKids cf m1 k1 m2 k2 (m1 ||| m2) #[]) c = mergeChild cf m1 k1 m2 k2 c := by
  obtain ⟨_, _, hthird⟩ := mergeKids_spec cf m1 k1 m2 k2 (m1 ||| m2).toNat (m1 ||| m2) rfl #[]
  have hc' := hthird c hc htb
  unfold childAt
  rw [show (#[] : Array (PTree L)).size = 0 from rfl, Nat.zero_add] at hc'
  rw [hc', Option.getD_some]

/-- The rebuilt child array has exactly one slot per present bit of the merged mask — the compact
size invariant the merged `bin` needs to stay well-formed. -/
theorem size_mergeKids (cf : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) :
    (mergeKids cf m1 k1 m2 k2 (m1 ||| m2) #[]).size = popCount (m1 ||| m2) := by
  obtain ⟨hsize, _, _⟩ := mergeKids_spec cf m1 k1 m2 k2 (m1 ||| m2).toNat (m1 ||| m2) rfl #[]
  rw [hsize, show (#[] : Array (PTree L)).size = 0 from rfl, Nat.zero_add]

/-- Every child the fold produces comes from either the seed `acc` or some present slot's
`mergeChild`. The membership companion to `mergeKids_spec`; feeds the non-`nil` clause of
`WF_unionU`'s aligned-`bin` case. -/
private theorem mergeKids_mem (cf : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) :
    ∀ (n : Nat) (rem : UInt32), rem.toNat = n → ∀ (acc : Array (PTree L)) (x : PTree L),
      x ∈ mergeKids cf m1 k1 m2 k2 rem acc →
        x ∈ acc ∨ ∃ c, testBit rem c = true ∧ x = mergeChild cf m1 k1 m2 k2 c := by
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
          (acc.push (mergeChild cf m1 k1 m2 k2 (lowestSetIdx rem))) x hx with hacc | hex
      · rcases Array.mem_push.mp hacc with hin | heq
        · exact Or.inl hin
        · exact Or.inr ⟨lowestSetIdx rem, testBit_lowestSetIdx rem hrem0, heq⟩
      · obtain ⟨c, htb, hxc⟩ := hex
        exact Or.inr ⟨c, testBit_of_clearLowest rem c htb, hxc⟩

/-- A `bin`'s children, well-formed, non-`nil`, and compactly stored — the part of `WF` the per-slot
union reasoning (`mergeChild`/`mergeKids`) consumes, abstracted so the motives can carry it. -/
def KidsWF (mask : UInt32) (kids : Array (PTree L)) : Prop :=
  kids.size = popCount mask ∧ (∀ c ∈ kids, WF c) ∧ (∀ c ∈ kids, c ≠ .nil)

/-- A key routing to a slot other than the one a subtree is aligned under is not in that subtree. -/
theorem contains_false_of_aligned {j : Nat} (l : Nat) (c : UInt32) (p : Nat) (t : PTree L)
    (h : AlignedAt l c p t) (hj : chunk j l ≠ c) : contains j t = false := by
  cases hcon : contains j t with
  | true => exact absurd (h j hcon).1 hj
  | false => rfl

/-- Descend case shared by all four `unionU` quadrants: when an operand `op` routes to a *present*
slot `c` of a well-formed `bin`, the result overwrites that slot's child with `unionU child op`.
Membership splits on whether `j` routes to `c`; off-slot keys of `op` are killed by its alignment. -/
private theorem contains_descend (cf : V → V → V) (j : Nat) (op : PTree L) (bp bl : Nat) (bm : UInt32)
    (bk : Array (PTree L)) (c : UInt32) (hc : c < 32) (hbin : WF (.bin bp bl bm bk))
    (halign : AlignedAt bl c bp op) (htb : testBit bm c = true) (hidx : arrayIndex bm c < bk.size)
    (IH : contains j (unionU cf (bk[arrayIndex bm c]'hidx) op)
            = (contains j (bk[arrayIndex bm c]'hidx) || contains j op)) :
    contains j (.bin bp bl bm (bk.setIfInBounds (arrayIndex bm c) (unionU cf (bk[arrayIndex bm c]'hidx) op)))
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
slot `c` of a well-formed `bin`, the result inserts `op` whole at the freshly-set slot. Leaf-
agnostic — no value combines, `op` is carried over wholesale. -/
private theorem contains_splice (j : Nat) (op : PTree L) (bp bl : Nat) (bm : UInt32)
    (bk : Array (PTree L)) (c : UInt32) (hc : c < 32) (hbin : WF (.bin bp bl bm bk))
    (halign : AlignedAt bl c bp op) (htb : testBit bm c = false) :
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

set_option maxHeartbeats 400000 in
/-- `get?_join` for the set at key-presence level: a key is in `unionU cf a b` iff in either
operand. The 31-case companion to `unionU`'s four quadrants × per-slot `mergeChild` fold; the
combine `cf` only touches values at a `tip`, so membership is combine-independent. The generic
`LeafOps` instance roughly triples the elaboration cost over the monomorphic original, so the
heartbeat budget is raised. -/
theorem contains_unionU (cf : V → V → V) (j : Nat) : ∀ (a b : PTree L), WF a → WF b →
    contains j (unionU cf a b) = (contains j a || contains j b) := by
  intro a b
  -- `unionU.induct` is generic over the `LeafOps` instance; left to `induction using` the instance
  -- becomes a stray alternative whose dangling metavar poisons every `KidsWF`/`contains` in the
  -- IHs. Applying the eliminator with `L`/`V`/instance/`c` already pinned (`@unionU.induct L V
  -- inferInstance cf`) keeps the motives concrete.
  induction a, b using (@unionU.induct L V inferInstance cf)
    (motive2 := fun m1 k1 m2 k2 rem _ =>
      KidsWF m1 k1 → KidsWF m2 k2 →
      (∀ c, c < 32 → testBit rem c = true → testBit (m1 ||| m2) c = true) →
      ∀ c, c < 32 → testBit rem c = true →
        contains j (mergeChild cf m1 k1 m2 k2 c)
          = ((testBit m1 c && contains j (childAt m1 k1 c))
              || (testBit m2 c && contains j (childAt m2 k2 c))))
    (motive3 := fun m1 k1 m2 k2 i =>
      KidsWF m1 k1 → KidsWF m2 k2 → i < 32 → (testBit m1 i || testBit m2 i) = true →
        contains j (mergeChild cf m1 k1 m2 k2 i)
          = ((testBit m1 i && contains j (childAt m1 k1 i))
              || (testBit m2 i && contains j (childAt m2 k2 i)))) with
  | case1 t => intro _ _; rw [unionU, contains_nil, Bool.false_or]
  | case2 s hs => intro _ _; rw [unionU, contains_nil, Bool.or_false]; exact hs
  | case3 p1 b1 p2 b2 heq =>
    intro _ _
    have hp : p1 = p2 := by simpa using heq
    rw [unionU, if_pos heq, contains_tip, contains_tip, contains_tip, ← hp,
        leaf_contains_join cf b1 b2 (chunk j 0) (chunk_lt _ _), Bool.and_or_distrib_left]
  | case4 p1 b1 p2 b2 hne =>
    intro hwf1 hwf2
    have hb1 : LeafOps.isEmpty b1 = false := by rw [WF] at hwf1; exact hwf1
    have hb2 : LeafOps.isEmpty b2 = false := by rw [WF] at hwf2; exact hwf2
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
    have hb1 : LeafOps.isEmpty b1 = false := by rw [WF] at hwf1; exact hwf1
    have hbl0 : 0 < bl := by rw [WF] at hwf2; exact hwf2.1
    have hwfchild := by rw [WF] at hwf2; exact hwf2.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.tip p1 b1)) bl = bp := by simpa using hpfx
    have halign : AlignedAt bl (chunk (someKey (.tip p1 b1)) bl) bp (.tip p1 b1) :=
      by rw [← hpfxeq]; exact aligned_tip p1 b1 hb1 bl hbl0
    rw [unionU, if_pos hpfx, if_pos htb, dif_pos h]
    exact contains_descend cf j (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl)
      (chunk_lt _ _) hwf2 halign htb h (IH hwfchild hwf1)
  | case6 p1 b1 bp bl bm bk hpfx htb hnh =>
    intro _ hwf2
    have hsize : bk.size = popCount bm := by rw [WF] at hwf2; exact hwf2.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt bm _ htb) hnh
  | case7 p1 b1 bp bl bm bk hpfx hntb =>
    intro hwf1 hwf2
    have hb1 : LeafOps.isEmpty b1 = false := by rw [WF] at hwf1; exact hwf1
    have hbl0 : 0 < bl := by rw [WF] at hwf2; exact hwf2.1
    have hpfxeq : prefixAbove (someKey (.tip p1 b1)) bl = bp := by simpa using hpfx
    have halign : AlignedAt bl (chunk (someKey (.tip p1 b1)) bl) bp (.tip p1 b1) :=
      by rw [← hpfxeq]; exact aligned_tip p1 b1 hb1 bl hbl0
    have htbf : testBit bm (chunk (someKey (.tip p1 b1)) bl) = false := by simpa using hntb
    rw [unionU, if_pos hpfx, if_neg hntb]
    exact contains_splice j (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl)
      (chunk_lt _ _) hwf2 halign htbf
  | case8 p1 b1 bp bl bm bk hnpfx =>
    intro hwf1 hwf2
    have hb1 : LeafOps.isEmpty b1 = false := by rw [WF] at hwf1; exact hwf1
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
    have hb2 : LeafOps.isEmpty b2 = false := by rw [WF] at hwftip; exact hwftip
    have hbl0 : 0 < bl := by rw [WF] at hwfbin; exact hwfbin.1
    have hwfchild := by rw [WF] at hwfbin; exact hwfbin.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.tip p2 b2)) bl = bp := by simpa using hpfx
    have halign : AlignedAt bl (chunk (someKey (.tip p2 b2)) bl) bp (.tip p2 b2) :=
      by rw [← hpfxeq]; exact aligned_tip p2 b2 hb2 bl hbl0
    rw [unionU, if_pos hpfx, if_pos htb, dif_pos h,
        contains_descend cf j (.tip p2 b2) bp bl bm bk (chunk (someKey (.tip p2 b2)) bl)
          (chunk_lt _ _) hwfbin halign htb h (IH hwfchild hwftip)]
    exact Bool.or_comm _ _
  | case10 bp bl bm bk p2 b2 hpfx htb hnh =>
    intro hwfbin _
    have hsize : bk.size = popCount bm := by rw [WF] at hwfbin; exact hwfbin.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt bm _ htb) hnh
  | case11 bp bl bm bk p2 b2 hpfx hntb =>
    intro hwfbin hwftip
    have hb2 : LeafOps.isEmpty b2 = false := by rw [WF] at hwftip; exact hwftip
    have hbl0 : 0 < bl := by rw [WF] at hwfbin; exact hwfbin.1
    have hpfxeq : prefixAbove (someKey (.tip p2 b2)) bl = bp := by simpa using hpfx
    have halign : AlignedAt bl (chunk (someKey (.tip p2 b2)) bl) bp (.tip p2 b2) :=
      by rw [← hpfxeq]; exact aligned_tip p2 b2 hb2 bl hbl0
    have htbf : testBit bm (chunk (someKey (.tip p2 b2)) bl) = false := by simpa using hntb
    rw [unionU, if_pos hpfx, if_neg hntb,
        contains_splice j (.tip p2 b2) bp bl bm bk (chunk (someKey (.tip p2 b2)) bl)
          (chunk_lt _ _) hwfbin halign htbf]
    exact Bool.or_comm _ _
  | case12 bp bl bm bk p2 b2 hnpfx =>
    intro hwfbin hwftip
    have hb2 : LeafOps.isEmpty b2 = false := by rw [WF] at hwftip; exact hwftip
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
    · rw [hM, Bool.true_and, childAt_mergeKids cf m1 k1 m2 k2 (chunk j l1) (chunk_lt j l1) hM,
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
    have hwfchild := by rw [WF] at hwf1; exact hwf1.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 = p1 := by simpa using hpfx
    have halign : AlignedAt l1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) p1 (.bin p2 l2 m2 k2) :=
      by rw [← hpfxeq]; exact aligned_bin p2 l2 m2 k2 hwf2 l1 hlt
    rw [unionU, if_neg hne, if_neg hlne, if_pos hlt, if_pos hpfx, if_pos htb, dif_pos h,
        contains_descend cf j (.bin p2 l2 m2 k2) p1 l1 m1 k1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)
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
      by rw [← hpfxeq]; exact aligned_bin p2 l2 m2 k2 hwf2 l1 hlt
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
    have hwfchild := by rw [WF] at hwf2; exact hwf2.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 = p2 := by simpa using hpfx
    have halign : AlignedAt l2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) p2 (.bin p1 l1 m1 k1) :=
      by rw [← hpfxeq]; exact aligned_bin p1 l1 m1 k1 hwf1 l2 hl12
    rw [unionU, if_neg hne, if_neg hlne, if_neg hnlt, if_pos hpfx, if_pos htb, dif_pos h]
    exact contains_descend cf j (.bin p1 l1 m1 k1) p2 l2 m2 k2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)
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
      by rw [← hpfxeq]; exact aligned_bin p1 l1 m1 k1 hwf1 l2 hl12
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
    have hwf1 := hkw1.2.1 _ (Array.getElem_mem h1)
    have hwf2 := hkw2.2.1 _ (Array.getElem_mem h2)
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
theorem contains_union (cf : V → V → V) (j : Nat) (a b : PTree L) (hwa : WF a) (hwb : WF b) :
    contains j (union cf a b) = (contains j a || contains j b) := by
  rw [union]; exact contains_unionU cf j a b hwa hwb

/-- Membership in a merged slot is membership in either operand's slot child — the per-slot form of
`contains_union`, now standalone (the `unionU` recursion it rests on is closed). Drives the routing
clause of `WF_union`: a merged child's keys come from one operand's child, so they stay aligned. -/
theorem contains_mergeChild (cf : V → V → V) (j : Nat) (m1 : UInt32) (k1 : Array (PTree L))
    (m2 : UInt32) (k2 : Array (PTree L)) (i : UInt32) (hkw1 : KidsWF m1 k1) (hkw2 : KidsWF m2 k2)
    (hpre : (testBit m1 i || testBit m2 i) = true) :
    contains j (mergeChild cf m1 k1 m2 k2 i)
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
          contains_unionU cf j _ _ (hkw1.2.1 _ (Array.getElem_mem h1)) (hkw2.2.1 _ (Array.getElem_mem h2)),
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
theorem mergeChild_ne_nil (cf : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) (i : UInt32) (hkw1 : KidsWF m1 k1) (hkw2 : KidsWF m2 k2)
    (hpre : (testBit m1 i || testBit m2 i) = true) :
    mergeChild cf m1 k1 m2 k2 i ≠ .nil := by
  rw [mergeChild]
  by_cases ht1 : testBit m1 i = true
  · have h1 : arrayIndex m1 i < k1.size := by rw [hkw1.1]; exact arrayIndex_lt m1 i ht1
    by_cases ht2 : testBit m2 i = true
    · have h2 : arrayIndex m2 i < k2.size := by rw [hkw2.1]; exact arrayIndex_lt m2 i ht2
      rw [if_pos ht1, if_pos ht2, dif_pos h1, dif_pos h2]
      exact unionU_ne_nil_of_left cf _ _ (hkw1.2.2 _ (Array.getElem_mem h1))
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
private theorem WF_descend (cf : V → V → V) (op : PTree L) (bp bl : Nat) (bm : UInt32)
    (bk : Array (PTree L)) (c : UInt32) (hc : c < 32) (hbin : WF (.bin bp bl bm bk))
    (halign : AlignedAt bl c bp op) (hwop : WF op) (htb : testBit bm c = true)
    (hidx : arrayIndex bm c < bk.size) (hwu : WF (unionU cf (bk[arrayIndex bm c]'hidx) op)) :
    WF (.bin bp bl bm (bk.setIfInBounds (arrayIndex bm c) (unionU cf (bk[arrayIndex bm c]'hidx) op))) := by
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
    · rw [heq]; exact unionU_ne_nil_of_left cf _ op (hnonnil _ (Array.getElem_mem hidx))
  · intro c'' hc''lt htc''
    by_cases hc''c : c'' = c
    · rw [hc''c, childAt_setIfInBounds bm c c bk _ hc hc htb htb hsize, if_pos rfl]
      intro k hk
      rw [contains_unionU cf k _ op (hkidswf _ (Array.getElem_mem hidx)) hwop, Bool.or_eq_true] at hk
      rcases hk with hkc | hko
      · have := hrout c hc htb; rw [hcAc] at this; exact this k hkc
      · exact halign k hko
    · rw [childAt_setIfInBounds bm c c'' bk _ hc hc''lt htb htc'' hsize, if_neg hc''c]
      exact hrout c'' hc''lt htc''

/-- `WF` splice case: inserting an aligned, well-formed operand `op` whole at an absent slot keeps
the `bin` canonical (one more child, mask gains its bit, the new slot's keys align by `op`). Leaf-
agnostic — `op` is carried over wholesale. -/
private theorem WF_splice (op : PTree L) (bp bl : Nat) (bm : UInt32) (bk : Array (PTree L))
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

end PTree
end NatCol
