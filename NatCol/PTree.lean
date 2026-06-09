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
              (unionU c (.tip p1 b1) (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h)))
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
              (unionU c (.bin p1 l1 m1 k1) (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h)))
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

/-- The op-first mirror of `contains_descend`: when the *left* operand `op` is routed into the right
operand's `bin` (`unionU cf op child`), so the combine fires `cf op-value child-value`. Membership
is identical to `contains_descend` (`||` is symmetric); the op-first union order is what keeps the
map value seam `optVjoin cf (get? a) (get? b)` faithful across taller-right descents. -/
private theorem contains_descend_left (cf : V → V → V) (j : Nat) (op : PTree L) (bp bl : Nat)
    (bm : UInt32) (bk : Array (PTree L)) (c : UInt32) (hc : c < 32) (hbin : WF (.bin bp bl bm bk))
    (halign : AlignedAt bl c bp op) (htb : testBit bm c = true) (hidx : arrayIndex bm c < bk.size)
    (IH : contains j (unionU cf op (bk[arrayIndex bm c]'hidx))
            = (contains j op || contains j (bk[arrayIndex bm c]'hidx))) :
    contains j (.bin bp bl bm (bk.setIfInBounds (arrayIndex bm c) (unionU cf op (bk[arrayIndex bm c]'hidx))))
      = (contains j op || contains j (.bin bp bl bm bk)) := by
  have hsize : bk.size = popCount bm := by rw [WF] at hbin; exact hbin.2.1
  have hcAc : childAt bm bk c = bk[arrayIndex bm c]'hidx := by
    unfold childAt; rw [Array.getElem?_eq_getElem hidx, Option.getD_some]
  rw [contains_bin, contains_bin]
  by_cases hcj : chunk j bl = c
  · rw [hcj, childAt_setIfInBounds bm c c bk _ hc hc htb htb hsize, if_pos rfl, IH, htb,
        Bool.true_and, hcAc, Bool.true_and]
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
    exact contains_descend_left cf j (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl)
      (chunk_lt _ _) hwf2 halign htb h (IH hwf1 hwfchild)
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
    exact contains_descend_left cf j (.bin p1 l1 m1 k1) p2 l2 m2 k2
      (chunk (someKey (.bin p1 l1 m1 k1)) l2) (chunk_lt _ _) hwf2 halign htb h (IH hwf1 hwfchild)
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

/-- The op-first mirror of `WF_descend` (`unionU cf op child`). `op` is the left operand routed into
the right's `bin`, so it must be non-`nil` (the left-`nil` quadrant is handled separately). -/
private theorem WF_descend_left (cf : V → V → V) (op : PTree L) (bp bl : Nat) (bm : UInt32)
    (bk : Array (PTree L)) (c : UInt32) (hc : c < 32) (hbin : WF (.bin bp bl bm bk))
    (halign : AlignedAt bl c bp op) (hwop : WF op) (hopne : op ≠ .nil) (htb : testBit bm c = true)
    (hidx : arrayIndex bm c < bk.size) (hwu : WF (unionU cf op (bk[arrayIndex bm c]'hidx))) :
    WF (.bin bp bl bm (bk.setIfInBounds (arrayIndex bm c) (unionU cf op (bk[arrayIndex bm c]'hidx)))) := by
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
    · rw [heq]; exact unionU_ne_nil_of_left cf op _ hopne
  · intro c'' hc''lt htc''
    by_cases hc''c : c'' = c
    · rw [hc''c, childAt_setIfInBounds bm c c bk _ hc hc htb htb hsize, if_pos rfl]
      intro k hk
      rw [contains_unionU cf k op _ hwop (hkidswf _ (Array.getElem_mem hidx)), Bool.or_eq_true] at hk
      rcases hk with hko | hkc
      · exact halign k hko
      · have := hrout c hc htb; rw [hcAc] at this; exact this k hkc
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

set_option maxHeartbeats 400000 in
/-- `union` preserves the canonical shape. Mirrors `contains_unionU` over the same mutual induction:
the merge quadrants reuse `WF_descend`/`WF_splice`/`WF_join`; the aligned-`bin` case rebuilds a
2-or-more-child node whose size is `size_mergeKids`, whose children are each well-formed
(`motive2`/`motive3`), and whose routing holds because each merged child's keys come from an
operand's aligned child (`contains_mergeChild`). The eliminator is applied with its instance pinned
(see `contains_unionU`). -/
theorem WF_unionU (cf : V → V → V) : ∀ (a b : PTree L), WF a → WF b → WF (unionU cf a b) := by
  intro a b
  induction a, b using (@unionU.induct L V inferInstance cf)
    (motive2 := fun m1 k1 m2 k2 rem acc =>
      KidsWF m1 k1 → KidsWF m2 k2 → (∀ c ∈ acc, WF c) →
        ∀ c ∈ mergeKids cf m1 k1 m2 k2 rem acc, WF c)
    (motive3 := fun m1 k1 m2 k2 i =>
      KidsWF m1 k1 → KidsWF m2 k2 → WF (mergeChild cf m1 k1 m2 k2 i)) with
  | case1 t => intro _ hwft; rw [unionU]; exact hwft
  | case2 s hs =>
    intro hwfs _
    rw [unionU]
    · exact hwfs
    · exact hs
  | case3 p1 b1 p2 b2 heq =>
    intro hwf1 _
    have hb1 : LeafOps.isEmpty b1 = false := by rw [WF] at hwf1; exact hwf1
    rw [unionU, if_pos heq, WF]
    exact LeafOps.isEmpty_join cf b1 b2 hb1
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
    have hb1 : LeafOps.isEmpty b1 = false := by rw [WF] at hwf1; exact hwf1
    have hbl0 : 0 < bl := by rw [WF] at hwf2; exact hwf2.1
    have hwfchild := by rw [WF] at hwf2; exact hwf2.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.tip p1 b1)) bl = bp := by simpa using hpfx
    have halign : AlignedAt bl (chunk (someKey (.tip p1 b1)) bl) bp (.tip p1 b1) :=
      by rw [← hpfxeq]; exact aligned_tip p1 b1 hb1 bl hbl0
    rw [unionU, if_pos hpfx, if_pos htb, dif_pos h]
    exact WF_descend_left cf (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl) (chunk_lt _ _)
      hwf2 halign hwf1 (by simp) htb h (IH hwf1 hwfchild)
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
    exact WF_splice (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl)
      (chunk_lt _ _) hwf2 halign hwf1 (by simp) htbf
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
    have hb2 : LeafOps.isEmpty b2 = false := by rw [WF] at hwftip; exact hwftip
    have hbl0 : 0 < bl := by rw [WF] at hwfbin; exact hwfbin.1
    have hwfchild := by rw [WF] at hwfbin; exact hwfbin.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.tip p2 b2)) bl = bp := by simpa using hpfx
    have halign : AlignedAt bl (chunk (someKey (.tip p2 b2)) bl) bp (.tip p2 b2) :=
      by rw [← hpfxeq]; exact aligned_tip p2 b2 hb2 bl hbl0
    rw [unionU, if_pos hpfx, if_pos htb, dif_pos h]
    exact WF_descend cf (.tip p2 b2) bp bl bm bk (chunk (someKey (.tip p2 b2)) bl) (chunk_lt _ _)
      hwfbin halign hwftip htb h (IH hwfchild hwftip)
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
    rw [unionU, if_pos hpfx, if_neg hntb]
    exact WF_splice (.tip p2 b2) bp bl bm bk (chunk (someKey (.tip p2 b2)) bl)
      (chunk_lt _ _) hwfbin halign hwftip (by simp) htbf
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
    refine ⟨hl0, size_mergeKids cf m1 k1 m2 k2, Nat.le_trans hpc1 (popCount_or_left m1 m2),
      IH hkw1 hkw2 (by intro c hc; simp at hc), ?_, ?_⟩
    · intro x hx
      rcases mergeKids_mem cf m1 k1 m2 k2 (m1 ||| m2).toNat (m1 ||| m2) rfl #[] x hx with hin | hex
      · simp at hin
      · obtain ⟨c, htb, hxc⟩ := hex
        rw [hxc]
        exact mergeChild_ne_nil cf m1 k1 m2 k2 c hkw1 hkw2 (by rw [← testBit_or]; exact htb)
    · intro c hclt htc
      rw [childAt_mergeKids cf m1 k1 m2 k2 c hclt htc]
      intro k hk
      rw [contains_mergeChild cf k m1 k1 m2 k2 c hkw1 hkw2 (by rw [← testBit_or]; exact htc),
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
    have hwfchild := by rw [WF] at hwf1; exact hwf1.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 = p1 := by simpa using hpfx
    have halign : AlignedAt l1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) p1 (.bin p2 l2 m2 k2) :=
      by rw [← hpfxeq]; exact aligned_bin p2 l2 m2 k2 hwf2 l1 hlt
    rw [unionU, if_neg hne, if_neg hlne, if_pos hlt, if_pos hpfx, if_pos htb, dif_pos h]
    exact WF_descend cf (.bin p2 l2 m2 k2) p1 l1 m1 k1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)
      (chunk_lt _ _) hwf1 halign hwf2 htb h (IH hwfchild hwf2)
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
    have hwfchild := by rw [WF] at hwf2; exact hwf2.2.2.2.1 _ (Array.getElem_mem h)
    have hpfxeq : prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 = p2 := by simpa using hpfx
    have halign : AlignedAt l2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) p2 (.bin p1 l1 m1 k1) :=
      by rw [← hpfxeq]; exact aligned_bin p1 l1 m1 k1 hwf1 l2 hl12
    rw [unionU, if_neg hne, if_neg hlne, if_neg hnlt, if_pos hpfx, if_pos htb, dif_pos h]
    exact WF_descend_left cf (.bin p1 l1 m1 k1) p2 l2 m2 k2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)
      (chunk_lt _ _) hwf2 halign hwf1 (by simp) htb h (IH hwf1 hwfchild)
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
    have hacc' : ∀ c' ∈ acc.push (mergeChild cf m1 k1 m2 k2 (lowestSetIdx rem)), WF c' := by
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
theorem WF_union (cf : V → V → V) (a b : PTree L) (hwa : WF a) (hwb : WF b) : WF (union cf a b) := by
  rw [union]; exact WF_unionU cf a b hwa hwb

/-! ### Intersection re-compression (`compactify`/`finalize`)

`meetU`'s aligned-`bin` case intersects the shared mask child-by-child (`meetKids`), producing an
array that may contain empty (`nil`) intersections. `compactify` drops those and recomputes the
surviving mask; `finalize` then re-wraps (0 survivors → `nil`, 1 → lift the lone child, ≥ 2 →
`bin`). The spec below pins down `compactify`'s output (its mask bits, its compact size, and that
reading any present slot recovers the original child), from which the `contains`/`WF` behaviour of
`finalize` follows. All leaf-agnostic — re-compression routes children, never touching values. -/

/-- The fold invariant of `compactify mask kids rem accM acc`, by strong induction on `rem.toNat`.
Starting from a seed `(accM, acc)` whose bits lie strictly below the unprocessed mask `rem`, it
keeps each non-empty child of `rem` lowest-first. The conclusion characterises the result mask
bit-for-bit (`accM` plus the surviving bits of `rem`), its compact size, and that reading any
present slot recovers `childAt mask kids`. -/
private theorem compactify_spec (mask : UInt32) (kids : Array (PTree L)) :
    ∀ (n : Nat) (rem : UInt32), rem.toNat = n → ∀ (accM : UInt32) (acc : Array (PTree L)),
      acc.size = popCount accM →
      (∀ c, c < 32 → testBit rem c = true → testBit accM c = false) →
      (∀ c c', c < 32 → c' < 32 → testBit accM c = true → testBit rem c' = true → c < c') →
      (∀ c, c < 32 → testBit accM c = true →
        acc[arrayIndex accM c]? = some (childAt mask kids c)) →
      (∀ c, c < 32 → testBit (compactify mask kids rem accM acc).1 c
          = (testBit accM c || (testBit rem c && !isNil (childAt mask kids c))))
      ∧ (compactify mask kids rem accM acc).2.size = popCount (compactify mask kids rem accM acc).1
      ∧ (∀ c, c < 32 → testBit (compactify mask kids rem accM acc).1 c = true →
          (compactify mask kids rem accM acc).2[arrayIndex (compactify mask kids rem accM acc).1 c]?
            = some (childAt mask kids c)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro rem hrem accM acc hP1 hP2 hP3 hP4
    by_cases h0 : (rem == 0) = true
    · have hr0 : rem = 0 := by simpa using h0
      rw [compactify, dif_pos h0]
      refine ⟨?_, hP1, ?_⟩
      · intro c hc; rw [hr0, testBit_zero, Bool.false_and, Bool.or_false]
      · intro c hc htb; exact hP4 c hc htb
    · have hrem0 : rem ≠ 0 := by intro h; exact h0 (by rw [h]; rfl)
      have hlo : lowestSetIdx rem < 32 := lowestSetIdx_lt rem hrem0
      have hlotb : testBit rem (lowestSetIdx rem) = true := testBit_lowestSetIdx rem hrem0
      have hlt : (clearLowest rem).toNat < n := by
        rw [← hrem]; exact UInt32.lt_iff_toNat_lt.mp (clearLowest_lt rem hrem0)
      by_cases hnil : isNil (childAt mask kids (lowestSetIdx rem)) = true
      · -- skip: the lowest slot's intersection is empty, drop it
        have hstep : compactify mask kids rem accM acc
            = compactify mask kids (clearLowest rem) accM acc := by
          rw [compactify, dif_neg h0, if_pos hnil]
        have hP2' : ∀ c, c < 32 → testBit (clearLowest rem) c = true → testBit accM c = false :=
          fun c hc htb => hP2 c hc (testBit_of_clearLowest rem c htb)
        have hP3' : ∀ c c', c < 32 → c' < 32 → testBit accM c = true →
            testBit (clearLowest rem) c' = true → c < c' :=
          fun c c' hc hc' hacc htb => hP3 c c' hc hc' hacc (testBit_of_clearLowest rem c' htb)
        obtain ⟨ihC1, ihC2, ihC3⟩ :=
          IH (clearLowest rem).toNat hlt (clearLowest rem) rfl accM acc hP1 hP2' hP3' hP4
        rw [hstep]
        refine ⟨?_, ihC2, ihC3⟩
        intro c hc
        rw [ihC1 c hc]
        by_cases hclo : c = lowestSetIdx rem
        · subst hclo
          rw [testBit_clearLowest_self rem hrem0, hlotb]
          simp only [hnil, Bool.not_true, Bool.and_false]
        · rw [testBit_clearLowest_of_ne rem c hc hclo]
      · -- keep: the lowest slot survives, push it and set its bit
        have hnf : isNil (childAt mask kids (lowestSetIdx rem)) = false := by
          simpa using hnil
        have hloacc : testBit accM (lowestSetIdx rem) = false := hP2 (lowestSetIdx rem) hlo hlotb
        have hbelow : ∀ d, d < 32 → testBit accM d = true → d < lowestSetIdx rem :=
          fun d hd hacc => hP3 d (lowestSetIdx rem) hd hlo hacc hlotb
        have hstep : compactify mask kids rem accM acc
            = compactify mask kids (clearLowest rem) (setBit accM (lowestSetIdx rem))
                (acc.push (childAt mask kids (lowestSetIdx rem))) := by
          rw [compactify, dif_neg h0, if_neg hnil]
        have hP1' : (acc.push (childAt mask kids (lowestSetIdx rem))).size
            = popCount (setBit accM (lowestSetIdx rem)) := by
          rw [Array.size_push, hP1, popCount_setBit accM (lowestSetIdx rem) hloacc]
        have hP2' : ∀ c, c < 32 → testBit (clearLowest rem) c = true →
            testBit (setBit accM (lowestSetIdx rem)) c = false := by
          intro c hc htb
          have hcne : c ≠ lowestSetIdx rem := by
            intro he; rw [he, testBit_clearLowest_self rem hrem0] at htb; exact absurd htb (by decide)
          rw [testBit_setBit accM (lowestSetIdx rem) c hlo hc,
              hP2 c hc (testBit_of_clearLowest rem c htb),
              beq_eq_false_iff_ne.mpr (fun he => hcne he.symm)]
          rfl
        have hP3' : ∀ c c', c < 32 → c' < 32 → testBit (setBit accM (lowestSetIdx rem)) c = true →
            testBit (clearLowest rem) c' = true → c < c' := by
          intro c c' hc hc' hacc htb'
          have hc'rem : testBit rem c' = true := testBit_of_clearLowest rem c' htb'
          have hc'ne : c' ≠ lowestSetIdx rem := by
            intro he; rw [he, testBit_clearLowest_self rem hrem0] at htb'
            exact absurd htb' (by decide)
          rw [testBit_setBit accM (lowestSetIdx rem) c hlo hc, Bool.or_eq_true] at hacc
          rcases hacc with haccM | heq
          · exact hP3 c c' hc hc' haccM hc'rem
          · have heq' : lowestSetIdx rem = c := by simpa using heq
            subst heq'
            exact uint32_lt_of_le_of_ne (lowestSetIdx_le_of_testBit rem c' hc' hc'rem)
              (fun he => hc'ne he.symm)
        have hP4' : ∀ c, c < 32 → testBit (setBit accM (lowestSetIdx rem)) c = true →
            (acc.push (childAt mask kids (lowestSetIdx rem)))[arrayIndex
              (setBit accM (lowestSetIdx rem)) c]? = some (childAt mask kids c) := by
          intro c hc htbc
          by_cases hclo : c = lowestSetIdx rem
          · subst hclo
            rw [arrayIndex_setBit_self,
                arrayIndex_eq_popCount_of_below accM (lowestSetIdx rem) hc hbelow, ← hP1,
                Array.getElem?_push_size]
          · have haccc : testBit accM c = true := by
              rw [testBit_setBit accM (lowestSetIdx rem) c hlo hc, Bool.or_eq_true] at htbc
              rcases htbc with h | h
              · exact h
              · have hcontra : lowestSetIdx rem = c := by simpa using h
                exact absurd hcontra (fun he => hclo he.symm)
            have hidxlt : arrayIndex accM c < acc.size := by
              rw [hP1]; exact arrayIndex_lt accM c haccc
            rw [arrayIndex_setBit_of_le accM (lowestSetIdx rem) c hlo hc
                  (uint32_le_of_lt (hbelow c hc haccc)),
                Array.getElem?_push_lt hidxlt, ← Array.getElem?_eq_getElem hidxlt]
            exact hP4 c hc haccc
        obtain ⟨ihC1, ihC2, ihC3⟩ :=
          IH (clearLowest rem).toNat hlt (clearLowest rem) rfl (setBit accM (lowestSetIdx rem))
            (acc.push (childAt mask kids (lowestSetIdx rem))) hP1' hP2' hP3' hP4'
        rw [hstep]
        refine ⟨?_, ihC2, ihC3⟩
        intro c hc
        rw [ihC1 c hc]
        by_cases hclo : c = lowestSetIdx rem
        · subst hclo
          rw [testBit_setBit accM (lowestSetIdx rem) (lowestSetIdx rem) hlo hlo,
              testBit_clearLowest_self rem hrem0, hloacc, hlotb, hnf]
          simp
        · rw [testBit_setBit accM (lowestSetIdx rem) c hlo hc,
              beq_eq_false_iff_ne.mpr (fun he => hclo he.symm), Bool.or_false,
              testBit_clearLowest_of_ne rem c hc hclo]

/-- `compactify_spec` specialised to the top-level call (`accM = 0`, `acc = #[]`): the surviving
mask has slot `c` iff `mask` did and the intersected child there is non-empty; the array stays
compact; and reading any present slot recovers `childAt mask kids`. -/
private theorem compactify_top (mask : UInt32) (kids : Array (PTree L)) :
    (∀ c, c < 32 → testBit (compactify mask kids mask 0 #[]).1 c
        = (testBit mask c && !isNil (childAt mask kids c)))
    ∧ (compactify mask kids mask 0 #[]).2.size = popCount (compactify mask kids mask 0 #[]).1
    ∧ (∀ c, c < 32 → testBit (compactify mask kids mask 0 #[]).1 c = true →
        (compactify mask kids mask 0 #[]).2[arrayIndex (compactify mask kids mask 0 #[]).1 c]?
          = some (childAt mask kids c)) := by
  obtain ⟨hM, hS, hR⟩ := compactify_spec mask kids mask.toNat mask rfl 0 #[]
    rfl
    (fun c _ _ => testBit_zero c)
    (fun c c' _ _ hacc _ => by simp [testBit_zero] at hacc)
    (fun c _ htb => by simp [testBit_zero] at htb)
  refine ⟨?_, hS, hR⟩
  intro c hc
  rw [hM c hc, testBit_zero, Bool.false_or]

/-- A short-circuit fact: if `b && !isNil x` is already `false`, then so is `b && contains j x`
(an empty child contains nothing). Bridges `compactify`'s "present and non-empty" mask bit to the
`contains` test `finalize` must satisfy. -/
private theorem and_contains_eq_false_of (j : Nat) (b : Bool) (x : PTree L)
    (h : (b && !isNil x) = false) : (b && contains j x) = false := by
  cases x with
  | nil => rw [contains_nil, Bool.and_false]
  | tip _ _ => simp only [isNil, Bool.not_false, Bool.and_true] at h; rw [h, Bool.false_and]
  | bin _ _ _ _ => simp only [isNil, Bool.not_false, Bool.and_true] at h; rw [h, Bool.false_and]

/-- Membership after re-compression: `finalize` collapses the empty-child cases but preserves
membership exactly — a key is in the re-wrapped branch iff its slot is present in `mask` and it is
in that slot's child. The single-survivor *lift* case relies on the routing hypothesis (`halign`):
the lifted child's keys all hang under its own slot, so dropping the branch level loses nothing. -/
theorem contains_finalize (j : Nat) (p l : Nat) (mask : UInt32) (kids : Array (PTree L))
    (halign : ∀ c, c < 32 → testBit mask c = true → AlignedAt l c p (childAt mask kids c)) :
    contains j (finalize p l mask kids)
      = (testBit mask (chunk j l) && contains j (childAt mask kids (chunk j l))) := by
  obtain ⟨m, ks, he⟩ : ∃ m ks, compactify mask kids mask 0 #[] = (m, ks) := ⟨_, _, rfl⟩
  obtain ⟨hM, _, hR⟩ := compactify_top mask kids
  rw [he] at hM hR
  have hMm : ∀ c, c < 32 → testBit m c = (testBit mask c && !isNil (childAt mask kids c)) := hM
  have hRm : ∀ c, c < 32 → testBit m c = true → ks[arrayIndex m c]? = some (childAt mask kids c) := hR
  have hmask_of_m : ∀ c, c < 32 → testBit m c = true → testBit mask c = true := by
    intro c hc htb
    have hmm := hMm c hc; rw [htb] at hmm
    cases hh : testBit mask c with
    | true => rfl
    | false => rw [hh, Bool.false_and] at hmm; exact absurd hmm (by decide)
  have hchild : ∀ c, c < 32 → testBit m c = true → childAt m ks c = childAt mask kids c := by
    intro c hc htb
    show (ks[arrayIndex m c]?).getD .nil = childAt mask kids c
    rw [hRm c hc htb, Option.getD_some]
  have hbridge : (testBit m (chunk j l) && contains j (childAt m ks (chunk j l)))
      = (testBit mask (chunk j l) && contains j (childAt mask kids (chunk j l))) := by
    by_cases htm : testBit m (chunk j l) = true
    · rw [htm, hchild (chunk j l) (chunk_lt j l) htm, hmask_of_m (chunk j l) (chunk_lt j l) htm]
    · simp only [Bool.not_eq_true] at htm
      rw [htm, Bool.false_and]
      have hkey : (testBit mask (chunk j l) && !isNil (childAt mask kids (chunk j l))) = false := by
        rw [← hMm (chunk j l) (chunk_lt j l), htm]
      exact (and_contains_eq_false_of j _ _ hkey).symm
  rw [finalize, he]
  show contains j (if m == 0 then .nil
        else if popCount m == 1 then (ks[0]?).getD .nil else .bin p l m ks)
      = (testBit mask (chunk j l) && contains j (childAt mask kids (chunk j l)))
  by_cases hm0 : (m == 0) = true
  · rw [if_pos hm0, contains_nil]
    have hmeq : m = 0 := by simpa using hm0
    rw [← hbridge, hmeq, testBit_zero, Bool.false_and]
  · rw [if_neg hm0]
    by_cases hp1 : (popCount m == 1) = true
    · rw [if_pos hp1]
      have hpc1 : popCount m = 1 := by simpa using hp1
      have hmne : m ≠ 0 := fun h0 => hm0 (by rw [h0]; rfl)
      have hc0 : testBit m (lowestSetIdx m) = true := testBit_lowestSetIdx m hmne
      have hlo32 : lowestSetIdx m < 32 := lowestSetIdx_lt m hmne
      have huniq : ∀ c, c < 32 → testBit m c = true → c = lowestSetIdx m := by
        intro c hc htb
        by_cases hcc : c = lowestSetIdx m
        · exact hcc
        · exfalso
          have h1 := arrayIndex_inj m c (lowestSetIdx m) hc hlo32 htb hc0 hcc
          rw [arrayIndex_lowestSetIdx m hmne] at h1
          have ha := arrayIndex_lt m c htb
          rw [hpc1] at ha
          omega
      have hks0 : (ks[0]?).getD .nil = childAt mask kids (lowestSetIdx m) := by
        have hr0 := hRm (lowestSetIdx m) hlo32 hc0
        rw [arrayIndex_lowestSetIdx m hmne] at hr0
        rw [hr0, Option.getD_some]
      rw [hks0, ← hbridge]
      by_cases hcjl : chunk j l = lowestSetIdx m
      · rw [hcjl, hc0, hchild (lowestSetIdx m) hlo32 hc0, Bool.true_and]
      · have htmf : testBit m (chunk j l) = false := by
          cases hh : testBit m (chunk j l) with
          | false => rfl
          | true => exact absurd (huniq (chunk j l) (chunk_lt j l) hh) hcjl
        rw [htmf, Bool.false_and]
        cases hcon : contains j (childAt mask kids (lowestSetIdx m)) with
        | false => rfl
        | true =>
          have hal := halign (lowestSetIdx m) hlo32 (hmask_of_m (lowestSetIdx m) hlo32 hc0) j hcon
          exact absurd hal.1 hcjl
    · rw [if_neg hp1, contains_bin]
      exact hbridge

/-- Every child `compactify` keeps comes from the seed `acc` or is a present, non-empty
`childAt mask kids` of a surviving slot. The membership companion to `compactify_spec`; it discharges
`WF_finalize`'s well-formed / non-`nil` children clauses. -/
private theorem compactify_mem (mask : UInt32) (kids : Array (PTree L)) :
    ∀ (n : Nat) (rem : UInt32), rem.toNat = n → ∀ (accM : UInt32) (acc : Array (PTree L)) (x : PTree L),
      x ∈ (compactify mask kids rem accM acc).2 →
        x ∈ acc ∨ ∃ c, c < 32 ∧ testBit rem c = true ∧ isNil (childAt mask kids c) = false
          ∧ x = childAt mask kids c := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro rem hrem accM acc x hx
    by_cases h0 : (rem == 0) = true
    · rw [compactify, dif_pos h0] at hx; exact Or.inl hx
    · have hrem0 : rem ≠ 0 := by intro h; exact h0 (by rw [h]; rfl)
      have hlo : lowestSetIdx rem < 32 := lowestSetIdx_lt rem hrem0
      have hlotb : testBit rem (lowestSetIdx rem) = true := testBit_lowestSetIdx rem hrem0
      have hlt : (clearLowest rem).toNat < n := by
        rw [← hrem]; exact UInt32.lt_iff_toNat_lt.mp (clearLowest_lt rem hrem0)
      by_cases hnil : isNil (childAt mask kids (lowestSetIdx rem)) = true
      · rw [compactify, dif_neg h0, if_pos hnil] at hx
        rcases IH (clearLowest rem).toNat hlt (clearLowest rem) rfl accM acc x hx with hacc | hex
        · exact Or.inl hacc
        · obtain ⟨c, hc, htb, hnfc, hxc⟩ := hex
          exact Or.inr ⟨c, hc, testBit_of_clearLowest rem c htb, hnfc, hxc⟩
      · have hnf : isNil (childAt mask kids (lowestSetIdx rem)) = false := by simpa using hnil
        rw [compactify, dif_neg h0, if_neg hnil] at hx
        rcases IH (clearLowest rem).toNat hlt (clearLowest rem) rfl (setBit accM (lowestSetIdx rem))
            (acc.push (childAt mask kids (lowestSetIdx rem))) x hx with hacc | hex
        · rcases Array.mem_push.mp hacc with hin | heq
          · exact Or.inl hin
          · exact Or.inr ⟨lowestSetIdx rem, hlo, hlotb, hnf, heq⟩
        · obtain ⟨c, hc, htb, hnfc, hxc⟩ := hex
          exact Or.inr ⟨c, hc, testBit_of_clearLowest rem c htb, hnfc, hxc⟩

/-- Top-level form of `compactify_mem`: every child the re-compressed array holds is a present,
non-empty `childAt mask kids`. -/
private theorem compactify_mem_top (mask : UInt32) (kids : Array (PTree L)) (x : PTree L)
    (hx : x ∈ (compactify mask kids mask 0 #[]).2) :
    ∃ c, c < 32 ∧ testBit mask c = true ∧ isNil (childAt mask kids c) = false
      ∧ x = childAt mask kids c := by
  rcases compactify_mem mask kids mask.toNat mask rfl 0 #[] x hx with hacc | hex
  · simp at hacc
  · exact hex

/-- `finalize` preserves well-formedness. Given aligned, well-formed candidate children under `mask`,
the re-wrapped branch is canonical: the empty cases (`nil`, lifted singleton) are trivially or
directly `WF`; the `bin` case rebuilds a `≥ 2`-child node whose size (`compactify_top`), children
(`compactify_mem_top`), non-emptiness, and routing (`hchild`/`halign`) all hold. -/
theorem WF_finalize (p l : Nat) (mask : UInt32) (kids : Array (PTree L)) (hl : 0 < l)
    (hwf : ∀ c, c < 32 → testBit mask c = true → WF (childAt mask kids c))
    (halign : ∀ c, c < 32 → testBit mask c = true → AlignedAt l c p (childAt mask kids c)) :
    WF (finalize p l mask kids) := by
  obtain ⟨m, ks, he⟩ : ∃ m ks, compactify mask kids mask 0 #[] = (m, ks) := ⟨_, _, rfl⟩
  obtain ⟨hM, hS, hR⟩ := compactify_top mask kids
  rw [he] at hM hS hR
  have hMm : ∀ c, c < 32 → testBit m c = (testBit mask c && !isNil (childAt mask kids c)) := hM
  have hSm : ks.size = popCount m := hS
  have hRm : ∀ c, c < 32 → testBit m c = true → ks[arrayIndex m c]? = some (childAt mask kids c) := hR
  have hmask_of_m : ∀ c, c < 32 → testBit m c = true → testBit mask c = true := by
    intro c hc htb
    have hmm := hMm c hc; rw [htb] at hmm
    cases hh : testBit mask c with
    | true => rfl
    | false => rw [hh, Bool.false_and] at hmm; exact absurd hmm (by decide)
  have hchild : ∀ c, c < 32 → testBit m c = true → childAt m ks c = childAt mask kids c := by
    intro c hc htb
    show (ks[arrayIndex m c]?).getD .nil = childAt mask kids c
    rw [hRm c hc htb, Option.getD_some]
  have hmem : ∀ x ∈ ks, ∃ c, c < 32 ∧ testBit mask c = true ∧ isNil (childAt mask kids c) = false
      ∧ x = childAt mask kids c := by
    intro x hx
    exact compactify_mem_top mask kids x (by rw [he]; exact hx)
  rw [finalize, he]
  show WF (if m == 0 then .nil
        else if popCount m == 1 then (ks[0]?).getD .nil else .bin p l m ks)
  by_cases hm0 : (m == 0) = true
  · rw [if_pos hm0, WF]; trivial
  · rw [if_neg hm0]
    have hmne : m ≠ 0 := fun h0 => hm0 (by rw [h0]; rfl)
    by_cases hp1 : (popCount m == 1) = true
    · rw [if_pos hp1]
      have hc0 : testBit m (lowestSetIdx m) = true := testBit_lowestSetIdx m hmne
      have hlo32 : lowestSetIdx m < 32 := lowestSetIdx_lt m hmne
      have hks0 : (ks[0]?).getD .nil = childAt mask kids (lowestSetIdx m) := by
        have hr0 := hRm (lowestSetIdx m) hlo32 hc0
        rw [arrayIndex_lowestSetIdx m hmne] at hr0
        rw [hr0, Option.getD_some]
      rw [hks0]
      exact hwf (lowestSetIdx m) hlo32 (hmask_of_m (lowestSetIdx m) hlo32 hc0)
    · rw [if_neg hp1, WF]
      have hpc2 : 2 ≤ popCount m := by
        have h1 := one_le_popCount_of_ne_zero m hmne
        have hne1 : popCount m ≠ 1 := fun h => hp1 (by rw [h]; rfl)
        omega
      refine ⟨hl, hSm, hpc2, ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨c', hc', htmask, _, hxc⟩ := hmem x hx
        rw [hxc]; exact hwf c' hc' htmask
      · intro x hx
        obtain ⟨c', _, _, hnf, hxc⟩ := hmem x hx
        rw [hxc]; intro hnil; rw [hnil] at hnf; simp [isNil] at hnf
      · intro c hc htb
        rw [hchild c hc htb]
        exact halign c hc (hmask_of_m c hc htb)

/-! ### Intersection (`meet`)

`meetU` is the per-slot intersection driver. Its aligned-`bin` case rebuilds the shared-mask child
array (`meetKids`/`meetChild`) and re-compresses it (`finalize`). The `WF` and membership facts are
proven together in a single mutual induction (`meet_WF_contains`): the membership equation the
induction hypothesis supplies is exactly the routing (`AlignedAt`) witness `finalize` needs, so the
two properties bootstrap each other. -/

/-- `meetKids`'s fold invariant — the verbatim `mergeKids_spec` shape for the shared mask. -/
private theorem meetKids_spec (cf : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) :
    ∀ (n : Nat) (rem : UInt32), rem.toNat = n → ∀ (acc : Array (PTree L)),
      (meetKids cf m1 k1 m2 k2 rem acc).size = acc.size + popCount rem
      ∧ (∀ i, i < acc.size → (meetKids cf m1 k1 m2 k2 rem acc)[i]? = acc[i]?)
      ∧ (∀ c, c < 32 → testBit rem c = true →
           (meetKids cf m1 k1 m2 k2 rem acc)[acc.size + arrayIndex rem c]?
             = some (meetChild cf m1 k1 m2 k2 c)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro rem hrem acc
    by_cases h0 : (rem == 0) = true
    · have hr0 : rem = 0 := by simpa using h0
      rw [meetKids, dif_pos h0]
      refine ⟨?_, ?_, ?_⟩
      · rw [hr0, show popCount (0 : UInt32) = 0 from rfl, Nat.add_zero]
      · intro i hi; rfl
      · intro c hc htb; rw [hr0, testBit_zero] at htb; exact absurd htb (by decide)
    · have hrem0 : rem ≠ 0 := by intro h; exact h0 (by rw [h]; rfl)
      have hstep : meetKids cf m1 k1 m2 k2 rem acc
          = meetKids cf m1 k1 m2 k2 (clearLowest rem)
              (acc.push (meetChild cf m1 k1 m2 k2 (lowestSetIdx rem))) := by
        rw [meetKids, dif_neg h0]
      have hlt : (clearLowest rem).toNat < n := by
        rw [← hrem]; exact UInt32.lt_iff_toNat_lt.mp (clearLowest_lt rem hrem0)
      obtain ⟨ihsize, ihpref, ihthird⟩ :=
        IH (clearLowest rem).toNat hlt (clearLowest rem) rfl
          (acc.push (meetChild cf m1 k1 m2 k2 (lowestSetIdx rem)))
      have hpc : popCount (clearLowest rem) + 1 = popCount rem := popCount_clearLowest rem hrem0
      have haccsz : (acc.push (meetChild cf m1 k1 m2 k2 (lowestSetIdx rem))).size = acc.size + 1 :=
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

/-- Reading a present slot of the shared-mask child array recovers that slot's `meetChild`. -/
theorem childAt_meetKids (cf : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) (c : UInt32) (hc : c < 32) (htb : testBit (m1 &&& m2) c = true) :
    childAt (m1 &&& m2) (meetKids cf m1 k1 m2 k2 (m1 &&& m2) #[]) c = meetChild cf m1 k1 m2 k2 c := by
  obtain ⟨_, _, hthird⟩ := meetKids_spec cf m1 k1 m2 k2 (m1 &&& m2).toNat (m1 &&& m2) rfl #[]
  have hc' := hthird c hc htb
  unfold childAt
  rw [show (#[] : Array (PTree L)).size = 0 from rfl, Nat.zero_add] at hc'
  rw [hc', Option.getD_some]

/-- The shared-mask child array has one slot per present bit of `m1 &&& m2`. -/
theorem size_meetKids (cf : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) :
    (meetKids cf m1 k1 m2 k2 (m1 &&& m2) #[]).size = popCount (m1 &&& m2) := by
  obtain ⟨hsize, _, _⟩ := meetKids_spec cf m1 k1 m2 k2 (m1 &&& m2).toNat (m1 &&& m2) rfl #[]
  rw [hsize, show (#[] : Array (PTree L)).size = 0 from rfl, Nat.zero_add]

/-- A `bin`'s keys all share its branch prefix at its own level — the routing fact membership pins
down. The half of `WF`'s routing clause the intersection's divergence cases consume. -/
private theorem prefixAbove_of_contains_bin (k bp bl : Nat) (bm : UInt32) (bk : Array (PTree L))
    (hwf : WF (.bin bp bl bm bk)) (h : contains k (.bin bp bl bm bk) = true) :
    prefixAbove k bl = bp := by
  rw [contains_bin, Bool.and_eq_true] at h
  obtain ⟨htb, hchild⟩ := h
  rw [WF] at hwf
  exact (hwf.2.2.2.2.2 (chunk k bl) (chunk_lt k bl) htb k hchild).2

/-- An empty leaf contains no slot — the leaf-level fact the tip/tip disjoint intersection case
needs to rule out a shared key when the leaf meet empties. Derived from the `LeafOps` seam
`eq_empty_of_isEmpty` plus `get?_empty` (an empty leaf reads `none` everywhere). -/
private theorem leaf_contains_eq_false_of_isEmpty (l : L) (i : UInt32)
    (h : LeafOps.isEmpty l = true) : LeafOps.contains l i = false := by
  rw [LeafOps.contains_eq_isSome, LeafOps.eq_empty_of_isEmpty l h, LeafOps.get?_empty]; rfl

/-- Split a `Bool` conjunction that holds into its two components. -/
private theorem and_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

/-- The two-pair `&&` reassociation the `tip`/`tip` divergence cases pivot on. -/
private theorem and_pair_swap (A B C D : Bool) :
    ((A && B) && (C && D)) = ((A && C) && (B && D)) := by
  cases A <;> cases B <;> cases C <;> cases D <;> rfl

/-- Two `tip`s whose leaf-meet empties share no key — every key common to both would survive the
leaf intersection, contradicting its emptiness. The generic successor of the monomorphic
bitset-disjoint lemma: where the old leaf used `b1 &&& b2 = 0`, the leaf meet emptying is the
abstract disjointness, bridged by `leaf_contains_meet`. -/
private theorem contains_tiptip_disjoint (cf : V → V → V) (k p1 : Nat) (b1 : L) (p2 : Nat) (b2 : L)
    (hdis : LeafOps.isEmpty (LeafOps.meet cf b1 b2) = true) :
    (contains k (.tip p1 b1) && contains k (.tip p2 b2)) = false := by
  have hmeet : (LeafOps.contains b1 (chunk k 0) && LeafOps.contains b2 (chunk k 0)) = false := by
    rw [← leaf_contains_meet cf b1 b2 (chunk k 0) (chunk_lt _ _)]
    exact leaf_contains_eq_false_of_isEmpty (LeafOps.meet cf b1 b2) (chunk k 0) hdis
  rw [contains_tip, contains_tip, and_pair_swap, hmeet, Bool.and_false]

/-- Two `tip`s with different prefixes share no key — a key can match only one prefix. -/
private theorem contains_tiptip_pfxne (k p1 : Nat) (b1 : L) (p2 : Nat) (b2 : L)
    (hpne : p1 ≠ p2) :
    (contains k (.tip p1 b1) && contains k (.tip p2 b2)) = false := by
  rw [contains_tip, contains_tip, and_pair_swap]
  have hpp : ((k >>> 5 == p1) && (k >>> 5 == p2)) = false := by
    cases h1 : (k >>> 5 == p1) with
    | false => rfl
    | true =>
      cases h2 : (k >>> 5 == p2) with
      | false => rfl
      | true => rw [beq_iff_eq] at h1 h2; exact absurd (h1.symm.trans h2) hpne
  rw [hpp, Bool.false_and]

/-- Two equal-level `bin`s with different prefixes share no key. -/
private theorem contains_binbin_pfxne (k p1 l : Nat) (m1 : UInt32) (k1 : Array (PTree L))
    (p2 : Nat) (m2 : UInt32) (k2 : Array (PTree L))
    (hwf1 : WF (.bin p1 l m1 k1)) (hwf2 : WF (.bin p2 l m2 k2)) (hpne : p1 ≠ p2) :
    (contains k (.bin p1 l m1 k1) && contains k (.bin p2 l m2 k2)) = false := by
  cases hB1 : contains k (.bin p1 l m1 k1) with
  | false => rfl
  | true =>
    cases hB2 : contains k (.bin p2 l m2 k2) with
    | false => rfl
    | true =>
      exact absurd (Eq.trans (prefixAbove_of_contains_bin k p1 l m1 k1 hwf1 hB1).symm
        (prefixAbove_of_contains_bin k p2 l m2 k2 hwf2 hB2)) hpne

/-- A `bin` and a tree `R` aligned to a slot the `bin` routes *away from* (absent, or wrong prefix)
share no key. The single divergence lemma for the routing/absent intersection cases (the right
operand is supplied via `aligned_tip`/`aligned_bin`). -/
private theorem contains_div_eq_false (k : Nat) (bp bl : Nat) (bm : UInt32) (bk : Array (PTree L))
    (R : PTree L) (c0 : UInt32) (pr : Nat) (hwfbin : WF (.bin bp bl bm bk))
    (halignR : AlignedAt bl c0 pr R)
    (hcond : ((pr == bp) && testBit bm c0) = false) :
    (contains k R && contains k (.bin bp bl bm bk)) = false := by
  cases hR : contains k R with
  | false => rfl
  | true =>
    obtain ⟨hchunk, hpfx⟩ := halignR k hR
    cases hB : contains k (.bin bp bl bm bk) with
    | false => rfl
    | true =>
      exfalso
      have hpref : prefixAbove k bl = bp := prefixAbove_of_contains_bin k bp bl bm bk hwfbin hB
      have htb : testBit bm (chunk k bl) = true := by
        rw [contains_bin, Bool.and_eq_true] at hB; exact hB.1
      rw [hchunk] at htb
      have hpreq : pr = bp := by rw [← hpfx]; exact hpref
      rw [hpreq, beq_self_eq_true, htb] at hcond
      exact absurd hcond (by decide)

/-- Descend bridge (right operand is the `bin`): intersecting `R` with the `bin`'s routed child is
the same as intersecting `R` with the whole `bin` — keys of `R` route only to that one slot. -/
private theorem contains_meet_descend_right (k bp bl : Nat) (bm : UInt32) (bk : Array (PTree L))
    (R : PTree L) (c0 : UInt32) (pr : Nat) (halignR : AlignedAt bl c0 pr R)
    (htb : testBit bm c0 = true) :
    (contains k R && contains k (childAt bm bk c0))
      = (contains k R && contains k (.bin bp bl bm bk)) := by
  by_cases hR : contains k R = true
  · obtain ⟨hchunk, _⟩ := halignR k hR
    rw [hR, contains_bin, hchunk, htb]; simp only [Bool.true_and]
  · simp only [Bool.not_eq_true] at hR
    rw [hR, Bool.false_and, Bool.false_and]

/-- Descend bridge (left operand is the `bin`): the mirror of `contains_meet_descend_right`. -/
private theorem contains_meet_descend_left (k bp bl : Nat) (bm : UInt32) (bk : Array (PTree L))
    (R : PTree L) (c0 : UInt32) (pr : Nat) (halignR : AlignedAt bl c0 pr R)
    (htb : testBit bm c0 = true) :
    (contains k (childAt bm bk c0) && contains k R)
      = (contains k (.bin bp bl bm bk) && contains k R) := by
  rw [Bool.and_comm (contains k (childAt bm bk c0)) (contains k R),
      Bool.and_comm (contains k (.bin bp bl bm bk)) (contains k R)]
  exact contains_meet_descend_right k bp bl bm bk R c0 pr halignR htb

set_option maxHeartbeats 400000 in
/-- The intersection's `WF` and membership characterisation, proven together: `WF (meetU cf a b)`
and `∀ k, contains k (meetU cf a b) = (contains k a && contains k b)`. Doing both in one mutual
induction lets the (∀-`k`) membership IH supply exactly the routing (`AlignedAt`) witness `finalize`
needs in the aligned-`bin` case. The generic `LeafOps` instance roughly triples the elaboration
cost, so the heartbeat budget is raised, and the eliminator is applied with `L`/`V`/instance/`cf`
pinned (`@meetU.induct L V inferInstance cf`) to keep the motives concrete. -/
theorem meet_WF_contains (cf : V → V → V) : ∀ (a b : PTree L), WF a → WF b →
    WF (meetU cf a b) ∧ ∀ k, contains k (meetU cf a b) = (contains k a && contains k b) := by
  intro a b
  induction a, b using (@meetU.induct L V inferInstance cf)
    (motive2 := fun m1 k1 m2 k2 rem _ =>
      KidsWF m1 k1 → KidsWF m2 k2 →
      (∀ c, c < 32 → testBit rem c = true → testBit m1 c = true ∧ testBit m2 c = true) →
      ∀ c, c < 32 → testBit rem c = true →
        WF (meetChild cf m1 k1 m2 k2 c)
        ∧ ∀ k, contains k (meetChild cf m1 k1 m2 k2 c)
            = (contains k (childAt m1 k1 c) && contains k (childAt m2 k2 c)))
    (motive3 := fun m1 k1 m2 k2 i =>
      KidsWF m1 k1 → KidsWF m2 k2 → testBit m1 i = true → testBit m2 i = true →
        WF (meetChild cf m1 k1 m2 k2 i)
        ∧ ∀ k, contains k (meetChild cf m1 k1 m2 k2 i)
            = (contains k (childAt m1 k1 i) && contains k (childAt m2 k2 i))) with
  | case1 x =>
    intro _ _
    exact ⟨by rw [meetU, WF]; trivial, fun k => by rw [meetU, contains_nil, Bool.false_and]⟩
  | case2 p1 b1 =>
    intro _ _
    exact ⟨by rw [meetU, WF]; trivial, fun k => by rw [meetU, contains_nil, Bool.and_false]⟩
  | case3 bp bl bm bk =>
    intro _ _
    exact ⟨by rw [meetU, WF]; trivial, fun k => by rw [meetU, contains_nil, Bool.and_false]⟩
  | case4 p1 b1 p2 b2 heq hdis =>
    intro _ _
    refine ⟨by rw [meetU, if_pos heq, if_pos hdis, WF]; trivial, ?_⟩
    intro k
    rw [meetU, if_pos heq, if_pos hdis, contains_nil]
    exact (contains_tiptip_disjoint cf k p1 b1 p2 b2 hdis).symm
  | case5 p1 b1 p2 b2 heq hndis =>
    intro _ _
    have hp : p1 = p2 := by simpa using heq
    have hbne : LeafOps.isEmpty (LeafOps.meet cf b1 b2) = false := by simpa using hndis
    refine ⟨by rw [meetU, if_pos heq, if_neg hndis, WF]; exact hbne, ?_⟩
    intro k
    rw [meetU, if_pos heq, if_neg hndis, contains_tip, contains_tip, contains_tip,
        leaf_contains_meet cf b1 b2 (chunk k 0) (chunk_lt _ _), ← hp]
    cases (k >>> 5 == p1) <;> cases LeafOps.contains b1 (chunk k 0) <;>
      cases LeafOps.contains b2 (chunk k 0) <;> rfl
  | case6 p1 b1 p2 b2 hne =>
    intro _ _
    have hpne : p1 ≠ p2 := by intro h; exact hne (by rw [h]; exact beq_self_eq_true p2)
    refine ⟨by rw [meetU, if_neg hne, WF]; trivial, ?_⟩
    intro k
    rw [meetU, if_neg hne, contains_nil]
    exact (contains_tiptip_pfxne k p1 b1 p2 b2 hpne).symm
  | case7 p1 b1 bp bl bm bk hcond h IH =>
    intro hwfa hwfb
    have hb1 : LeafOps.isEmpty b1 = false := by rw [WF] at hwfa; exact hwfa
    have hbl0 : 0 < bl := by rw [WF] at hwfb; exact hwfb.1
    have hwfchild := by rw [WF] at hwfb; exact hwfb.2.2.2.1 _ (Array.getElem_mem h)
    obtain ⟨hpfxb, htbb⟩ := and_split hcond
    have hpfxeq : prefixAbove (someKey (.tip p1 b1)) bl = bp := by simpa using hpfxb
    have halign : AlignedAt bl (chunk (someKey (.tip p1 b1)) bl) bp (.tip p1 b1) :=
      hpfxeq ▸ aligned_tip p1 b1 hb1 bl hbl0
    have hcAc : childAt bm bk (chunk (someKey (.tip p1 b1)) bl)
        = bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h := by
      unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
    have hmu : meetU cf (.tip p1 b1) (.bin bp bl bm bk)
        = meetU cf (.tip p1 b1) (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h) := by
      rw [meetU, if_pos hcond, dif_pos h]
    obtain ⟨ihwf, ihc⟩ := IH hwfa hwfchild
    rw [hmu]
    refine ⟨ihwf, ?_⟩
    intro k
    rw [ihc k, ← hcAc]
    exact contains_meet_descend_right k bp bl bm bk (.tip p1 b1)
      (chunk (someKey (.tip p1 b1)) bl) bp halign htbb
  | case8 p1 b1 bp bl bm bk hcond hnh =>
    intro _ hwfb
    obtain ⟨_, htbb⟩ := and_split hcond
    have hsize : bk.size = popCount bm := by rw [WF] at hwfb; exact hwfb.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt bm _ htbb) hnh
  | case9 p1 b1 bp bl bm bk hncond =>
    intro hwfa hwfb
    have hb1 : LeafOps.isEmpty b1 = false := by rw [WF] at hwfa; exact hwfa
    have hbl0 : 0 < bl := by rw [WF] at hwfb; exact hwfb.1
    have hcondf : ((prefixAbove (someKey (.tip p1 b1)) bl == bp)
        && testBit bm (chunk (someKey (.tip p1 b1)) bl)) = false := by simpa using hncond
    have halign : AlignedAt bl (chunk (someKey (.tip p1 b1)) bl)
        (prefixAbove (someKey (.tip p1 b1)) bl) (.tip p1 b1) := aligned_tip p1 b1 hb1 bl hbl0
    refine ⟨by rw [meetU, if_neg hncond, WF]; trivial, ?_⟩
    intro k
    rw [meetU, if_neg hncond, contains_nil]
    exact (contains_div_eq_false k bp bl bm bk (.tip p1 b1) (chunk (someKey (.tip p1 b1)) bl)
      (prefixAbove (someKey (.tip p1 b1)) bl) hwfb halign hcondf).symm
  | case10 bp bl bm bk p2 b2 hcond h IH =>
    intro hwfa hwfb
    have hb2 : LeafOps.isEmpty b2 = false := by rw [WF] at hwfb; exact hwfb
    have hbl0 : 0 < bl := by rw [WF] at hwfa; exact hwfa.1
    have hwfchild := by rw [WF] at hwfa; exact hwfa.2.2.2.1 _ (Array.getElem_mem h)
    obtain ⟨hpfxb, htbb⟩ := and_split hcond
    have hpfxeq : prefixAbove (someKey (.tip p2 b2)) bl = bp := by simpa using hpfxb
    have halign : AlignedAt bl (chunk (someKey (.tip p2 b2)) bl) bp (.tip p2 b2) :=
      hpfxeq ▸ aligned_tip p2 b2 hb2 bl hbl0
    have hcAc : childAt bm bk (chunk (someKey (.tip p2 b2)) bl)
        = bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h := by
      unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
    have hmu : meetU cf (.bin bp bl bm bk) (.tip p2 b2)
        = meetU cf (bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h) (.tip p2 b2) := by
      rw [meetU, if_pos hcond, dif_pos h]
    obtain ⟨ihwf, ihc⟩ := IH hwfchild hwfb
    rw [hmu]
    refine ⟨ihwf, ?_⟩
    intro k
    rw [ihc k, ← hcAc]
    exact contains_meet_descend_left k bp bl bm bk (.tip p2 b2)
      (chunk (someKey (.tip p2 b2)) bl) bp halign htbb
  | case11 bp bl bm bk p2 b2 hcond hnh =>
    intro hwfa _
    obtain ⟨_, htbb⟩ := and_split hcond
    have hsize : bk.size = popCount bm := by rw [WF] at hwfa; exact hwfa.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt bm _ htbb) hnh
  | case12 bp bl bm bk p2 b2 hncond =>
    intro hwfa hwfb
    have hb2 : LeafOps.isEmpty b2 = false := by rw [WF] at hwfb; exact hwfb
    have hbl0 : 0 < bl := by rw [WF] at hwfa; exact hwfa.1
    have hcondf : ((prefixAbove (someKey (.tip p2 b2)) bl == bp)
        && testBit bm (chunk (someKey (.tip p2 b2)) bl)) = false := by simpa using hncond
    have halign : AlignedAt bl (chunk (someKey (.tip p2 b2)) bl)
        (prefixAbove (someKey (.tip p2 b2)) bl) (.tip p2 b2) := aligned_tip p2 b2 hb2 bl hbl0
    refine ⟨by rw [meetU, if_neg hncond, WF]; trivial, ?_⟩
    intro k
    rw [meetU, if_neg hncond, contains_nil,
        Bool.and_comm (contains k (.bin bp bl bm bk)) (contains k (.tip p2 b2))]
    exact (contains_div_eq_false k bp bl bm bk (.tip p2 b2) (chunk (someKey (.tip p2 b2)) bl)
      (prefixAbove (someKey (.tip p2 b2)) bl) hwfa halign hcondf).symm
  | case13 p1 l1 m1 k1 p2 l2 m2 k2 heq hpfx IH =>
    intro hwf1 hwf2
    have hl : l1 = l2 := by simpa using heq
    subst hl
    have hkw1 : KidsWF m1 k1 := by rw [WF] at hwf1; exact ⟨hwf1.2.1, hwf1.2.2.2.1, hwf1.2.2.2.2.1⟩
    have hkw2 : KidsWF m2 k2 := by rw [WF] at hwf2; exact ⟨hwf2.2.1, hwf2.2.2.2.1, hwf2.2.2.2.2.1⟩
    have hl0 : 0 < l1 := by rw [WF] at hwf1; exact hwf1.1
    have hrout1 : ∀ c, c < 32 → testBit m1 c = true → AlignedAt l1 c p1 (childAt m1 k1 c) := by
      rw [WF] at hwf1; exact hwf1.2.2.2.2.2
    have hslot := IH hkw1 hkw2 (fun c _ hb => by
      rw [testBit_and] at hb; exact ⟨(and_split hb).1, (and_split hb).2⟩)
    have hwfchildren : ∀ c, c < 32 → testBit (m1 &&& m2) c = true →
        WF (childAt (m1 &&& m2) (meetKids cf m1 k1 m2 k2 (m1 &&& m2) #[]) c) := by
      intro c hc htb
      rw [childAt_meetKids cf m1 k1 m2 k2 c hc htb]; exact (hslot c hc htb).1
    have halign : ∀ c, c < 32 → testBit (m1 &&& m2) c = true →
        AlignedAt l1 c p1 (childAt (m1 &&& m2) (meetKids cf m1 k1 m2 k2 (m1 &&& m2) #[]) c) := by
      intro c hc htb
      rw [childAt_meetKids cf m1 k1 m2 k2 c hc htb]
      intro key hkey
      rw [(hslot c hc htb).2 key] at hkey
      have htbm1 : testBit m1 c = true := by
        rw [testBit_and] at htb; exact (and_split htb).1
      exact hrout1 c hc htbm1 key (and_split hkey).1
    have hmu : meetU cf (.bin p1 l1 m1 k1) (.bin p2 l1 m2 k2)
        = finalize p1 l1 (m1 &&& m2) (meetKids cf m1 k1 m2 k2 (m1 &&& m2) #[]) := by
      rw [meetU, if_pos heq, if_pos hpfx]
    rw [hmu]
    refine ⟨WF_finalize p1 l1 (m1 &&& m2) _ hl0 hwfchildren halign, ?_⟩
    intro k
    rw [contains_finalize k p1 l1 (m1 &&& m2) _ halign, contains_bin, contains_bin]
    by_cases hM : testBit (m1 &&& m2) (chunk k l1) = true
    · rw [hM, Bool.true_and, childAt_meetKids cf m1 k1 m2 k2 (chunk k l1) (chunk_lt k l1) hM,
          (hslot (chunk k l1) (chunk_lt k l1) hM).2 k]
      have h12 := testBit_and m1 m2 (chunk k l1)
      rw [hM] at h12
      obtain ⟨ht1, ht2⟩ := and_split h12.symm
      rw [ht1, ht2, Bool.true_and, Bool.true_and]
    · simp only [Bool.not_eq_true] at hM
      rw [hM, Bool.false_and, and_pair_swap, ← testBit_and, hM, Bool.false_and]
  | case14 p1 l1 m1 k1 p2 l2 m2 k2 heq hnpfx =>
    intro hwf1 hwf2
    have hl : l1 = l2 := by simpa using heq
    subst hl
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
    have hpne : p1 ≠ p2 := by
      intro h; apply hnpfx; rw [hsk1, hsk2, h]; exact beq_self_eq_true p2
    refine ⟨by rw [meetU, if_pos heq, if_neg hnpfx, WF]; trivial, ?_⟩
    intro k
    rw [meetU, if_pos heq, if_neg hnpfx, contains_nil]
    exact (contains_binbin_pfxne k p1 l1 m1 k1 p2 m2 k2 hwf1 hwf2 hpne).symm
  | case15 p1 l1 m1 k1 p2 l2 m2 k2 hne hlt hcond h IH =>
    intro hwf1 hwf2
    have hwfchild := by rw [WF] at hwf1; exact hwf1.2.2.2.1 _ (Array.getElem_mem h)
    obtain ⟨hpfxb, htbb⟩ := and_split hcond
    have hpfxeq : prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 = p1 := by simpa using hpfxb
    have halign : AlignedAt l1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) p1 (.bin p2 l2 m2 k2) :=
      hpfxeq ▸ aligned_bin p2 l2 m2 k2 hwf2 l1 hlt
    have hcAc : childAt m1 k1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)
        = k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h := by
      unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
    have hmu : meetU cf (.bin p1 l1 m1 k1) (.bin p2 l2 m2 k2)
        = meetU cf (k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h) (.bin p2 l2 m2 k2) := by
      rw [meetU, if_neg hne, if_pos hlt, if_pos hcond, dif_pos h]
    obtain ⟨ihwf, ihc⟩ := IH hwfchild hwf2
    rw [hmu]
    refine ⟨ihwf, ?_⟩
    intro k
    rw [ihc k, ← hcAc]
    exact contains_meet_descend_left k p1 l1 m1 k1 (.bin p2 l2 m2 k2)
      (chunk (someKey (.bin p2 l2 m2 k2)) l1) p1 halign htbb
  | case16 p1 l1 m1 k1 p2 l2 m2 k2 hne hlt hcond hnh =>
    intro hwf1 _
    obtain ⟨_, htbb⟩ := and_split hcond
    have hsize : k1.size = popCount m1 := by rw [WF] at hwf1; exact hwf1.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt m1 _ htbb) hnh
  | case17 p1 l1 m1 k1 p2 l2 m2 k2 hne hlt hncond =>
    intro hwf1 hwf2
    have hcondf : ((prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 == p1)
        && testBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)) = false := by simpa using hncond
    have halign : AlignedAt l1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)
        (prefixAbove (someKey (.bin p2 l2 m2 k2)) l1) (.bin p2 l2 m2 k2) :=
      aligned_bin p2 l2 m2 k2 hwf2 l1 hlt
    refine ⟨by rw [meetU, if_neg hne, if_pos hlt, if_neg hncond, WF]; trivial, ?_⟩
    intro k
    rw [meetU, if_neg hne, if_pos hlt, if_neg hncond, contains_nil,
        Bool.and_comm (contains k (.bin p1 l1 m1 k1)) (contains k (.bin p2 l2 m2 k2))]
    exact (contains_div_eq_false k p1 l1 m1 k1 (.bin p2 l2 m2 k2)
      (chunk (someKey (.bin p2 l2 m2 k2)) l1) (prefixAbove (someKey (.bin p2 l2 m2 k2)) l1)
      hwf1 halign hcondf).symm
  | case18 p1 l1 m1 k1 p2 l2 m2 k2 hne hnlt hcond h IH =>
    intro hwf1 hwf2
    have hl12 : l1 < l2 := by
      have hlne : l1 ≠ l2 := by intro he; exact hne (by rw [he]; exact beq_self_eq_true l2)
      omega
    have hwfchild := by rw [WF] at hwf2; exact hwf2.2.2.2.1 _ (Array.getElem_mem h)
    obtain ⟨hpfxb, htbb⟩ := and_split hcond
    have hpfxeq : prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 = p2 := by simpa using hpfxb
    have halign : AlignedAt l2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) p2 (.bin p1 l1 m1 k1) :=
      hpfxeq ▸ aligned_bin p1 l1 m1 k1 hwf1 l2 hl12
    have hcAc : childAt m2 k2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)
        = k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h := by
      unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
    have hmu : meetU cf (.bin p1 l1 m1 k1) (.bin p2 l2 m2 k2)
        = meetU cf (.bin p1 l1 m1 k1) (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h) := by
      rw [meetU, if_neg hne, if_neg hnlt, if_pos hcond, dif_pos h]
    obtain ⟨ihwf, ihc⟩ := IH hwf1 hwfchild
    rw [hmu]
    refine ⟨ihwf, ?_⟩
    intro k
    rw [ihc k, ← hcAc]
    exact contains_meet_descend_right k p2 l2 m2 k2 (.bin p1 l1 m1 k1)
      (chunk (someKey (.bin p1 l1 m1 k1)) l2) p2 halign htbb
  | case19 p1 l1 m1 k1 p2 l2 m2 k2 hne hnlt hcond hnh =>
    intro _ hwf2
    obtain ⟨_, htbb⟩ := and_split hcond
    have hsize : k2.size = popCount m2 := by rw [WF] at hwf2; exact hwf2.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt m2 _ htbb) hnh
  | case20 p1 l1 m1 k1 p2 l2 m2 k2 hne hnlt hncond =>
    intro hwf1 hwf2
    have hl12 : l1 < l2 := by
      have hlne : l1 ≠ l2 := by intro he; exact hne (by rw [he]; exact beq_self_eq_true l2)
      omega
    have hcondf : ((prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 == p2)
        && testBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)) = false := by simpa using hncond
    have halign : AlignedAt l2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)
        (prefixAbove (someKey (.bin p1 l1 m1 k1)) l2) (.bin p1 l1 m1 k1) :=
      aligned_bin p1 l1 m1 k1 hwf1 l2 hl12
    refine ⟨by rw [meetU, if_neg hne, if_neg hnlt, if_neg hncond, WF]; trivial, ?_⟩
    intro k
    rw [meetU, if_neg hne, if_neg hnlt, if_neg hncond, contains_nil]
    exact (contains_div_eq_false k p2 l2 m2 k2 (.bin p1 l1 m1 k1)
      (chunk (someKey (.bin p1 l1 m1 k1)) l2) (prefixAbove (someKey (.bin p1 l1 m1 k1)) l2)
      hwf2 halign hcondf).symm
  | case21 m1 k1 m2 k2 rem acc hrem =>
    rename_i _ _ _ c hc htb
    have hr0 : rem = 0 := by simpa using hrem
    rw [hr0, testBit_zero] at htb; exact absurd htb (by decide)
  | case22 m1 k1 m2 k2 rem acc hrem IHchild IHrec =>
    rename_i hkw1 hkw2 hpre c hc htb
    have hrem0 : rem ≠ 0 := by intro h; exact hrem (by rw [h]; rfl)
    by_cases hclo : c = lowestSetIdx rem
    · subst hclo
      have hpr := hpre (lowestSetIdx rem) (lowestSetIdx_lt rem hrem0) (testBit_lowestSetIdx rem hrem0)
      exact IHchild hkw1 hkw2 hpr.1 hpr.2
    · have htb' : testBit (clearLowest rem) c = true := by
        rw [testBit_clearLowest_of_ne rem c hc hclo]; exact htb
      exact IHrec hkw1 hkw2
        (fun c' hc' h' => hpre c' hc' (testBit_of_clearLowest rem c' h')) c hc htb'
  | case23 m1 k1 m2 k2 i h1 h2 IH =>
    rename_i hkw1 hkw2 _ _
    have hwf1 := hkw1.2.1 _ (Array.getElem_mem h1)
    have hwf2 := hkw2.2.1 _ (Array.getElem_mem h2)
    have hc1 : childAt m1 k1 i = k1[arrayIndex m1 i]'h1 := by
      unfold childAt; rw [Array.getElem?_eq_getElem h1, Option.getD_some]
    have hc2 : childAt m2 k2 i = k2[arrayIndex m2 i]'h2 := by
      unfold childAt; rw [Array.getElem?_eq_getElem h2, Option.getD_some]
    have hmc : meetChild cf m1 k1 m2 k2 i = meetU cf (k1[arrayIndex m1 i]'h1) (k2[arrayIndex m2 i]'h2) := by
      rw [meetChild, dif_pos h1, dif_pos h2]
    obtain ⟨ihwf, ihc⟩ := IH hwf1 hwf2
    rw [hmc, hc1, hc2]
    exact ⟨ihwf, ihc⟩
  | case24 m1 k1 m2 k2 i h1 hnh2 =>
    rename_i _ hkw2 _ ht2
    exact absurd (by rw [hkw2.1]; exact arrayIndex_lt m2 i ht2) hnh2
  | case25 m1 k1 m2 k2 i hnh1 =>
    rename_i hkw1 _ ht1 _
    exact absurd (by rw [hkw1.1]; exact arrayIndex_lt m1 i ht1) hnh1

/-- `get?_meet` for the set: membership after `meet` is membership in both operands — the seam the
intersection lattice/order suite routes through. -/
theorem contains_meet (cf : V → V → V) (j : Nat) (a b : PTree L) (hwa : WF a) (hwb : WF b) :
    contains j (meet cf a b) = (contains j a && contains j b) := by
  rw [meet]; exact (meet_WF_contains cf a b hwa hwb).2 j

/-- `meet` keeps the canonical shape. -/
theorem WF_meet (cf : V → V → V) (a b : PTree L) (hwa : WF a) (hwb : WF b) : WF (meet cf a b) := by
  rw [meet]; exact (meet_WF_contains cf a b hwa hwb).1

/-! ### Extensionality

A well-formed tree is determined by its `get?` denotation: two `WF` trees that read identically at
every key are equal (`ext_get?`). This lifts the `get?_*`/`contains_*` seams to structural
equalities, the bridge the lattice/order laws cross. The key-set alone (`contains`) already pins a
tree's *shape* — its `nil`/`tip`/`bin` structure and a `bin`'s level/prefix/mask/children — so that
machinery is leaf-agnostic and stated on `contains`; only the final `tip`-vs-`tip` step needs the
leaf's full value denotation (via `LeafOps.get?_ext`), which is why the top-level theorem is
`get?`-based rather than `contains`-based (two maps can share a key-set yet differ in values). -/

/-- A concrete member key: descend to the first child of every `bin`, then read a leaf's
representative slot (`someSlot`). Unlike `someKey` (which zeroes the bits below a node's level — only
a prefix probe), this follows a real path to a leaf, so a `WF` tree genuinely contains it. -/
private def witnessKey : PTree L → Nat
  | .nil => 0
  | .tip pfx leaf => (LeafOps.someSlot leaf).toNat + 32 * pfx
  | .bin _ _ _ kids => if h : 0 < kids.size then witnessKey (kids[0]'h) else 0
decreasing_by
  simp_wf
  rename_i h
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem h)
  omega

/-- Adding a multiple of 32 leaves the bottom chunk unchanged. -/
private theorem chunk_zero_add_mul (a b : Nat) : chunk (a + 32 * b) 0 = chunk a 0 := by
  rw [chunk0_eq, chunk0_eq, Nat.add_mul_mod_self_left]

/-- `witnessKey` names a real member of any well-formed non-empty tree: a leaf's representative slot,
or (recursively) a member of a `bin`'s first child — which routes back to that child by alignment. -/
private theorem contains_witnessKey :
    ∀ (t : PTree L), WF t → t ≠ .nil → contains (witnessKey t) t = true := by
  intro t
  induction t using witnessKey.induct with
  | case1 => intro _ hne; exact absurd rfl hne
  | case2 pfx leaf =>
    intro hwf _
    have hb : LeafOps.isEmpty leaf = false := by rw [WF] at hwf; exact hwf
    have hlo : (LeafOps.someSlot leaf).toNat < 32 := by
      have h := UInt32.lt_iff_toNat_lt.mp (LeafOps.someSlot_lt leaf hb)
      rwa [show (32 : UInt32).toNat = 32 from by decide] at h
    rw [contains_tip, Bool.and_eq_true, beq_iff_eq, witnessKey]
    refine ⟨?_, ?_⟩
    · rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 5 = 32 from rfl,
          Nat.add_mul_div_left _ _ (by decide : 0 < 32), Nat.div_eq_of_lt hlo, Nat.zero_add]
    · rw [chunk_zero_add_mul, chunk_toNat_zero _ (LeafOps.someSlot_lt leaf hb)]
      exact LeafOps.contains_someSlot leaf hb
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
theorem exists_mem (t : PTree L) (hwf : WF t) (hne : t ≠ .nil) : ∃ j, contains j t = true :=
  ⟨witnessKey t, contains_witnessKey t hwf hne⟩

/-- The converse: a well-formed tree with no members is `nil`. The `nil` half of `ext`. -/
theorem eq_nil_of_no_member (t : PTree L) (hwf : WF t) (h : ∀ j, contains j t = false) :
    t = .nil := by
  cases t with
  | nil => rfl
  | tip pfx leaf =>
    have hpos := contains_witnessKey _ hwf (by simp)
    rw [h] at hpos; exact absurd hpos (by decide)
  | bin pfx level mask kids =>
    have hpos := contains_witnessKey _ hwf (by simp)
    rw [h] at hpos; exact absurd hpos (by decide)

/-- A present slot's child sits in the `kids` array (it is read at an in-range compact index). -/
private theorem childAt_mem (mask : UInt32) (kids : Array (PTree L)) (c : UInt32)
    (hsize : kids.size = popCount mask) (htb : testBit mask c = true) :
    childAt mask kids c ∈ kids := by
  have hidx : arrayIndex mask c < kids.size := by rw [hsize]; exact arrayIndex_lt mask c htb
  have he : childAt mask kids c = kids[arrayIndex mask c]'hidx := by
    unfold childAt; rw [Array.getElem?_eq_getElem hidx, Option.getD_some]
  rw [he]; exact Array.getElem_mem hidx

/-- Every key in a well-formed `bin` carries the branch prefix. -/
private theorem prefixAbove_eq_of_mem (p l : Nat) (m : UInt32) (k : Array (PTree L))
    (hwf : WF (.bin p l m k)) (j : Nat) (hj : contains j (.bin p l m k) = true) :
    prefixAbove j l = p := by
  rw [WF] at hwf
  obtain ⟨_, _, _, _, _, hrout⟩ := hwf
  rw [contains_bin, Bool.and_eq_true] at hj
  obtain ⟨htb, hcc⟩ := hj
  exact (hrout (chunk j l) (chunk_lt _ _) htb j hcc).2

/-- A key contained in a present slot's child is contained in the `bin`: it routes back to that
slot (its chunk equals `c` by alignment). -/
private theorem mem_child_imp_mem_bin (p l : Nat) (m : UInt32) (k : Array (PTree L))
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
private theorem exists_two_divergent (p l : Nat) (m : UInt32) (k : Array (PTree L))
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
private theorem not_lt_level (pA lA : Nat) (mA : UInt32) (kA : Array (PTree L))
    (pB lB : Nat) (mB : UInt32) (kB : Array (PTree L))
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
private theorem mask_testBit_imp (pA l : Nat) (mA : UInt32) (kA : Array (PTree L))
    (pB : Nat) (mB : UInt32) (kB : Array (PTree L))
    (hwa : WF (.bin pA l mA kA)) (_hwb : WF (.bin pB l mB kB))
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

/-- An aligned subtree reads `none` at a key that routes away from its slot — the `get?` shadow of
`contains_false_of_aligned`, for the off-slot child recursion in `ext_get?`. -/
private theorem get?_none_of_aligned {j : Nat} (l : Nat) (c : UInt32) (p : Nat) (t : PTree L)
    (h : AlignedAt l c p t) (hj : chunk j l ≠ c) : get? j t = none := by
  have hcf := contains_false_of_aligned l c p t h hj
  rw [contains_eq_isSome] at hcf
  cases hg : get? j t with
  | none => rfl
  | some v => rw [hg] at hcf; simp at hcf

/-- A "probe" key targeting slot `c`: prefix `p`, bottom chunk `c`. Its lookup in `tip p leaf` reads
exactly the leaf's slot `c` — the per-slot lever that recovers a tip's leaf from its denotation. -/
private theorem get?_tip_probe (p : Nat) (leaf : L) (c : UInt32) (hc : c < 32) :
    get? (c.toNat + 32 * p) (.tip p leaf) = LeafOps.get? leaf c := by
  have hclt : c.toNat < 32 := by
    have := UInt32.lt_iff_toNat_lt.mp hc; rwa [show (32 : UInt32).toNat = 32 from by decide] at this
  have hpre : (c.toNat + 32 * p) >>> 5 = p := by
    rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 5 = 32 from rfl,
        Nat.add_mul_div_left _ _ (by decide : 0 < 32), Nat.div_eq_of_lt hclt, Nat.zero_add]
  have hch : chunk (c.toNat + 32 * p) 0 = c := by rw [chunk_zero_add_mul, chunk_toNat_zero _ hc]
  rw [get?_tip, hpre, hch]; simp

/-- Same key set + same level/prefix/mask ⇒ matching present children read identically: a key routes
to slot `c` in both, or to neither (alignment reads `none`). Drives the per-child recursion. -/
private theorem child_get?_eq (p l : Nat) (m : UInt32) (kA kB : Array (PTree L))
    (hwa : WF (.bin p l m kA)) (hwb : WF (.bin p l m kB))
    (h : ∀ j, get? j (.bin p l m kA) = get? j (.bin p l m kB))
    (c : UInt32) (hc : c < 32) (htb : testBit m c = true) (x : Nat) :
    get? x (childAt m kA c) = get? x (childAt m kB c) := by
  by_cases hcx : chunk x l = c
  · have eA : get? x (.bin p l m kA) = get? x (childAt m kA c) := by
      rw [get?_bin, hcx, if_pos htb]
    have eB : get? x (.bin p l m kB) = get? x (childAt m kB c) := by
      rw [get?_bin, hcx, if_pos htb]
    rw [← eA, ← eB, h]
  · have hwa' := hwa; rw [WF] at hwa'
    have hwb' := hwb; rw [WF] at hwb'
    obtain ⟨_, _, _, _, _, hroutA⟩ := hwa'
    obtain ⟨_, _, _, _, _, hroutB⟩ := hwb'
    rw [get?_none_of_aligned l c p _ (hroutA c hc htb) hcx,
        get?_none_of_aligned l c p _ (hroutB c hc htb) hcx]

/-- **Extensionality** (`get?` form): two well-formed trees with the same lookup at every key are
equal. The keystone that lifts the `get?_*`/`contains_*` seams to structural equalities, so the
lattice/order laws reduce to matching denotations pointwise. By recursion on `a`: `nil` pins by
`eq_nil_of_no_member`; a `tip` vs a `bin` is impossible (a `bin` diverges, a `tip` does not); two
`tip`s share prefix (a member's key) and leaf (`LeafOps.get?_ext`); two `bin`s share level, prefix,
mask (`not_lt_level`/`mask_testBit_imp`) and then, child by child, recurse. -/
theorem ext_get? (a b : PTree L) (hwa : WF a) (hwb : WF b)
    (h : ∀ j, get? j a = get? j b) : a = b := by
  match a, b, hwa, hwb, h with
  | .nil, b, _, hwb, h =>
    refine (eq_nil_of_no_member b hwb (fun j => ?_)).symm
    have hj : get? j b = none := (h j).symm.trans (get?_nil j)
    simp [contains_eq_isSome, hj]
  | .tip p1 b1, .nil, hwa, _, h =>
    refine eq_nil_of_no_member _ hwa (fun j => ?_)
    have hj : get? j (.tip p1 b1) = none := (h j).trans (get?_nil j)
    simp [contains_eq_isSome, hj]
  | .bin p1 l1 m1 k1, .nil, hwa, _, h =>
    refine eq_nil_of_no_member _ hwa (fun j => ?_)
    have hj : get? j (.bin p1 l1 m1 k1) = none := (h j).trans (get?_nil j)
    simp [contains_eq_isSome, hj]
  | .tip p1 b1, .bin p2 l2 m2 k2, hwa, hwb, h =>
    exfalso
    have hcont : ∀ j, contains j (.tip p1 b1) = contains j (.bin p2 l2 m2 k2) :=
      fun j => by rw [contains_eq_isSome, contains_eq_isSome, h j]
    obtain ⟨j1, j2, hj1, hj2, hne⟩ := exists_two_divergent p2 l2 m2 k2 hwb
    have hj1a : contains j1 (.tip p1 b1) = true := by rw [hcont]; exact hj1
    have hj2a : contains j2 (.tip p1 b1) = true := by rw [hcont]; exact hj2
    rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hj1a hj2a
    have hbl0 : 0 < l2 := by rw [WF] at hwb; exact hwb.1
    apply hne
    apply chunk_eq_of_shiftRight_eq
    exact shiftRight_mono_eq (hj1a.1.trans hj2a.1.symm) (by omega)
  | .bin p1 l1 m1 k1, .tip p2 b2, hwa, hwb, h =>
    exfalso
    have hcont : ∀ j, contains j (.bin p1 l1 m1 k1) = contains j (.tip p2 b2) :=
      fun j => by rw [contains_eq_isSome, contains_eq_isSome, h j]
    obtain ⟨j1, j2, hj1, hj2, hne⟩ := exists_two_divergent p1 l1 m1 k1 hwa
    have hj1b : contains j1 (.tip p2 b2) = true := by rw [← hcont]; exact hj1
    have hj2b : contains j2 (.tip p2 b2) = true := by rw [← hcont]; exact hj2
    rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hj1b hj2b
    have hbl0 : 0 < l1 := by rw [WF] at hwa; exact hwa.1
    apply hne
    apply chunk_eq_of_shiftRight_eq
    exact shiftRight_mono_eq (hj1b.1.trans hj2b.1.symm) (by omega)
  | .tip p1 b1, .tip p2 b2, hwa, hwb, h =>
    have hcont : ∀ j, contains j (.tip p1 b1) = contains j (.tip p2 b2) :=
      fun j => by rw [contains_eq_isSome, contains_eq_isSome, h j]
    have hp : p1 = p2 := by
      obtain ⟨j, hj⟩ := exists_mem (.tip p1 b1) hwa (by simp)
      have hjb : contains j (.tip p2 b2) = true := by rw [← hcont]; exact hj
      rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hj hjb
      rw [← hj.1, ← hjb.1]
    subst hp
    have hbits : b1 = b2 := by
      apply LeafOps.get?_ext
      intro c hcc
      rw [← get?_tip_probe p1 b1 c hcc, ← get?_tip_probe p1 b2 c hcc, h]
    rw [hbits]
  | .bin p1 l1 m1 k1, .bin p2 l2 m2 k2, hwa, hwb, h =>
    have hcont : ∀ j, contains j (.bin p1 l1 m1 k1) = contains j (.bin p2 l2 m2 k2) :=
      fun j => by rw [contains_eq_isSome, contains_eq_isSome, h j]
    have hl : l1 = l2 := by
      have h1 := not_lt_level p1 l1 m1 k1 p2 l2 m2 k2 hwa hwb hcont
      have h2 := not_lt_level p2 l2 m2 k2 p1 l1 m1 k1 hwb hwa (fun j => (hcont j).symm)
      omega
    subst hl
    have hp : p1 = p2 := by
      obtain ⟨j, hj⟩ := exists_mem (.bin p1 l1 m1 k1) hwa (by simp)
      have hjb : contains j (.bin p2 l1 m2 k2) = true := by rw [← hcont]; exact hj
      rw [← prefixAbove_eq_of_mem p1 l1 m1 k1 hwa j hj,
          ← prefixAbove_eq_of_mem p2 l1 m2 k2 hwb j hjb]
    subst hp
    have hm : m1 = m2 := by
      apply eq_of_testBit_eq
      intro c hc
      have d1 := mask_testBit_imp p1 l1 m1 k1 p1 m2 k2 hwa hwb hcont c hc
      have d2 := mask_testBit_imp p1 l1 m2 k2 p1 m1 k1 hwb hwa (fun j => (hcont j).symm) c hc
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
        refine ext_get? (k1[i]'hi1) (k2[i]'hi2) (hkidswfA _ (Array.getElem_mem hi1))
          (hkidswfB _ (Array.getElem_mem hi2)) ?_
        intro x
        rw [hk1, hk2]
        exact child_get?_eq p1 l1 m1 k1 k2 hwa hwb h c hc htb x
    rw [hk]
termination_by sizeOf a
decreasing_by
  simp_wf
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem hi1)
  omega

/-! ### The `get?` value seams

The map-facing companions to the `contains_*` seams: where `contains` reads key-presence, `get?`
reads the stored value. Each mirrors its `contains` cousin's routing but tracks values through the
leaf (`LeafOps.get?_*`) and the disjoint branch `join`. With `ext_get?`, these are the single point
of contact between the map lattice/order laws and the representation. -/

/-- Leaf lookup of a singleton: the one inserted slot reads its value, all others read `none`. -/
private theorem leaf_get?_singleton (i j : UInt32) (v : V) (hi : i < 32) (hj : j < 32) :
    LeafOps.get? (LeafOps.insert (LeafOps.empty : L) i v) j = if j = i then some v else none := by
  rw [LeafOps.get?_insert LeafOps.empty i j v hi hj]
  by_cases h : j = i
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, LeafOps.get?_empty]

/-- Lookup of a singleton: `k` reads `v`, every other key reads `none`. -/
theorem get?_singleton (j k : Nat) (v : V) :
    get? j (singleton k v : PTree L) = if j == k then some v else none := by
  rw [singleton, get?_tip,
      leaf_get?_singleton (chunk k 0) (chunk j 0) v (chunk_lt _ _) (chunk_lt _ _)]
  by_cases hjk : j = k
  · subst hjk; simp
  · have hjkne : ¬ (j == k) = true := by rw [beq_iff_eq]; exact hjk
    rw [if_neg hjkne]
    by_cases h5 : (j >>> 5 == k >>> 5) = true
    · rw [if_pos h5]
      by_cases h0 : chunk j 0 = chunk k 0
      · exact absurd ((key_eq_iff j k).mpr ⟨by rw [beq_iff_eq] at h5; exact h5, h0⟩) hjk
      · rw [if_neg h0]
    · rw [if_neg h5]

/-- Lookup in a disjoint branch `join` (two subtrees aligned to different slots): a key in the first
operand reads there, else it reads the second — the `get?` shadow of `contains_join`. -/
theorem get?_join (j p l : Nat) (ca cb : UInt32) (a b : PTree L)
    (hca : ca < 32) (hcb : cb < 32) (hne : ca ≠ cb)
    (ha : AlignedAt l ca p a) (hb : AlignedAt l cb p b) :
    get? j (.bin p l (setBit (setBit 0 ca) cb) (if ca < cb then #[a, b] else #[b, a]))
      = (get? j a).orElse (fun _ => get? j b) := by
  rw [get?_bin, testBit_join_mask ca cb (chunk j l) hca hcb (chunk_lt j l)]
  by_cases hjca : chunk j l = ca
  · have hcond : ((ca == chunk j l) || (cb == chunk j l)) = true := by
      rw [hjca, beq_self_eq_true, Bool.true_or]
    rw [if_pos hcond, hjca, childAt_join_ca ca cb a b hca hcb hne]
    have hjb : get? j b = none := get?_none_of_aligned l cb p b hb (by rw [hjca]; exact hne)
    rw [hjb]; cases get? j a <;> rfl
  · by_cases hjcb : chunk j l = cb
    · have hcond : ((ca == chunk j l) || (cb == chunk j l)) = true := by
        rw [hjcb, beq_self_eq_true, Bool.or_true]
      rw [if_pos hcond, hjcb, childAt_join_cb ca cb a b hca hcb hne]
      have hja : get? j a = none :=
        get?_none_of_aligned l ca p a ha (by rw [hjcb]; exact fun h => hne h.symm)
      rw [hja]; rfl
    · have hcond : ((ca == chunk j l) || (cb == chunk j l)) = false := by
        rw [beq_eq_false_iff_ne.mpr (Ne.symm hjca), beq_eq_false_iff_ne.mpr (Ne.symm hjcb),
            Bool.or_false]
      rw [if_neg (by rw [hcond]; exact Bool.false_ne_true)]
      have hja : get? j a = none := get?_none_of_aligned l ca p a ha hjca
      have hjb : get? j b = none := get?_none_of_aligned l cb p b hb hjcb
      rw [hja, hjb]; rfl

/-- Lookup in a `join`, stated directly on the `join` builder (the `get?` cousin of
`contains_join_eq`). -/
theorem get?_join_eq (j ka kb : Nat) (a b : PTree L) (hne : ka ≠ kb)
    (ha : AlignedAt (branchLevel ka kb) (chunk ka (branchLevel ka kb))
            (prefixAbove ka (branchLevel ka kb)) a)
    (hb : AlignedAt (branchLevel ka kb) (chunk kb (branchLevel ka kb))
            (prefixAbove ka (branchLevel ka kb)) b) :
    get? j (join ka a kb b) = (get? j a).orElse (fun _ => get? j b) := by
  rw [join]
  exact get?_join j (prefixAbove ka (branchLevel ka kb)) (branchLevel ka kb)
    (chunk ka (branchLevel ka kb)) (chunk kb (branchLevel ka kb)) a b
    (chunk_lt _ _) (chunk_lt _ _) (chunk_branchLevel_ne ka kb hne) ha hb

set_option linter.unusedVariables false in
/-- `get?_insert`: the value after `insert k v` reads `v` at `k` and is unchanged elsewhere. The
map-facing point of contact between the lattice/order proofs and `insert`'s structural code. -/
theorem get?_insert (k j : Nat) (v : V) :
    ∀ (t : PTree L), WF t → get? j (insert k v t) = if j == k then some v else get? j t := by
  intro t
  induction t using insert.induct (k := k) with
  | case1 =>
    intro _
    rw [insert, get?_singleton, get?_nil]
  | case2 pfx leaf hmatch =>
    intro _
    have hk5 : k >>> 5 = pfx := by simpa using hmatch
    rw [insert, if_pos hmatch, get?_tip, get?_tip,
        LeafOps.get?_insert leaf (chunk k 0) (chunk j 0) v (chunk_lt _ _) (chunk_lt _ _)]
    by_cases hp5 : (j >>> 5 == pfx) = true
    · have hjeq5 : j >>> 5 = k >>> 5 := by rw [beq_iff_eq] at hp5; rw [hp5, hk5]
      rw [if_pos hp5]
      by_cases hc0 : chunk j 0 = chunk k 0
      · have hjk : j = k := (key_eq_iff j k).mpr ⟨hjeq5, hc0⟩
        have hjkt : (j == k) = true := by rw [hjk]; exact beq_self_eq_true k
        rw [if_pos hc0, if_pos hjkt]
      · have hjkf : ¬ (j == k) = true := by rw [beq_iff_eq]; intro he; exact hc0 (by rw [he])
        rw [if_neg hc0, if_neg hjkf, if_pos hp5]
    · have hjkf : ¬ (j == k) = true := by
        rw [beq_iff_eq]; intro he; subst he
        exact hp5 (by rw [hk5]; exact beq_self_eq_true pfx)
      rw [if_neg hp5, if_neg hjkf, if_neg hp5]
  | case3 pfx leaf hmatch =>
    intro hwf
    have hleaf : LeafOps.isEmpty leaf = false := by rw [WF] at hwf; exact hwf
    have hsk : someKey (.tip pfx leaf) >>> 5 = pfx := someKey_tip_shiftRight5 pfx leaf hleaf
    have hkne5 : k >>> 5 ≠ someKey (.tip pfx leaf) >>> 5 := by
      rw [hsk]; intro h; exact hmatch (by rw [h]; exact beq_self_eq_true pfx)
    have hkne : k ≠ someKey (.tip pfx leaf) := fun h => hkne5 (by rw [h])
    rw [insert, if_neg hmatch,
        show ((pfx <<< 5) ||| (LeafOps.someSlot leaf).toNat) = someKey (.tip pfx leaf) from rfl,
        get?_join_eq j k (someKey (.tip pfx leaf)) (singleton k v) (.tip pfx leaf) hkne ?ha ?hb,
        get?_singleton]
    case ha =>
      intro k' hk'; rw [show k' = k from (contains_singleton k' k v).mp hk']; exact ⟨rfl, rfl⟩
    case hb =>
      rw [prefixAbove_branchLevel_eq k (someKey (.tip pfx leaf))]
      exact aligned_tip pfx leaf hleaf _ (branchLevel_pos k _ hkne5)
    by_cases hjk : (j == k) = true
    · rw [if_pos hjk, if_pos hjk]; rfl
    · rw [if_neg hjk, if_neg hjk]; rfl
  | case4 pfx level mask kids hpfx htb h IH =>
    intro hwf
    rw [WF] at hwf
    obtain ⟨_, hsize, _, hkidswf, _⟩ := hwf
    have hwfchild : WF kids[arrayIndex mask (chunk k level)] := hkidswf _ (Array.getElem_mem h)
    have hclt : chunk k level < 32 := chunk_lt k level
    have hcjlt : chunk j level < 32 := chunk_lt j level
    have hcAc : childAt mask kids (chunk k level) = kids[arrayIndex mask (chunk k level)] := by
      unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
    rw [insert, if_pos hpfx, if_pos htb, dif_pos h, get?_bin, get?_bin]
    by_cases hcjc : chunk j level = chunk k level
    · rw [hcjc,
          childAt_setIfInBounds mask (chunk k level) (chunk k level) kids _ hclt hclt htb htb hsize,
          if_pos rfl, IH hwfchild, hcAc, if_pos htb, if_pos htb]
    · have hjkf : ¬ (j == k) = true := by rw [beq_iff_eq]; intro he; exact hcjc (by rw [he])
      rw [if_neg hjkf]
      by_cases htcj : testBit mask (chunk j level) = true
      · rw [if_pos htcj, if_pos htcj,
            childAt_setIfInBounds mask (chunk k level) (chunk j level) kids _ hclt hcjlt htb htcj hsize,
            if_neg hcjc]
      · have htcjf : ¬ testBit mask (chunk j level) = true := by simpa using htcj
        rw [if_neg htcjf, if_neg htcjf]
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
    rw [insert, if_pos hpfx, if_neg htb, get?_bin, get?_bin]
    by_cases hcjc : chunk j level = chunk k level
    · have hcondL : testBit (setBit mask (chunk k level)) (chunk j level) = true := by
        rw [hcjc, testBit_setBit mask (chunk k level) (chunk k level) hclt hclt,
            beq_self_eq_true, Bool.or_true]
      rw [if_pos hcondL, hcjc,
          childAt_insertIdx_self mask (chunk k level) kids (singleton k v) hsize, get?_singleton,
          if_neg (show ¬ testBit mask (chunk k level) = true by rw [htbf]; exact Bool.false_ne_true)]
    · have hjkf : ¬ (j == k) = true := by rw [beq_iff_eq]; intro he; exact hcjc (by rw [he])
      have hcondL : testBit (setBit mask (chunk k level)) (chunk j level)
          = testBit mask (chunk j level) := by
        rw [testBit_setBit mask (chunk k level) (chunk j level) hclt hcjlt,
            beq_eq_false_iff_ne.mpr (fun he => hcjc he.symm), Bool.or_false]
      rw [if_neg hjkf, hcondL]
      by_cases htcj : testBit mask (chunk j level) = true
      · rw [if_pos htcj, if_pos htcj,
            childAt_insertIdx_of_ne mask (chunk k level) (chunk j level) kids (singleton k v)
              hclt hcjlt hcjc htbf htcj hsize]
      · have htcjf : ¬ testBit mask (chunk j level) = true := by simpa using htcj
        rw [if_neg htcjf, if_neg htcjf]
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
        get?_join_eq j k (someKey (.bin pfx level mask kids)) (singleton k v)
          (.bin pfx level mask kids) hkne ?ha ?hb, get?_singleton]
    case ha =>
      intro k' hk'; rw [show k' = k from (contains_singleton k' k v).mp hk']; exact ⟨rfl, rfl⟩
    case hb =>
      rw [prefixAbove_branchLevel_eq k (someKey (.bin pfx level mask kids))]
      exact aligned_bin pfx level mask kids hwf _ (lt_branchLevel k _ level hkne5)
    by_cases hjk : (j == k) = true
    · rw [if_pos hjk, if_pos hjk]; rfl
    · rw [if_neg hjk, if_neg hjk]; rfl

/-! ### `get?_union` — the value-level union seam

`get?` of a `unionU` is the value-level join (`optVjoin`) of the two lookups: present on both →
combine with `cf`, present on one → copy. The map-facing companion of `contains_unionU`. The
operand *order* matters now (unlike the set, where `||` is symmetric): `cf` fires as
`cf left-value right-value`, so the descend/splice helpers come in child-first and op-first
flavours to keep that order faithful across taller-left vs taller-right descents. -/

/-- `optVjoin` collapses to `Option.orElse` when the two lookups are disjoint (the left is present
only where the right is absent). Lets the `join` cases reuse `get?_join_eq`'s `orElse` shape. -/
private theorem optVjoin_eq_orElse_left (cf : V → V → V) (oa ob : Option V)
    (h : oa.isSome = true → ob = none) : optVjoin cf oa ob = oa.orElse (fun _ => ob) := by
  cases oa with
  | none => cases ob with | none => rfl | some y => rfl
  | some x => cases ob with
    | none => rfl
    | some y => exact absurd (h rfl) (by simp)

/-- The mirror of `optVjoin_eq_orElse_left` for the swapped operand order: collapses to the second
operand's `orElse` when the first is present only where the second is absent. -/
private theorem optVjoin_eq_orElse_right (cf : V → V → V) (oa ob : Option V)
    (h : ob.isSome = true → oa = none) : optVjoin cf oa ob = ob.orElse (fun _ => oa) := by
  cases oa with
  | none => cases ob with | none => rfl | some y => rfl
  | some x => cases ob with
    | none => rfl
    | some y => exact absurd (h rfl) (by simp)

/-- `optVjoin` with `none` on the left is the right operand (the `none, oy => oy` arm), stated as a
rewrite so the disjoint-merge cases close syntactically. -/
private theorem optVjoin_none_left (cf : V → V → V) (oy : Option V) :
    optVjoin cf none oy = oy := rfl

/-- A disjoint branch `join` reads as the `optVjoin` of the two operands (the value-level cousin of
`get?_join_eq`): the operands route to different slots, so at most one is present at any key. -/
private theorem get?_join_optVjoin (cf : V → V → V) (j ka kb : Nat) (a b : PTree L) (hne : ka ≠ kb)
    (ha : AlignedAt (branchLevel ka kb) (chunk ka (branchLevel ka kb))
            (prefixAbove ka (branchLevel ka kb)) a)
    (hb : AlignedAt (branchLevel ka kb) (chunk kb (branchLevel ka kb))
            (prefixAbove ka (branchLevel ka kb)) b) :
    get? j (join ka a kb b) = optVjoin cf (get? j a) (get? j b) := by
  rw [get?_join_eq j ka kb a b hne ha hb]
  refine (optVjoin_eq_orElse_left cf (get? j a) (get? j b) ?_).symm
  intro hsome
  have hcon : contains j a = true := by rw [contains_eq_isSome]; exact hsome
  exact get?_none_of_aligned (branchLevel ka kb) (chunk kb (branchLevel ka kb))
    (prefixAbove ka (branchLevel ka kb)) b hb (by rw [(ha j hcon).1]; exact chunk_branchLevel_ne ka kb hne)

/-- `get?_join_optVjoin` with the conclusion's operands swapped, for the `unionU` quadrants whose
`join` builder lists the operands opposite to the theorem's `a b` (the taller operand goes first). -/
private theorem get?_join_optVjoin_swap (cf : V → V → V) (j ka kb : Nat) (a b : PTree L) (hne : ka ≠ kb)
    (ha : AlignedAt (branchLevel ka kb) (chunk ka (branchLevel ka kb))
            (prefixAbove ka (branchLevel ka kb)) a)
    (hb : AlignedAt (branchLevel ka kb) (chunk kb (branchLevel ka kb))
            (prefixAbove ka (branchLevel ka kb)) b) :
    get? j (join ka a kb b) = optVjoin cf (get? j b) (get? j a) := by
  rw [get?_join_eq j ka kb a b hne ha hb]
  refine (optVjoin_eq_orElse_right cf (get? j b) (get? j a) ?_).symm
  intro hsome
  have hcon : contains j a = true := by rw [contains_eq_isSome]; exact hsome
  exact get?_none_of_aligned (branchLevel ka kb) (chunk kb (branchLevel ka kb))
    (prefixAbove ka (branchLevel ka kb)) b hb (by rw [(ha j hcon).1]; exact chunk_branchLevel_ne ka kb hne)

/-- Descend case (child-first) for `get?_union`: routing `op` into a *present* slot `c` overwrites
that child with `unionU child op`, so a key under `c` reads the recursive merge and every other key
reads the original `bin`. The `optVjoin` keeps the `bin` operand on the left (its values lead). -/
private theorem get?_descend (cf : V → V → V) (j : Nat) (op : PTree L) (bp bl : Nat) (bm : UInt32)
    (bk : Array (PTree L)) (c : UInt32) (hc : c < 32) (hbin : WF (.bin bp bl bm bk))
    (halign : AlignedAt bl c bp op) (htb : testBit bm c = true) (hidx : arrayIndex bm c < bk.size)
    (IH : get? j (unionU cf (bk[arrayIndex bm c]'hidx) op)
            = optVjoin cf (get? j (bk[arrayIndex bm c]'hidx)) (get? j op)) :
    get? j (.bin bp bl bm (bk.setIfInBounds (arrayIndex bm c) (unionU cf (bk[arrayIndex bm c]'hidx) op)))
      = optVjoin cf (get? j (.bin bp bl bm bk)) (get? j op) := by
  have hsize : bk.size = popCount bm := by rw [WF] at hbin; exact hbin.2.1
  have hcAc : childAt bm bk c = bk[arrayIndex bm c]'hidx := by
    unfold childAt; rw [Array.getElem?_eq_getElem hidx, Option.getD_some]
  rw [get?_bin, get?_bin]
  by_cases hcj : chunk j bl = c
  · rw [hcj, childAt_setIfInBounds bm c c bk _ hc hc htb htb hsize, if_pos rfl, if_pos htb, IH,
        if_pos htb, hcAc]
  · have htcjlt := chunk_lt j bl
    by_cases htcj : testBit bm (chunk j bl) = true
    · rw [childAt_setIfInBounds bm c (chunk j bl) bk _ hc htcjlt htb htcj hsize, if_neg hcj,
          if_pos htcj, get?_none_of_aligned bl c bp op halign hcj, optVjoin_none_right]
    · have htcjf : testBit bm (chunk j bl) = false := by simpa using htcj
      rw [if_neg (show ¬ testBit bm (chunk j bl) = true by rw [htcjf]; exact Bool.false_ne_true),
          if_neg (show ¬ testBit bm (chunk j bl) = true by rw [htcjf]; exact Bool.false_ne_true),
          get?_none_of_aligned bl c bp op halign hcj, optVjoin_none_left]

/-- The op-first mirror of `get?_descend`: when `op` is the *left* operand routed into the right
operand's `bin` (`unionU op child`), the `optVjoin` keeps `op`'s values leading. -/
private theorem get?_descend_left (cf : V → V → V) (j : Nat) (op : PTree L) (bp bl : Nat) (bm : UInt32)
    (bk : Array (PTree L)) (c : UInt32) (hc : c < 32) (hbin : WF (.bin bp bl bm bk))
    (halign : AlignedAt bl c bp op) (htb : testBit bm c = true) (hidx : arrayIndex bm c < bk.size)
    (IH : get? j (unionU cf op (bk[arrayIndex bm c]'hidx))
            = optVjoin cf (get? j op) (get? j (bk[arrayIndex bm c]'hidx))) :
    get? j (.bin bp bl bm (bk.setIfInBounds (arrayIndex bm c) (unionU cf op (bk[arrayIndex bm c]'hidx))))
      = optVjoin cf (get? j op) (get? j (.bin bp bl bm bk)) := by
  have hsize : bk.size = popCount bm := by rw [WF] at hbin; exact hbin.2.1
  have hcAc : childAt bm bk c = bk[arrayIndex bm c]'hidx := by
    unfold childAt; rw [Array.getElem?_eq_getElem hidx, Option.getD_some]
  rw [get?_bin, get?_bin]
  by_cases hcj : chunk j bl = c
  · rw [hcj, childAt_setIfInBounds bm c c bk _ hc hc htb htb hsize, if_pos rfl, if_pos htb, IH,
        if_pos htb, hcAc]
  · have htcjlt := chunk_lt j bl
    by_cases htcj : testBit bm (chunk j bl) = true
    · rw [childAt_setIfInBounds bm c (chunk j bl) bk _ hc htcjlt htb htcj hsize, if_neg hcj,
          if_pos htcj, get?_none_of_aligned bl c bp op halign hcj, optVjoin_none_left]
    · have htcjf : testBit bm (chunk j bl) = false := by simpa using htcj
      rw [if_neg (show ¬ testBit bm (chunk j bl) = true by rw [htcjf]; exact Bool.false_ne_true),
          if_neg (show ¬ testBit bm (chunk j bl) = true by rw [htcjf]; exact Bool.false_ne_true),
          get?_none_of_aligned bl c bp op halign hcj, optVjoin_none_left]

/-- Splice case (bin-first) for `get?_union`: routing `op` into an *absent* slot `c` inserts `op`
whole. No values combine — `op`'s keys (all under `c`) and the `bin`'s keys (under other slots) are
disjoint — so the lookup reads whichever side claims the key. -/
private theorem get?_splice (cf : V → V → V) (j : Nat) (op : PTree L) (bp bl : Nat) (bm : UInt32)
    (bk : Array (PTree L)) (c : UInt32) (hc : c < 32) (hbin : WF (.bin bp bl bm bk))
    (halign : AlignedAt bl c bp op) (htb : testBit bm c = false) :
    get? j (.bin bp bl (setBit bm c) (bk.insertIdx! (arrayIndex bm c) op))
      = optVjoin cf (get? j (.bin bp bl bm bk)) (get? j op) := by
  have hsize : bk.size = popCount bm := by rw [WF] at hbin; exact hbin.2.1
  rw [get?_bin, get?_bin]
  by_cases hcj : chunk j bl = c
  · subst hcj
    have hcondL : testBit (setBit bm (chunk j bl)) (chunk j bl) = true := by
      rw [testBit_setBit bm (chunk j bl) (chunk j bl) (chunk_lt j bl) (chunk_lt j bl),
          beq_self_eq_true, Bool.or_true]
    rw [if_pos hcondL, childAt_insertIdx_self bm (chunk j bl) bk op hsize,
        if_neg (show ¬ testBit bm (chunk j bl) = true by rw [htb]; exact Bool.false_ne_true),
        optVjoin_none_left]
  · have htcjlt := chunk_lt j bl
    by_cases htcj : testBit bm (chunk j bl) = true
    · have hcondL : testBit (setBit bm c) (chunk j bl) = testBit bm (chunk j bl) := by
        rw [testBit_setBit bm c (chunk j bl) hc htcjlt, beq_eq_false_iff_ne.mpr (Ne.symm hcj),
            Bool.or_false]
      rw [hcondL, if_pos htcj, if_pos htcj,
          childAt_insertIdx_of_ne bm c (chunk j bl) bk op hc htcjlt hcj htb htcj hsize,
          get?_none_of_aligned bl c bp op halign hcj, optVjoin_none_right]
    · have htcjf : testBit bm (chunk j bl) = false := by simpa using htcj
      have hcondL : testBit (setBit bm c) (chunk j bl) = false := by
        rw [testBit_setBit bm c (chunk j bl) hc htcjlt, beq_eq_false_iff_ne.mpr (Ne.symm hcj),
            htcjf, Bool.or_self]
      rw [if_neg (show ¬ testBit (setBit bm c) (chunk j bl) = true by rw [hcondL]; exact Bool.false_ne_true),
          if_neg (show ¬ testBit bm (chunk j bl) = true by rw [htcjf]; exact Bool.false_ne_true),
          get?_none_of_aligned bl c bp op halign hcj, optVjoin_none_left]

/-- The op-first mirror of `get?_splice`: `op` is the *left* operand spliced into the right operand's
`bin`, so the `optVjoin` keeps `op`'s values leading. -/
private theorem get?_splice_left (cf : V → V → V) (j : Nat) (op : PTree L) (bp bl : Nat) (bm : UInt32)
    (bk : Array (PTree L)) (c : UInt32) (hc : c < 32) (hbin : WF (.bin bp bl bm bk))
    (halign : AlignedAt bl c bp op) (htb : testBit bm c = false) :
    get? j (.bin bp bl (setBit bm c) (bk.insertIdx! (arrayIndex bm c) op))
      = optVjoin cf (get? j op) (get? j (.bin bp bl bm bk)) := by
  have hsize : bk.size = popCount bm := by rw [WF] at hbin; exact hbin.2.1
  rw [get?_bin, get?_bin]
  by_cases hcj : chunk j bl = c
  · subst hcj
    have hcondL : testBit (setBit bm (chunk j bl)) (chunk j bl) = true := by
      rw [testBit_setBit bm (chunk j bl) (chunk j bl) (chunk_lt j bl) (chunk_lt j bl),
          beq_self_eq_true, Bool.or_true]
    rw [if_pos hcondL, childAt_insertIdx_self bm (chunk j bl) bk op hsize,
        if_neg (show ¬ testBit bm (chunk j bl) = true by rw [htb]; exact Bool.false_ne_true),
        optVjoin_none_right]
  · have htcjlt := chunk_lt j bl
    by_cases htcj : testBit bm (chunk j bl) = true
    · have hcondL : testBit (setBit bm c) (chunk j bl) = testBit bm (chunk j bl) := by
        rw [testBit_setBit bm c (chunk j bl) hc htcjlt, beq_eq_false_iff_ne.mpr (Ne.symm hcj),
            Bool.or_false]
      rw [hcondL, if_pos htcj, if_pos htcj,
          childAt_insertIdx_of_ne bm c (chunk j bl) bk op hc htcjlt hcj htb htcj hsize,
          get?_none_of_aligned bl c bp op halign hcj, optVjoin_none_left]
    · have htcjf : testBit bm (chunk j bl) = false := by simpa using htcj
      have hcondL : testBit (setBit bm c) (chunk j bl) = false := by
        rw [testBit_setBit bm c (chunk j bl) hc htcjlt, beq_eq_false_iff_ne.mpr (Ne.symm hcj),
            htcjf, Bool.or_self]
      rw [if_neg (show ¬ testBit (setBit bm c) (chunk j bl) = true by rw [hcondL]; exact Bool.false_ne_true),
          if_neg (show ¬ testBit bm (chunk j bl) = true by rw [htcjf]; exact Bool.false_ne_true),
          get?_none_of_aligned bl c bp op halign hcj, optVjoin_none_left]

set_option maxHeartbeats 400000 in
/-- `get?` of `unionU` is the value-level join of the two lookups. The map-facing seam the
lattice/order suite routes through; mirrors `contains_unionU`'s 31-case mutual induction, but the
combine `cf` now genuinely fires (at colliding `tip`s and merged children), so the conclusion is
`optVjoin` rather than `||`. The eliminator is applied with its `LeafOps` instance pinned (see
`contains_unionU`); the per-slot motives carry the `optVjoin` characterization of `mergeChild`. -/
theorem get?_unionU (cf : V → V → V) (j : Nat) : ∀ (a b : PTree L), WF a → WF b →
    get? j (unionU cf a b) = optVjoin cf (get? j a) (get? j b) := by
  intro a b
  induction a, b using (@unionU.induct L V inferInstance cf)
    (motive2 := fun m1 k1 m2 k2 rem _ =>
      KidsWF m1 k1 → KidsWF m2 k2 →
      (∀ c, c < 32 → testBit rem c = true → testBit (m1 ||| m2) c = true) →
      ∀ c, c < 32 → testBit rem c = true →
        get? j (mergeChild cf m1 k1 m2 k2 c)
          = optVjoin cf (if testBit m1 c then get? j (childAt m1 k1 c) else none)
                        (if testBit m2 c then get? j (childAt m2 k2 c) else none))
    (motive3 := fun m1 k1 m2 k2 i =>
      KidsWF m1 k1 → KidsWF m2 k2 → i < 32 → (testBit m1 i || testBit m2 i) = true →
        get? j (mergeChild cf m1 k1 m2 k2 i)
          = optVjoin cf (if testBit m1 i then get? j (childAt m1 k1 i) else none)
                        (if testBit m2 i then get? j (childAt m2 k2 i) else none)) with
  | case1 t => intro _ _; rw [unionU, get?_nil, optVjoin_none_left]
  | case2 s hs => intro _ _; rw [unionU, get?_nil, optVjoin_none_right]; exact hs
  | case3 p1 b1 p2 b2 heq =>
    intro _ _
    have hp : p1 = p2 := by simpa using heq
    rw [unionU, if_pos heq, get?_tip, get?_tip, get?_tip, ← hp]
    by_cases hj : (j >>> 5 == p1) = true
    · rw [if_pos hj, if_pos hj, if_pos hj, LeafOps.get?_join cf b1 b2 (chunk j 0) (chunk_lt _ _)]
    · rw [if_neg hj, if_neg hj, if_neg hj, optVjoin_none_left]
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
        get?_join_optVjoin cf j (someKey (.tip p1 b1)) (someKey (.tip p2 b2)) (.tip p1 b1) (.tip p2 b2)
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
    exact get?_descend_left cf j (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl)
      (chunk_lt _ _) hwf2 halign htb h (IH hwf1 hwfchild)
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
    exact get?_splice_left cf j (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl)
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
        get?_join_optVjoin_swap cf j (someKey (.bin bp bl bm bk)) (someKey (.tip p1 b1))
          (.bin bp bl bm bk) (.tip p1 b1) hkne ?ha ?hb]
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
    rw [unionU, if_pos hpfx, if_pos htb, dif_pos h]
    exact get?_descend cf j (.tip p2 b2) bp bl bm bk (chunk (someKey (.tip p2 b2)) bl)
      (chunk_lt _ _) hwfbin halign htb h (IH hwfchild hwftip)
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
    rw [unionU, if_pos hpfx, if_neg hntb]
    exact get?_splice cf j (.tip p2 b2) bp bl bm bk (chunk (someKey (.tip p2 b2)) bl)
      (chunk_lt _ _) hwfbin halign htbf
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
        get?_join_optVjoin cf j (someKey (.bin bp bl bm bk)) (someKey (.tip p2 b2)) (.bin bp bl bm bk)
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
    rw [unionU, if_pos heq, get?_bin, get?_bin, get?_bin]
    by_cases hM : testBit (m1 ||| m2) (chunk j l1) = true
    · rw [if_pos hM, childAt_mergeKids cf m1 k1 m2 k2 (chunk j l1) (chunk_lt j l1) hM]
      exact hmc (chunk j l1) (chunk_lt j l1) hM
    · simp only [Bool.not_eq_true] at hM
      have hor : (testBit m1 (chunk j l1) || testBit m2 (chunk j l1)) = false := by
        rw [← testBit_or]; exact hM
      rw [Bool.or_eq_false_iff] at hor
      rw [if_neg (show ¬ testBit (m1 ||| m2) (chunk j l1) = true by rw [hM]; exact Bool.false_ne_true),
          if_neg (show ¬ testBit m1 (chunk j l1) = true by rw [hor.1]; exact Bool.false_ne_true),
          if_neg (show ¬ testBit m2 (chunk j l1) = true by rw [hor.2]; exact Bool.false_ne_true),
          optVjoin_none_left]
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
        get?_join_optVjoin cf j (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l1 m2 k2))
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
    rw [unionU, if_neg hne, if_neg hlne, if_pos hlt, if_pos hpfx, if_pos htb, dif_pos h]
    exact get?_descend cf j (.bin p2 l2 m2 k2) p1 l1 m1 k1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)
      (chunk_lt _ _) hwf1 halign htb h (IH hwfchild hwf2)
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
    rw [unionU, if_neg hne, if_neg hlne, if_pos hlt, if_pos hpfx, if_neg hntb]
    exact get?_splice cf j (.bin p2 l2 m2 k2) p1 l1 m1 k1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)
      (chunk_lt _ _) hwf1 halign htbf
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
        get?_join_optVjoin cf j (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l2 m2 k2))
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
    exact get?_descend_left cf j (.bin p1 l1 m1 k1) p2 l2 m2 k2
      (chunk (someKey (.bin p1 l1 m1 k1)) l2) (chunk_lt _ _) hwf2 halign htb h (IH hwf1 hwfchild)
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
    exact get?_splice_left cf j (.bin p1 l1 m1 k1) p2 l2 m2 k2
      (chunk (someKey (.bin p1 l1 m1 k1)) l2) (chunk_lt _ _) hwf2 halign htbf
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
        get?_join_optVjoin_swap cf j (someKey (.bin p2 l2 m2 k2)) (someKey (.bin p1 l1 m1 k1))
          (.bin p2 l2 m2 k2) (.bin p1 l1 m1 k1) hkne ?ha ?hb]
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
    rw [mergeChild, if_pos ht1, if_pos ht2, dif_pos h1, dif_pos h2, IH hwf1 hwf2, if_pos ht1, if_pos ht2,
        hc1, hc2]
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
    rw [mergeChild, if_pos ht1, if_neg hnt2, dif_pos h1, if_pos ht1,
        if_neg (show ¬ testBit m2 i = true by rw [hf2]; exact Bool.false_ne_true), hc1,
        optVjoin_none_right]
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
    rw [mergeChild, if_neg hnt1, dif_pos h2,
        if_neg (show ¬ testBit m1 i = true by rw [hf1]; exact Bool.false_ne_true), if_pos ht2, hc2,
        optVjoin_none_left]
  | case31 m1 k1 m2 k2 i hnt1 hnh2 =>
    rename_i _ hkw2 _ hor
    have hf1 : testBit m1 i = false := by simpa using hnt1
    have ht2 : testBit m2 i = true := by
      rw [hf1, Bool.false_or] at hor; exact hor
    exact absurd (by rw [hkw2.1]; exact arrayIndex_lt m2 i ht2) hnh2

/-- `get?` of `union` is the value-level join of the two lookups. The map-facing seam the lattice/
order suite routes through; stated on `union`, the work is in `get?_unionU`. -/
theorem get?_union (cf : V → V → V) (j : Nat) (a b : PTree L) (hwa : WF a) (hwb : WF b) :
    get? j (union cf a b) = optVjoin cf (get? j a) (get? j b) := by
  rw [union]; exact get?_unionU cf j a b hwa hwb

/-! ### `get?_meet` — the value-level intersection seam

`get?` of a `meetU` is the value-level meet (`optVmeet`) of the two lookups: present on both →
combine with `cf`, present on at most one → `none`. The map-facing companion of `meet_WF_contains`.
Where union *grows* the tree, meet *prunes* it, so the seam routes through `get?_finalize` (the
re-compression's `get?` law) and the disjoint cases collapse to `none`. -/

/-- `optVmeet` with `none` on the left is `none` (the catch-all arm), as a `rfl`-rewrite. -/
private theorem optVmeet_none_left (cf : V → V → V) (oy : Option V) :
    optVmeet cf none oy = none := rfl

/-- `optVmeet` with `none` on the right is `none` (needs a case on the left, unlike the left form). -/
private theorem optVmeet_none_right (cf : V → V → V) (ox : Option V) :
    optVmeet cf ox none = none := by cases ox <;> rfl

/-- A key absent from a subtree reads `none` — the `get?` shadow of `contains j a = false`. -/
private theorem get?_eq_none_of_contains_false (j : Nat) (a : PTree L) (h : contains j a = false) :
    get? j a = none := by
  rw [contains_eq_isSome] at h
  cases hg : get? j a with
  | none => rfl
  | some v => rw [hg] at h; simp at h

/-- `optVmeet` of two lookups collapses to `none` whenever the two key-presences are disjoint
(`contains a && contains b = false`). The single bridge the disjoint meet cases (tip/tip empty or
divergent, bin/bin divergent) route through, reusing the already-proven `contains_*` disjointness. -/
private theorem optVmeet_get?_eq_none_of_contains (cf : V → V → V) (j : Nat) (a b : PTree L)
    (h : (contains j a && contains j b) = false) :
    optVmeet cf (get? j a) (get? j b) = none := by
  cases ha : contains j a with
  | false => rw [get?_eq_none_of_contains_false j a ha]; rfl
  | true =>
    rw [ha, Bool.true_and] at h
    rw [get?_eq_none_of_contains_false j b h, optVmeet_none_right]

/-- A guarded child lookup `if b then get? j x else none` is `none` once `b && !isNil x` is `false`
(absent slot, or empty child reads `none`). The `get?` cousin of `and_contains_eq_false_of`; the
re-compression `get?` proof uses it where a slot drops out of the compacted mask. -/
private theorem get?_ite_eq_none_of (j : Nat) (b : Bool) (x : PTree L)
    (h : (b && !isNil x) = false) : (if b = true then get? j x else none) = none := by
  cases x with
  | nil => rw [get?_nil]; cases b <;> rfl
  | tip _ _ =>
    simp only [isNil, Bool.not_false, Bool.and_true] at h
    rw [if_neg (show ¬ b = true by rw [h]; exact Bool.false_ne_true)]
  | bin _ _ _ _ =>
    simp only [isNil, Bool.not_false, Bool.and_true] at h
    rw [if_neg (show ¬ b = true by rw [h]; exact Bool.false_ne_true)]

/-- Lookup after re-compression: `finalize` reads exactly like a `bin` for `get?` — route by the
level's chunk, read that slot's child (the `get?` cousin of `contains_finalize`). The empty-child
drops and the single-survivor lift both preserve the per-key value. The lift relies on the routing
hypothesis (`halign`): the lifted child's keys all hang under its own slot. -/
theorem get?_finalize (j : Nat) (p l : Nat) (mask : UInt32) (kids : Array (PTree L))
    (halign : ∀ c, c < 32 → testBit mask c = true → AlignedAt l c p (childAt mask kids c)) :
    get? j (finalize p l mask kids)
      = (if testBit mask (chunk j l) then get? j (childAt mask kids (chunk j l)) else none) := by
  obtain ⟨m, ks, he⟩ : ∃ m ks, compactify mask kids mask 0 #[] = (m, ks) := ⟨_, _, rfl⟩
  obtain ⟨hM, _, hR⟩ := compactify_top mask kids
  rw [he] at hM hR
  have hMm : ∀ c, c < 32 → testBit m c = (testBit mask c && !isNil (childAt mask kids c)) := hM
  have hRm : ∀ c, c < 32 → testBit m c = true → ks[arrayIndex m c]? = some (childAt mask kids c) := hR
  have hmask_of_m : ∀ c, c < 32 → testBit m c = true → testBit mask c = true := by
    intro c hc htb
    have hmm := hMm c hc; rw [htb] at hmm
    cases hh : testBit mask c with
    | true => rfl
    | false => rw [hh, Bool.false_and] at hmm; exact absurd hmm (by decide)
  have hchild : ∀ c, c < 32 → testBit m c = true → childAt m ks c = childAt mask kids c := by
    intro c hc htb
    show (ks[arrayIndex m c]?).getD .nil = childAt mask kids c
    rw [hRm c hc htb, Option.getD_some]
  have hbridge : (if testBit m (chunk j l) then get? j (childAt m ks (chunk j l)) else none)
      = (if testBit mask (chunk j l) then get? j (childAt mask kids (chunk j l)) else none) := by
    by_cases htm : testBit m (chunk j l) = true
    · rw [if_pos htm, hchild (chunk j l) (chunk_lt j l) htm,
          if_pos (hmask_of_m (chunk j l) (chunk_lt j l) htm)]
    · simp only [Bool.not_eq_true] at htm
      rw [if_neg (show ¬ testBit m (chunk j l) = true by rw [htm]; exact Bool.false_ne_true)]
      have hkey : (testBit mask (chunk j l) && !isNil (childAt mask kids (chunk j l))) = false := by
        rw [← hMm (chunk j l) (chunk_lt j l), htm]
      exact (get?_ite_eq_none_of j (testBit mask (chunk j l)) (childAt mask kids (chunk j l)) hkey).symm
  rw [finalize, he]
  show get? j (if m == 0 then .nil
        else if popCount m == 1 then (ks[0]?).getD .nil else .bin p l m ks)
      = (if testBit mask (chunk j l) then get? j (childAt mask kids (chunk j l)) else none)
  by_cases hm0 : (m == 0) = true
  · rw [if_pos hm0, get?_nil]
    have hmeq : m = 0 := by simpa using hm0
    have hkey : (testBit mask (chunk j l) && !isNil (childAt mask kids (chunk j l))) = false := by
      rw [← hMm (chunk j l) (chunk_lt j l), hmeq, testBit_zero]
    exact (get?_ite_eq_none_of j (testBit mask (chunk j l)) (childAt mask kids (chunk j l)) hkey).symm
  · rw [if_neg hm0]
    by_cases hp1 : (popCount m == 1) = true
    · rw [if_pos hp1]
      have hpc1 : popCount m = 1 := by simpa using hp1
      have hmne : m ≠ 0 := fun h0 => hm0 (by rw [h0]; rfl)
      have hc0 : testBit m (lowestSetIdx m) = true := testBit_lowestSetIdx m hmne
      have hlo32 : lowestSetIdx m < 32 := lowestSetIdx_lt m hmne
      have huniq : ∀ c, c < 32 → testBit m c = true → c = lowestSetIdx m := by
        intro c hc htb
        by_cases hcc : c = lowestSetIdx m
        · exact hcc
        · exfalso
          have h1 := arrayIndex_inj m c (lowestSetIdx m) hc hlo32 htb hc0 hcc
          rw [arrayIndex_lowestSetIdx m hmne] at h1
          have ha := arrayIndex_lt m c htb
          rw [hpc1] at ha
          omega
      have hks0 : (ks[0]?).getD .nil = childAt mask kids (lowestSetIdx m) := by
        have hr0 := hRm (lowestSetIdx m) hlo32 hc0
        rw [arrayIndex_lowestSetIdx m hmne] at hr0
        rw [hr0, Option.getD_some]
      rw [hks0, ← hbridge]
      by_cases hcjl : chunk j l = lowestSetIdx m
      · rw [if_pos (show testBit m (chunk j l) = true by rw [hcjl]; exact hc0), hcjl,
            hchild (lowestSetIdx m) hlo32 hc0]
      · have htmf : testBit m (chunk j l) = false := by
          cases hh : testBit m (chunk j l) with
          | false => rfl
          | true => exact absurd (huniq (chunk j l) (chunk_lt j l) hh) hcjl
        rw [if_neg (show ¬ testBit m (chunk j l) = true by rw [htmf]; exact Bool.false_ne_true)]
        cases hcon : get? j (childAt mask kids (lowestSetIdx m)) with
        | none => rfl
        | some v =>
          have hcontains : contains j (childAt mask kids (lowestSetIdx m)) = true := by
            rw [contains_eq_isSome, hcon]; rfl
          have hal := halign (lowestSetIdx m) hlo32 (hmask_of_m (lowestSetIdx m) hlo32 hc0) j hcontains
          exact absurd hal.1 hcjl
    · rw [if_neg hp1, get?_bin]
      exact hbridge

/-- Descend bridge (right operand is the `bin`) for `get?_meet`: intersecting `R` with the `bin`'s
routed child reads the same as intersecting `R` with the whole `bin` — keys of `R` route to that one
slot, and where `R` is absent the meet is `none` regardless. -/
private theorem get?_meet_descend_right (cf : V → V → V) (k bp bl : Nat) (bm : UInt32)
    (bk : Array (PTree L)) (R : PTree L) (c0 : UInt32) (pr : Nat) (halignR : AlignedAt bl c0 pr R)
    (htb : testBit bm c0 = true) :
    optVmeet cf (get? k R) (get? k (childAt bm bk c0))
      = optVmeet cf (get? k R) (get? k (.bin bp bl bm bk)) := by
  by_cases hR : (get? k R).isSome = true
  · have hcon : contains k R = true := by rw [contains_eq_isSome]; exact hR
    obtain ⟨hchunk, _⟩ := halignR k hcon
    rw [get?_bin, hchunk, if_pos htb]
  · have hRn : get? k R = none := by
      cases hg : get? k R with
      | none => rfl
      | some v => rw [hg] at hR; simp at hR
    rw [hRn, optVmeet_none_left, optVmeet_none_left]

/-- Descend bridge (left operand is the `bin`): the mirror of `get?_meet_descend_right`. -/
private theorem get?_meet_descend_left (cf : V → V → V) (k bp bl : Nat) (bm : UInt32)
    (bk : Array (PTree L)) (R : PTree L) (c0 : UInt32) (pr : Nat) (halignR : AlignedAt bl c0 pr R)
    (htb : testBit bm c0 = true) :
    optVmeet cf (get? k (childAt bm bk c0)) (get? k R)
      = optVmeet cf (get? k (.bin bp bl bm bk)) (get? k R) := by
  by_cases hR : (get? k R).isSome = true
  · have hcon : contains k R = true := by rw [contains_eq_isSome]; exact hR
    obtain ⟨hchunk, _⟩ := halignR k hcon
    rw [get?_bin, hchunk, if_pos htb]
  · have hRn : get? k R = none := by
      cases hg : get? k R with
      | none => rfl
      | some v => rw [hg] at hR; simp at hR
    rw [hRn, optVmeet_none_right, optVmeet_none_right]

set_option maxHeartbeats 400000 in
/-- `get?` of `meetU` is the value-level meet of the two lookups. The map-facing seam the
intersection lattice/order suite routes through; a separate `get?`-form induction mirroring
`meet_WF_contains`'s 25 cases, reusing the already-proven `WF`/`contains` facts for the routing
(`halign`) and disjointness obligations. The eliminator is applied with `L`/`V`/instance/`cf`
pinned (see `meet_WF_contains`); the per-slot motives carry the `optVmeet` characterization. -/
theorem get?_meetU (cf : V → V → V) (j : Nat) : ∀ (a b : PTree L), WF a → WF b →
    get? j (meetU cf a b) = optVmeet cf (get? j a) (get? j b) := by
  intro a b
  induction a, b using (@meetU.induct L V inferInstance cf)
    (motive2 := fun m1 k1 m2 k2 rem _ =>
      KidsWF m1 k1 → KidsWF m2 k2 →
      (∀ c, c < 32 → testBit rem c = true → testBit m1 c = true ∧ testBit m2 c = true) →
      ∀ c, c < 32 → testBit rem c = true →
        get? j (meetChild cf m1 k1 m2 k2 c)
          = optVmeet cf (get? j (childAt m1 k1 c)) (get? j (childAt m2 k2 c)))
    (motive3 := fun m1 k1 m2 k2 i =>
      KidsWF m1 k1 → KidsWF m2 k2 → testBit m1 i = true → testBit m2 i = true →
        get? j (meetChild cf m1 k1 m2 k2 i)
          = optVmeet cf (get? j (childAt m1 k1 i)) (get? j (childAt m2 k2 i))) with
  | case1 x => intro _ _; rw [meetU, get?_nil, optVmeet_none_left]
  | case2 p1 b1 => intro _ _; rw [meetU, get?_nil, optVmeet_none_right]
  | case3 bp bl bm bk => intro _ _; rw [meetU, get?_nil, optVmeet_none_right]
  | case4 p1 b1 p2 b2 heq hdis =>
    intro _ _
    rw [meetU, if_pos heq, if_pos hdis, get?_nil]
    exact (optVmeet_get?_eq_none_of_contains cf j (.tip p1 b1) (.tip p2 b2)
      (contains_tiptip_disjoint cf j p1 b1 p2 b2 hdis)).symm
  | case5 p1 b1 p2 b2 heq hndis =>
    intro _ _
    have hp : p1 = p2 := by simpa using heq
    rw [meetU, if_pos heq, if_neg hndis, get?_tip, get?_tip, get?_tip, ← hp]
    by_cases hj : (j >>> 5 == p1) = true
    · rw [if_pos hj, if_pos hj, if_pos hj, LeafOps.get?_meet cf b1 b2 (chunk j 0) (chunk_lt _ _)]
    · rw [if_neg hj, if_neg hj, if_neg hj, optVmeet_none_left]
  | case6 p1 b1 p2 b2 hne =>
    intro _ _
    have hpne : p1 ≠ p2 := by intro h; exact hne (by rw [h]; exact beq_self_eq_true p2)
    rw [meetU, if_neg hne, get?_nil]
    exact (optVmeet_get?_eq_none_of_contains cf j (.tip p1 b1) (.tip p2 b2)
      (contains_tiptip_pfxne j p1 b1 p2 b2 hpne)).symm
  | case7 p1 b1 bp bl bm bk hcond h IH =>
    intro hwfa hwfb
    have hb1 : LeafOps.isEmpty b1 = false := by rw [WF] at hwfa; exact hwfa
    have hbl0 : 0 < bl := by rw [WF] at hwfb; exact hwfb.1
    have hwfchild := by rw [WF] at hwfb; exact hwfb.2.2.2.1 _ (Array.getElem_mem h)
    obtain ⟨hpfxb, htbb⟩ := and_split hcond
    have hpfxeq : prefixAbove (someKey (.tip p1 b1)) bl = bp := by simpa using hpfxb
    have halign : AlignedAt bl (chunk (someKey (.tip p1 b1)) bl) bp (.tip p1 b1) :=
      hpfxeq ▸ aligned_tip p1 b1 hb1 bl hbl0
    have hcAc : childAt bm bk (chunk (someKey (.tip p1 b1)) bl)
        = bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h := by
      unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
    rw [meetU, if_pos hcond, dif_pos h, IH hwfa hwfchild, ← hcAc]
    exact get?_meet_descend_right cf j bp bl bm bk (.tip p1 b1)
      (chunk (someKey (.tip p1 b1)) bl) bp halign htbb
  | case8 p1 b1 bp bl bm bk hcond hnh =>
    intro _ hwfb
    obtain ⟨_, htbb⟩ := and_split hcond
    have hsize : bk.size = popCount bm := by rw [WF] at hwfb; exact hwfb.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt bm _ htbb) hnh
  | case9 p1 b1 bp bl bm bk hncond =>
    intro hwfa hwfb
    have hb1 : LeafOps.isEmpty b1 = false := by rw [WF] at hwfa; exact hwfa
    have hbl0 : 0 < bl := by rw [WF] at hwfb; exact hwfb.1
    have hcondf : ((prefixAbove (someKey (.tip p1 b1)) bl == bp)
        && testBit bm (chunk (someKey (.tip p1 b1)) bl)) = false := by simpa using hncond
    have halign : AlignedAt bl (chunk (someKey (.tip p1 b1)) bl)
        (prefixAbove (someKey (.tip p1 b1)) bl) (.tip p1 b1) := aligned_tip p1 b1 hb1 bl hbl0
    rw [meetU, if_neg hncond, get?_nil]
    exact (optVmeet_get?_eq_none_of_contains cf j (.tip p1 b1) (.bin bp bl bm bk)
      (contains_div_eq_false j bp bl bm bk (.tip p1 b1) (chunk (someKey (.tip p1 b1)) bl)
        (prefixAbove (someKey (.tip p1 b1)) bl) hwfb halign hcondf)).symm
  | case10 bp bl bm bk p2 b2 hcond h IH =>
    intro hwfa hwfb
    have hb2 : LeafOps.isEmpty b2 = false := by rw [WF] at hwfb; exact hwfb
    have hbl0 : 0 < bl := by rw [WF] at hwfa; exact hwfa.1
    have hwfchild := by rw [WF] at hwfa; exact hwfa.2.2.2.1 _ (Array.getElem_mem h)
    obtain ⟨hpfxb, htbb⟩ := and_split hcond
    have hpfxeq : prefixAbove (someKey (.tip p2 b2)) bl = bp := by simpa using hpfxb
    have halign : AlignedAt bl (chunk (someKey (.tip p2 b2)) bl) bp (.tip p2 b2) :=
      hpfxeq ▸ aligned_tip p2 b2 hb2 bl hbl0
    have hcAc : childAt bm bk (chunk (someKey (.tip p2 b2)) bl)
        = bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h := by
      unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
    rw [meetU, if_pos hcond, dif_pos h, IH hwfchild hwfb, ← hcAc]
    exact get?_meet_descend_left cf j bp bl bm bk (.tip p2 b2)
      (chunk (someKey (.tip p2 b2)) bl) bp halign htbb
  | case11 bp bl bm bk p2 b2 hcond hnh =>
    intro hwfa _
    obtain ⟨_, htbb⟩ := and_split hcond
    have hsize : bk.size = popCount bm := by rw [WF] at hwfa; exact hwfa.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt bm _ htbb) hnh
  | case12 bp bl bm bk p2 b2 hncond =>
    intro hwfa hwfb
    have hb2 : LeafOps.isEmpty b2 = false := by rw [WF] at hwfb; exact hwfb
    have hbl0 : 0 < bl := by rw [WF] at hwfa; exact hwfa.1
    have hcondf : ((prefixAbove (someKey (.tip p2 b2)) bl == bp)
        && testBit bm (chunk (someKey (.tip p2 b2)) bl)) = false := by simpa using hncond
    have halign : AlignedAt bl (chunk (someKey (.tip p2 b2)) bl)
        (prefixAbove (someKey (.tip p2 b2)) bl) (.tip p2 b2) := aligned_tip p2 b2 hb2 bl hbl0
    rw [meetU, if_neg hncond, get?_nil]
    refine (optVmeet_get?_eq_none_of_contains cf j (.bin bp bl bm bk) (.tip p2 b2) ?_).symm
    rw [Bool.and_comm]
    exact contains_div_eq_false j bp bl bm bk (.tip p2 b2) (chunk (someKey (.tip p2 b2)) bl)
      (prefixAbove (someKey (.tip p2 b2)) bl) hwfa halign hcondf
  | case13 p1 l1 m1 k1 p2 l2 m2 k2 heq hpfx IH =>
    intro hwf1 hwf2
    have hl : l1 = l2 := by simpa using heq
    subst hl
    have hkw1 : KidsWF m1 k1 := by rw [WF] at hwf1; exact ⟨hwf1.2.1, hwf1.2.2.2.1, hwf1.2.2.2.2.1⟩
    have hkw2 : KidsWF m2 k2 := by rw [WF] at hwf2; exact ⟨hwf2.2.1, hwf2.2.2.2.1, hwf2.2.2.2.2.1⟩
    have hl0 : 0 < l1 := by rw [WF] at hwf1; exact hwf1.1
    have hrout1 : ∀ c, c < 32 → testBit m1 c = true → AlignedAt l1 c p1 (childAt m1 k1 c) := by
      rw [WF] at hwf1; exact hwf1.2.2.2.2.2
    have hslot := IH hkw1 hkw2 (fun c _ hb => by
      rw [testBit_and] at hb; exact ⟨(and_split hb).1, (and_split hb).2⟩)
    have hslotC : ∀ c, c < 32 → testBit (m1 &&& m2) c = true →
        ∀ key, contains key (meetChild cf m1 k1 m2 k2 c)
          = (contains key (childAt m1 k1 c) && contains key (childAt m2 k2 c)) := by
      intro c hc htb key
      rw [testBit_and] at htb
      obtain ⟨ht1, ht2⟩ := and_split htb
      have hi1 : arrayIndex m1 c < k1.size := by rw [hkw1.1]; exact arrayIndex_lt m1 c ht1
      have hi2 : arrayIndex m2 c < k2.size := by rw [hkw2.1]; exact arrayIndex_lt m2 c ht2
      have hcc1 : childAt m1 k1 c = k1[arrayIndex m1 c]'hi1 := by
        unfold childAt; rw [Array.getElem?_eq_getElem hi1, Option.getD_some]
      have hcc2 : childAt m2 k2 c = k2[arrayIndex m2 c]'hi2 := by
        unfold childAt; rw [Array.getElem?_eq_getElem hi2, Option.getD_some]
      rw [meetChild, dif_pos hi1, dif_pos hi2, hcc1, hcc2]
      exact (meet_WF_contains cf (k1[arrayIndex m1 c]'hi1) (k2[arrayIndex m2 c]'hi2)
        (hkw1.2.1 _ (Array.getElem_mem hi1)) (hkw2.2.1 _ (Array.getElem_mem hi2))).2 key
    have halign : ∀ c, c < 32 → testBit (m1 &&& m2) c = true →
        AlignedAt l1 c p1 (childAt (m1 &&& m2) (meetKids cf m1 k1 m2 k2 (m1 &&& m2) #[]) c) := by
      intro c hc htb
      rw [childAt_meetKids cf m1 k1 m2 k2 c hc htb]
      intro key hkey
      rw [hslotC c hc htb key] at hkey
      have htbm1 : testBit m1 c = true := by rw [testBit_and] at htb; exact (and_split htb).1
      exact hrout1 c hc htbm1 key (and_split hkey).1
    rw [meetU, if_pos heq, if_pos hpfx, get?_finalize j p1 l1 (m1 &&& m2) _ halign]
    by_cases hM : testBit (m1 &&& m2) (chunk j l1) = true
    · have h12 := testBit_and m1 m2 (chunk j l1)
      rw [hM] at h12
      obtain ⟨ht1, ht2⟩ := and_split h12.symm
      rw [if_pos hM, childAt_meetKids cf m1 k1 m2 k2 (chunk j l1) (chunk_lt j l1) hM,
          hslot (chunk j l1) (chunk_lt j l1) hM, get?_bin, get?_bin, if_pos ht1, if_pos ht2]
    · simp only [Bool.not_eq_true] at hM
      rw [if_neg (show ¬ testBit (m1 &&& m2) (chunk j l1) = true by rw [hM]; exact Bool.false_ne_true)]
      refine (optVmeet_get?_eq_none_of_contains cf j (.bin p1 l1 m1 k1) (.bin p2 l1 m2 k2) ?_).symm
      rw [contains_bin, contains_bin, and_pair_swap, ← testBit_and, hM, Bool.false_and]
  | case14 p1 l1 m1 k1 p2 l2 m2 k2 heq hnpfx =>
    intro hwf1 hwf2
    have hl : l1 = l2 := by simpa using heq
    subst hl
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
    have hpne : p1 ≠ p2 := by
      intro h; apply hnpfx; rw [hsk1, hsk2, h]; exact beq_self_eq_true p2
    rw [meetU, if_pos heq, if_neg hnpfx, get?_nil]
    exact (optVmeet_get?_eq_none_of_contains cf j (.bin p1 l1 m1 k1) (.bin p2 l1 m2 k2)
      (contains_binbin_pfxne j p1 l1 m1 k1 p2 m2 k2 hwf1 hwf2 hpne)).symm
  | case15 p1 l1 m1 k1 p2 l2 m2 k2 hne hlt hcond h IH =>
    intro hwf1 hwf2
    have hwfchild := by rw [WF] at hwf1; exact hwf1.2.2.2.1 _ (Array.getElem_mem h)
    obtain ⟨hpfxb, htbb⟩ := and_split hcond
    have hpfxeq : prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 = p1 := by simpa using hpfxb
    have halign : AlignedAt l1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) p1 (.bin p2 l2 m2 k2) :=
      hpfxeq ▸ aligned_bin p2 l2 m2 k2 hwf2 l1 hlt
    have hcAc : childAt m1 k1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)
        = k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h := by
      unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
    rw [meetU, if_neg hne, if_pos hlt, if_pos hcond, dif_pos h, IH hwfchild hwf2, ← hcAc]
    exact get?_meet_descend_left cf j p1 l1 m1 k1 (.bin p2 l2 m2 k2)
      (chunk (someKey (.bin p2 l2 m2 k2)) l1) p1 halign htbb
  | case16 p1 l1 m1 k1 p2 l2 m2 k2 hne hlt hcond hnh =>
    intro hwf1 _
    obtain ⟨_, htbb⟩ := and_split hcond
    have hsize : k1.size = popCount m1 := by rw [WF] at hwf1; exact hwf1.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt m1 _ htbb) hnh
  | case17 p1 l1 m1 k1 p2 l2 m2 k2 hne hlt hncond =>
    intro hwf1 hwf2
    have hcondf : ((prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 == p1)
        && testBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)) = false := by simpa using hncond
    have halign : AlignedAt l1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)
        (prefixAbove (someKey (.bin p2 l2 m2 k2)) l1) (.bin p2 l2 m2 k2) :=
      aligned_bin p2 l2 m2 k2 hwf2 l1 hlt
    rw [meetU, if_neg hne, if_pos hlt, if_neg hncond, get?_nil]
    refine (optVmeet_get?_eq_none_of_contains cf j (.bin p1 l1 m1 k1) (.bin p2 l2 m2 k2) ?_).symm
    rw [Bool.and_comm]
    exact contains_div_eq_false j p1 l1 m1 k1 (.bin p2 l2 m2 k2)
      (chunk (someKey (.bin p2 l2 m2 k2)) l1) (prefixAbove (someKey (.bin p2 l2 m2 k2)) l1)
      hwf1 halign hcondf
  | case18 p1 l1 m1 k1 p2 l2 m2 k2 hne hnlt hcond h IH =>
    intro hwf1 hwf2
    have hl12 : l1 < l2 := by
      have hlne : l1 ≠ l2 := by intro he; exact hne (by rw [he]; exact beq_self_eq_true l2)
      omega
    have hwfchild := by rw [WF] at hwf2; exact hwf2.2.2.2.1 _ (Array.getElem_mem h)
    obtain ⟨hpfxb, htbb⟩ := and_split hcond
    have hpfxeq : prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 = p2 := by simpa using hpfxb
    have halign : AlignedAt l2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) p2 (.bin p1 l1 m1 k1) :=
      hpfxeq ▸ aligned_bin p1 l1 m1 k1 hwf1 l2 hl12
    have hcAc : childAt m2 k2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)
        = k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h := by
      unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
    rw [meetU, if_neg hne, if_neg hnlt, if_pos hcond, dif_pos h, IH hwf1 hwfchild, ← hcAc]
    exact get?_meet_descend_right cf j p2 l2 m2 k2 (.bin p1 l1 m1 k1)
      (chunk (someKey (.bin p1 l1 m1 k1)) l2) p2 halign htbb
  | case19 p1 l1 m1 k1 p2 l2 m2 k2 hne hnlt hcond hnh =>
    intro _ hwf2
    obtain ⟨_, htbb⟩ := and_split hcond
    have hsize : k2.size = popCount m2 := by rw [WF] at hwf2; exact hwf2.2.1
    exact absurd (by rw [hsize]; exact arrayIndex_lt m2 _ htbb) hnh
  | case20 p1 l1 m1 k1 p2 l2 m2 k2 hne hnlt hncond =>
    intro hwf1 hwf2
    have hl12 : l1 < l2 := by
      have hlne : l1 ≠ l2 := by intro he; exact hne (by rw [he]; exact beq_self_eq_true l2)
      omega
    have hcondf : ((prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 == p2)
        && testBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)) = false := by simpa using hncond
    have halign : AlignedAt l2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)
        (prefixAbove (someKey (.bin p1 l1 m1 k1)) l2) (.bin p1 l1 m1 k1) :=
      aligned_bin p1 l1 m1 k1 hwf1 l2 hl12
    rw [meetU, if_neg hne, if_neg hnlt, if_neg hncond, get?_nil]
    exact (optVmeet_get?_eq_none_of_contains cf j (.bin p1 l1 m1 k1) (.bin p2 l2 m2 k2)
      (contains_div_eq_false j p2 l2 m2 k2 (.bin p1 l1 m1 k1)
        (chunk (someKey (.bin p1 l1 m1 k1)) l2) (prefixAbove (someKey (.bin p1 l1 m1 k1)) l2)
        hwf2 halign hcondf)).symm
  | case21 m1 k1 m2 k2 rem acc hrem =>
    rename_i _ _ _ c hc htb
    have hr0 : rem = 0 := by simpa using hrem
    rw [hr0, testBit_zero] at htb; exact absurd htb (by decide)
  | case22 m1 k1 m2 k2 rem acc hrem IHchild IHrec =>
    rename_i hkw1 hkw2 hpre c hc htb
    have hrem0 : rem ≠ 0 := by intro h; exact hrem (by rw [h]; rfl)
    by_cases hclo : c = lowestSetIdx rem
    · subst hclo
      have hpr := hpre (lowestSetIdx rem) (lowestSetIdx_lt rem hrem0) (testBit_lowestSetIdx rem hrem0)
      exact IHchild hkw1 hkw2 hpr.1 hpr.2
    · have htb' : testBit (clearLowest rem) c = true := by
        rw [testBit_clearLowest_of_ne rem c hc hclo]; exact htb
      exact IHrec hkw1 hkw2
        (fun c' hc' h' => hpre c' hc' (testBit_of_clearLowest rem c' h')) c hc htb'
  | case23 m1 k1 m2 k2 i h1 h2 IH =>
    rename_i hkw1 hkw2 _ _
    have hwf1 := hkw1.2.1 _ (Array.getElem_mem h1)
    have hwf2 := hkw2.2.1 _ (Array.getElem_mem h2)
    have hc1 : childAt m1 k1 i = k1[arrayIndex m1 i]'h1 := by
      unfold childAt; rw [Array.getElem?_eq_getElem h1, Option.getD_some]
    have hc2 : childAt m2 k2 i = k2[arrayIndex m2 i]'h2 := by
      unfold childAt; rw [Array.getElem?_eq_getElem h2, Option.getD_some]
    rw [meetChild, dif_pos h1, dif_pos h2, IH hwf1 hwf2, hc1, hc2]
  | case24 m1 k1 m2 k2 i h1 hnh2 =>
    rename_i _ hkw2 _ ht2
    exact absurd (by rw [hkw2.1]; exact arrayIndex_lt m2 i ht2) hnh2
  | case25 m1 k1 m2 k2 i hnh1 =>
    rename_i hkw1 _ ht1 _
    exact absurd (by rw [hkw1.1]; exact arrayIndex_lt m1 i ht1) hnh1

/-- `get?` of `meet` is the value-level meet of the two lookups. The map-facing seam the intersection
lattice/order suite routes through; stated on `meet`, the work is in `get?_meetU`. -/
theorem get?_meet (cf : V → V → V) (j : Nat) (a b : PTree L) (hwa : WF a) (hwb : WF b) :
    get? j (meet cf a b) = optVmeet cf (get? j a) (get? j b) := by
  rw [meet]; exact get?_meetU cf j a b hwa hwb

/-! ### `subset_iff` — the order/restriction seam

`subsetU rel a b` decides the value-aware restriction order: every key of `a` is present in `b` with
its value `rel`-related to `b`'s — `∀ k, optRel rel (get? k a) (get? k b)`. The get?-form analogue of
`meet_WF_contains`/`get?_meetU`'s contains-vs-value split: the *structural* obligations (a key is
present, two trees diverge) reuse the proven `contains_*` membership lemmas through
`contains_of_optRel`; only the leaf comparison (`LeafOps.get?_restricts`) and the per-child relation
are genuinely value-aware. An iff over the mutual `subsetU`/`subsetKids`. -/

/-- A bitset inclusion `b1 &&& b2 = b1` says every in-range bit of `b1` is also a bit of `b2`. -/
private theorem and_eq_self_iff (b1 b2 : UInt32) :
    (b1 &&& b2) = b1 ↔ ∀ c, c < 32 → testBit b1 c = true → testBit b2 c = true := by
  constructor
  · intro h c hc hb1
    have key : testBit (b1 &&& b2) c = testBit b1 c := by rw [h]
    rw [testBit_and, hb1, Bool.true_and] at key; exact key
  · intro h
    apply eq_of_testBit_eq
    intro i hi
    rw [testBit_and]
    cases hb1 : testBit b1 i with
    | true => simp [h i hi hb1]
    | false => rfl

/-- `optRel` with `none` on the left holds vacuously (the `none, _ => true` arm). -/
private theorem optRel_none_left (rel : V → V → Bool) (ob : Option V) :
    optRel rel none ob = true := rfl

/-- A left-present lookup forces a right-present one when `optRel` holds (`some _, none => false`). -/
private theorem isSome_of_optRel_some (rel : V → V → Bool) (x : V) (ob : Option V)
    (h : optRel rel (some x) ob = true) : ob.isSome = true := by
  cases ob with
  | none => simp [optRel] at h
  | some y => rfl

/-- The order's key-presence content: a key present in `a` and `optRel`-related to `b` is present in
`b`. The bridge that lets the structural obligations reuse the `contains_*` membership lemmas. -/
private theorem contains_of_optRel (rel : V → V → Bool) (j : Nat) (a b : PTree L)
    (hca : contains j a = true) (h : optRel rel (get? j a) (get? j b) = true) :
    contains j b = true := by
  rw [contains_eq_isSome] at hca ⊢
  cases hga : get? j a with
  | none => rw [hga] at hca; exact absurd hca (by simp)
  | some x => rw [hga] at h; exact isSome_of_optRel_some rel x _ h

/-- A non-empty well-formed tree has a key it actually maps (`get?` reads `some`). -/
private theorem exists_get?_some (t : PTree L) (hwf : WF t) (hne : t ≠ .nil) :
    ∃ j x, get? j t = some x := by
  obtain ⟨j, hj⟩ := exists_mem t hwf hne
  rw [contains_eq_isSome] at hj
  cases hg : get? j t with
  | none => rw [hg] at hj; simp at hj
  | some x => exact ⟨j, x, hg⟩

/-- Descend bridge for `subset_iff`: when `a` routes to a present slot `c0` of a `bin`, comparing `a`
against that slot's child is the same as comparing it against the whole `bin` — off-slot keys of `a`
are absent (`optRel none _` holds vacuously). -/
private theorem optRel_descend (rel : V → V → Bool) (a : PTree L) (bp bl : Nat) (bm : UInt32)
    (bk : Array (PTree L)) (c0 : UInt32) (pr : Nat) (halign : AlignedAt bl c0 pr a)
    (htb : testBit bm c0 = true) :
    (∀ k, optRel rel (get? k a) (get? k (childAt bm bk c0)) = true)
      ↔ (∀ k, optRel rel (get? k a) (get? k (.bin bp bl bm bk)) = true) := by
  constructor
  · intro h k
    by_cases hcj : chunk k bl = c0
    · rw [get?_bin, hcj, if_pos htb]; exact h k
    · rw [get?_eq_none_of_contains_false k a (contains_false_of_aligned bl c0 pr a halign hcj)]; rfl
  · intro h k
    by_cases hcj : chunk k bl = c0
    · have hk := h k; rw [get?_bin, hcj, if_pos htb] at hk; exact hk
    · rw [get?_eq_none_of_contains_false k a (contains_false_of_aligned bl c0 pr a halign hcj)]; rfl

set_option maxHeartbeats 400000 in
/-- **Subset characterization** (`get?` form): the `subsetU`/`subsetKids` walk decides the
value-aware restriction order — `a` restricts `b` iff `optRel rel` relates their lookups at every key
(needs `rel` reflexive, for the set leaf whose `restricts` discards `rel`). The order analogue of
`get?_meet`, by the combined `subsetU.induct`; `motive2` carries the per-child spec the equal-level
`bin`/`bin` case consumes. The eliminator is applied with `L`/`V`/instance/`rel` pinned. -/
theorem subset_iff (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (a b : PTree L)
    (hwa : WF a) (hwb : WF b) :
    subsetU rel a b = true ↔ ∀ k, optRel rel (get? k a) (get? k b) = true := by
  revert hwa hwb
  induction a, b using (@subsetU.induct L V inferInstance)
    (motive2 := fun m1 k1 m2 k2 rem =>
      KidsWF m1 k1 → KidsWF m2 k2 →
        (∀ c, c < 32 → testBit rem c = true → testBit m1 c = true) →
        (∀ c, c < 32 → testBit rem c = true → testBit m2 c = true) →
        (subsetKids rel m1 k1 m2 k2 rem = true ↔
          ∀ c, c < 32 → testBit rem c = true →
            ∀ k, optRel rel (get? k (childAt m1 k1 c)) (get? k (childAt m2 k2 c)) = true)) with
  | case1 x =>
    intro hwa hwb
    refine iff_of_true (by rw [subsetU]) (fun k => ?_)
    rw [get?_nil]; rfl
  | case2 pfx bits =>
    intro hwa hwb
    apply iff_of_false
    · intro h; rw [subsetU] at h; exact absurd h (by decide)
    · intro hsub
      obtain ⟨j, x, hx⟩ := exists_get?_some (.tip pfx bits) hwa (by simp)
      have hj := hsub j
      rw [hx, get?_nil] at hj
      simp [optRel] at hj
  | case3 pfx level mask kids =>
    intro hwa hwb
    apply iff_of_false
    · intro h; rw [subsetU] at h; exact absurd h (by decide)
    · intro hsub
      obtain ⟨j, x, hx⟩ := exists_get?_some (.bin pfx level mask kids) hwa (by simp)
      have hj := hsub j
      rw [hx, get?_nil] at hj
      simp [optRel] at hj
  | case4 p1 b1 p2 b2 =>
    intro hwa hwb
    have hb1 : LeafOps.isEmpty b1 = false := by rw [WF] at hwa; exact hwa
    rw [subsetU, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨hp, hres⟩ k
      rw [get?_tip, get?_tip, ← hp]
      by_cases hk : (k >>> 5 == p1) = true
      · rw [if_pos hk, if_pos hk]
        exact (LeafOps.get?_restricts rel hrefl b1 b2).mp hres (chunk k 0) (chunk_lt _ _)
      · rw [if_neg hk]; rfl
    · intro hsub
      have hp : p1 = p2 := by
        obtain ⟨j0, x0, hx0⟩ := exists_get?_some (.tip p1 b1) hwa (by simp)
        have hj0 : contains j0 (.tip p1 b1) = true := by rw [contains_eq_isSome, hx0]; rfl
        have hj0t : contains j0 (.tip p2 b2) = true :=
          contains_of_optRel rel j0 (.tip p1 b1) (.tip p2 b2) hj0 (hsub j0)
        rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hj0 hj0t
        rw [← hj0.1]; exact hj0t.1
      refine ⟨hp, (LeafOps.get?_restricts rel hrefl b1 b2).mpr (fun i hi => ?_)⟩
      have hk := hsub (i.toNat + 32 * p1)
      rw [get?_tip_probe p1 b1 i hi] at hk
      rw [show i.toNat + 32 * p1 = i.toNat + 32 * p2 from by rw [hp]] at hk
      rw [get?_tip_probe p2 b2 i hi] at hk
      exact hk
  | case5 p1 b1 bp bl bm bk ih =>
    intro hwa hwb
    have hb1 : LeafOps.isEmpty b1 = false := by rw [WF] at hwa; exact hwa
    have hwb' := hwb; rw [WF] at hwb'
    obtain ⟨hbl0, hsize, hpc, hkidswf, hnonnil, hrout⟩ := hwb'
    have halign := aligned_tip p1 b1 hb1 bl hbl0
    rw [subsetU]
    constructor
    · intro hcond
      rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨hpre, htb⟩, hdite⟩ := hcond
      have hidx : arrayIndex bm (chunk (someKey (.tip p1 b1)) bl) < bk.size := by
        rw [hsize]; exact arrayIndex_lt bm _ htb
      rw [dif_pos hidx] at hdite
      have hchild : bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'hidx
                      = childAt bm bk (chunk (someKey (.tip p1 b1)) bl) := by
        unfold childAt; rw [Array.getElem?_eq_getElem hidx, Option.getD_some]
      have hwfbkidx := hkidswf _ (Array.getElem_mem hidx)
      have hrec := (ih hidx hwa hwfbkidx).mp hdite
      rw [hchild] at hrec
      exact (optRel_descend rel (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl)
        (prefixAbove (someKey (.tip p1 b1)) bl) halign htb).mp hrec
    · intro hsub
      obtain ⟨j0, x0, hx0⟩ := exists_get?_some (.tip p1 b1) hwa (by simp)
      have hj0 : contains j0 (.tip p1 b1) = true := by rw [contains_eq_isSome, hx0]; rfl
      have hj0bin : contains j0 (.bin bp bl bm bk) = true :=
        contains_of_optRel rel j0 (.tip p1 b1) (.bin bp bl bm bk) hj0 (hsub j0)
      have hchunk0 : chunk j0 bl = chunk (someKey (.tip p1 b1)) bl := (halign j0 hj0).1
      have hpre0 : prefixAbove j0 bl = prefixAbove (someKey (.tip p1 b1)) bl := (halign j0 hj0).2
      rw [contains_bin, hchunk0, Bool.and_eq_true] at hj0bin
      obtain ⟨htb, hchildmem⟩ := hj0bin
      have hidx : arrayIndex bm (chunk (someKey (.tip p1 b1)) bl) < bk.size := by
        rw [hsize]; exact arrayIndex_lt bm _ htb
      have hprebp : prefixAbove (someKey (.tip p1 b1)) bl = bp := by
        rw [← hpre0]
        exact prefixAbove_eq_of_mem bp bl bm bk hwb j0
          (by rw [contains_bin, hchunk0, htb, Bool.true_and]; exact hchildmem)
      have hchild : bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'hidx
                      = childAt bm bk (chunk (someKey (.tip p1 b1)) bl) := by
        unfold childAt; rw [Array.getElem?_eq_getElem hidx, Option.getD_some]
      have hwfbkidx := hkidswf _ (Array.getElem_mem hidx)
      rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨hprebp, htb⟩, ?_⟩
      rw [dif_pos hidx]
      apply (ih hidx hwa hwfbkidx).mpr
      have hbridge := (optRel_descend rel (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl)
        (prefixAbove (someKey (.tip p1 b1)) bl) halign htb).mpr hsub
      rw [← hchild] at hbridge; exact hbridge
  | case6 pfx level mask kids p2 bits =>
    intro hwa hwb
    apply iff_of_false
    · intro h; rw [subsetU] at h; exact absurd h (by decide)
    · intro hsub
      obtain ⟨j1, j2, hj1, hj2, hne⟩ := exists_two_divergent pfx level mask kids hwa
      have hlvl : 0 < level := by rw [WF] at hwa; exact hwa.1
      have h1 := contains_of_optRel rel j1 _ _ hj1 (hsub j1)
      have h2 := contains_of_optRel rel j2 _ _ hj2 (hsub j2)
      rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at h1 h2
      have h5 : j1 >>> 5 = j2 >>> 5 := h1.1.trans h2.1.symm
      exact hne (chunk_eq_of_shiftRight_eq (shiftRight_mono_eq h5 (by omega)))
  | case7 p1 l1 m1 k1 p2 l2 m2 k2 heq ih2 =>
    intro hwa hwb
    have hl12 : l1 = l2 := eq_of_beq heq
    subst hl12
    have hwa' := hwa; rw [WF] at hwa'
    obtain ⟨hl1, hsize1, hpc1, hkidswf1, hnonnil1, hrout1⟩ := hwa'
    have hwb' := hwb; rw [WF] at hwb'
    obtain ⟨hl2, hsize2, hpc2, hkidswf2, hnonnil2, hrout2⟩ := hwb'
    have hm1 : m1 ≠ 0 := by intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc1; omega
    have hm2 : m2 ≠ 0 := by intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc2; omega
    have hkw1 : KidsWF m1 k1 := ⟨hsize1, hkidswf1, hnonnil1⟩
    have hkw2 : KidsWF m2 k2 := ⟨hsize2, hkidswf2, hnonnil2⟩
    rw [subsetU, if_pos heq, someKey_bin_prefixAbove p1 l1 m1 k1 hm1,
        someKey_bin_prefixAbove p2 l1 m2 k2 hm2, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq,
        beq_iff_eq, and_eq_self_iff]
    constructor
    · rintro ⟨⟨hp, hmsub⟩, hsk⟩ k
      have hchildsub := (ih2 hkw1 hkw2 (fun c _ h => h) hmsub).mp hsk
      rw [get?_bin, get?_bin]
      by_cases htb1 : testBit m1 (chunk k l1) = true
      · rw [if_pos htb1, if_pos (hmsub (chunk k l1) (chunk_lt k l1) htb1)]
        exact hchildsub (chunk k l1) (chunk_lt k l1) htb1 k
      · simp only [Bool.not_eq_true] at htb1
        rw [if_neg (show ¬ testBit m1 (chunk k l1) = true by rw [htb1]; exact Bool.false_ne_true)]
        rfl
    · intro hsub
      have hp : p1 = p2 := by
        obtain ⟨j0, x0, hx0⟩ := exists_get?_some (.bin p1 l1 m1 k1) hwa (by simp)
        have hj0 : contains j0 (.bin p1 l1 m1 k1) = true := by rw [contains_eq_isSome, hx0]; rfl
        have hj0b : contains j0 (.bin p2 l1 m2 k2) = true :=
          contains_of_optRel rel j0 _ _ hj0 (hsub j0)
        have e1 : prefixAbove j0 l1 = p1 := prefixAbove_eq_of_mem p1 l1 m1 k1 hwa j0 hj0
        have e2 : prefixAbove j0 l1 = p2 := prefixAbove_eq_of_mem p2 l1 m2 k2 hwb j0 hj0b
        rw [← e1, e2]
      have hmsub : ∀ c, c < 32 → testBit m1 c = true → testBit m2 c = true := by
        intro c hc htb
        have hwfc : WF (childAt m1 k1 c) := hkidswf1 _ (childAt_mem m1 k1 c hsize1 htb)
        have hnec : childAt m1 k1 c ≠ .nil := hnonnil1 _ (childAt_mem m1 k1 c hsize1 htb)
        obtain ⟨j, hj⟩ := exists_mem _ hwfc hnec
        have hjbin1 : contains j (.bin p1 l1 m1 k1) = true :=
          mem_child_imp_mem_bin p1 l1 m1 k1 hwa c hc htb j hj
        have hjbin2 : contains j (.bin p2 l1 m2 k2) = true :=
          contains_of_optRel rel j _ _ hjbin1 (hsub j)
        have hcj : chunk j l1 = c := (hrout1 c hc htb j hj).1
        rw [contains_bin, hcj, Bool.and_eq_true] at hjbin2; exact hjbin2.1
      have hchildsub : ∀ c, c < 32 → testBit m1 c = true →
          ∀ k, optRel rel (get? k (childAt m1 k1 c)) (get? k (childAt m2 k2 c)) = true := by
        intro c hc htb k
        by_cases hck : chunk k l1 = c
        · have hk := hsub k
          rw [get?_bin, get?_bin, hck, if_pos htb, if_pos (hmsub c hc htb)] at hk
          exact hk
        · rw [get?_eq_none_of_contains_false k (childAt m1 k1 c)
              (contains_false_of_aligned l1 c p1 (childAt m1 k1 c) (hrout1 c hc htb) hck)]
          rfl
      exact ⟨⟨hp, hmsub⟩, (ih2 hkw1 hkw2 (fun c _ h => h) hmsub).mpr hchildsub⟩
  | case8 p1 l1 m1 k1 p2 l2 m2 k2 hne hlt ih =>
    intro hwa hwb
    have hwb' := hwb; rw [WF] at hwb'
    obtain ⟨hl2, hsize2, hpc2, hkidswf2, hnonnil2, hrout2⟩ := hwb'
    have hm2 : m2 ≠ 0 := by intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc2; omega
    have halign := aligned_bin p1 l1 m1 k1 hwa l2 hlt
    rw [subsetU, if_neg hne, if_pos hlt, someKey_bin_prefixAbove p2 l2 m2 k2 hm2]
    constructor
    · intro hcond
      rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨hpre, htb⟩, hdite⟩ := hcond
      have hidx : arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) < k2.size := by
        rw [hsize2]; exact arrayIndex_lt m2 _ htb
      rw [dif_pos hidx] at hdite
      have hchild : k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'hidx
                      = childAt m2 k2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) := by
        unfold childAt; rw [Array.getElem?_eq_getElem hidx, Option.getD_some]
      have hwfbkidx := hkidswf2 _ (Array.getElem_mem hidx)
      have hrec := (ih hidx hwa hwfbkidx).mp hdite
      rw [hchild] at hrec
      exact (optRel_descend rel (.bin p1 l1 m1 k1) p2 l2 m2 k2
        (chunk (someKey (.bin p1 l1 m1 k1)) l2) (prefixAbove (someKey (.bin p1 l1 m1 k1)) l2)
        halign htb).mp hrec
    · intro hsub
      obtain ⟨j0, x0, hx0⟩ := exists_get?_some (.bin p1 l1 m1 k1) hwa (by simp)
      have hj0 : contains j0 (.bin p1 l1 m1 k1) = true := by rw [contains_eq_isSome, hx0]; rfl
      have hj0bin : contains j0 (.bin p2 l2 m2 k2) = true :=
        contains_of_optRel rel j0 (.bin p1 l1 m1 k1) (.bin p2 l2 m2 k2) hj0 (hsub j0)
      have hchunk0 : chunk j0 l2 = chunk (someKey (.bin p1 l1 m1 k1)) l2 := (halign j0 hj0).1
      have hpre0 : prefixAbove j0 l2 = prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 :=
        (halign j0 hj0).2
      rw [contains_bin, hchunk0, Bool.and_eq_true] at hj0bin
      obtain ⟨htb, hchildmem⟩ := hj0bin
      have hidx : arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) < k2.size := by
        rw [hsize2]; exact arrayIndex_lt m2 _ htb
      have hprebp : prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 = p2 := by
        rw [← hpre0]
        exact prefixAbove_eq_of_mem p2 l2 m2 k2 hwb j0
          (by rw [contains_bin, hchunk0, htb, Bool.true_and]; exact hchildmem)
      have hchild : k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'hidx
                      = childAt m2 k2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) := by
        unfold childAt; rw [Array.getElem?_eq_getElem hidx, Option.getD_some]
      have hwfbkidx := hkidswf2 _ (Array.getElem_mem hidx)
      rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨hprebp, htb⟩, ?_⟩
      rw [dif_pos hidx]
      apply (ih hidx hwa hwfbkidx).mpr
      have hbridge := (optRel_descend rel (.bin p1 l1 m1 k1) p2 l2 m2 k2
        (chunk (someKey (.bin p1 l1 m1 k1)) l2) (prefixAbove (someKey (.bin p1 l1 m1 k1)) l2)
        halign htb).mpr hsub
      rw [← hchild] at hbridge; exact hbridge
  | case9 p1 l1 m1 k1 p2 l2 m2 k2 hne hnlt =>
    intro hwa hwb
    apply iff_of_false
    · intro h; rw [subsetU, if_neg hne, if_neg hnlt] at h; exact absurd h (by decide)
    · intro hsub
      obtain ⟨j1, j2, hj1, hj2, hdiv⟩ := exists_two_divergent p1 l1 m1 k1 hwa
      have hj1b := contains_of_optRel rel j1 _ _ hj1 (hsub j1)
      have hj2b := contains_of_optRel rel j2 _ _ hj2 (hsub j2)
      have e1 : prefixAbove j1 l2 = p2 := prefixAbove_eq_of_mem p2 l2 m2 k2 hwb j1 hj1b
      have e2 : prefixAbove j2 l2 = p2 := prefixAbove_eq_of_mem p2 l2 m2 k2 hwb j2 hj2b
      have hl2lt : l2 < l1 := by
        have hne' : l1 ≠ l2 := by intro he; apply hne; rw [he]; simp
        omega
      exact hdiv (chunk_eq_of_prefixAbove_lt (e1.trans e2.symm) hl2lt)
  | case10 m1 k1 m2 k2 rem hrem =>
    rename_i hkw1 hkw2 hr1 hr2
    have hrem0 : rem = 0 := eq_of_beq hrem
    rw [subsetKids, dif_pos hrem]
    refine iff_of_true rfl (fun c hc htb k => ?_)
    rw [hrem0, testBit_zero] at htb; exact absurd htb (by decide)
  | case11 m1 k1 m2 k2 rem hrem ihchild ihrec =>
    rename_i hkw1 hkw2 hr1 hr2
    have hrem0 : rem ≠ 0 := by intro h; rw [h] at hrem; exact hrem (by decide)
    have hc0lt : lowestSetIdx rem < 32 := lowestSetIdx_lt rem hrem0
    have hc0rem : testBit rem (lowestSetIdx rem) = true := testBit_lowestSetIdx rem hrem0
    have htbm1 : testBit m1 (lowestSetIdx rem) = true := hr1 _ hc0lt hc0rem
    have htbm2 : testBit m2 (lowestSetIdx rem) = true := hr2 _ hc0lt hc0rem
    have h1 : arrayIndex m1 (lowestSetIdx rem) < k1.size := by
      rw [hkw1.1]; exact arrayIndex_lt m1 _ htbm1
    have h2 : arrayIndex m2 (lowestSetIdx rem) < k2.size := by
      rw [hkw2.1]; exact arrayIndex_lt m2 _ htbm2
    have hch1 : k1[arrayIndex m1 (lowestSetIdx rem)]'h1 = childAt m1 k1 (lowestSetIdx rem) := by
      unfold childAt; rw [Array.getElem?_eq_getElem h1, Option.getD_some]
    have hch2 : k2[arrayIndex m2 (lowestSetIdx rem)]'h2 = childAt m2 k2 (lowestSetIdx rem) := by
      unfold childAt; rw [Array.getElem?_eq_getElem h2, Option.getD_some]
    have hwf1 := hkw1.2.1 _ (childAt_mem m1 k1 _ hkw1.1 htbm1)
    have hwf2 := hkw2.2.1 _ (childAt_mem m2 k2 _ hkw2.1 htbm2)
    have hce : subsetU rel (childAt m1 k1 (lowestSetIdx rem)) (childAt m2 k2 (lowestSetIdx rem)) = true ↔
        ∀ k, optRel rel (get? k (childAt m1 k1 (lowestSetIdx rem)))
              (get? k (childAt m2 k2 (lowestSetIdx rem))) = true := by
      have hih := ihchild h1 h2; rw [hch1, hch2] at hih; exact hih hwf1 hwf2
    have hre := ihrec hkw1 hkw2
      (fun c hc h => hr1 c hc (testBit_of_clearLowest rem c h))
      (fun c hc h => hr2 c hc (testBit_of_clearLowest rem c h))
    rw [subsetKids, dif_neg hrem, dif_pos h1, dif_pos h2, hch1, hch2, Bool.and_eq_true, hce, hre]
    constructor
    · rintro ⟨hP0, hPrest⟩ c hc htbc k
      by_cases hcc0 : c = lowestSetIdx rem
      · rw [hcc0]; exact hP0 k
      · rw [← testBit_clearLowest_of_ne rem c hc hcc0] at htbc
        exact hPrest c hc htbc k
    · intro hall
      exact ⟨fun k => hall (lowestSetIdx rem) hc0lt hc0rem k,
             fun c hc htbcl k => hall c hc (testBit_of_clearLowest rem c htbcl) k⟩

/-- `subset rel a b` decides the value-aware restriction order; stated on `subset`, the work is in
`subset_iff`. -/
theorem subset_iff_eq (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (a b : PTree L)
    (hwa : WF a) (hwb : WF b) :
    subset rel a b = true ↔ ∀ k, optRel rel (get? k a) (get? k b) = true := by
  rw [subset]; exact subset_iff rel hrefl a b hwa hwb

/-! ### Lattice and order laws (generic `PTree L`)

The value-level algebra (`optVjoin`/`optVmeet`/`optRel` on `Option V`) lifts to the tree level
through the four seams + `ext_get?`: a structural equality reduces to a pointwise `Option`-algebra
identity, and an order fact to a pointwise `optRel` fact. Each law carries exactly the combine
hypotheses its value-level counterpart needs (commutativity, idempotence, transitivity, …). The
template the migration re-exports on `NatSet`/`NatMap`. -/

private theorem get?_empty (j : Nat) : get? j (empty : PTree L) = none := get?_nil j

private theorem optVjoin_idem (cf : V → V → V) (hidem : ∀ x, cf x x = x) (ox : Option V) :
    optVjoin cf ox ox = ox := by cases ox <;> simp only [optVjoin] <;> rw [hidem]

private theorem optVmeet_idem (cf : V → V → V) (hidem : ∀ x, cf x x = x) (ox : Option V) :
    optVmeet cf ox ox = ox := by cases ox <;> simp only [optVmeet] <;> rw [hidem]

private theorem optVjoin_comm (cf : V → V → V) (hc : ∀ x y, cf x y = cf y x) (ox oy : Option V) :
    optVjoin cf ox oy = optVjoin cf oy ox := by
  cases ox <;> cases oy <;> simp only [optVjoin] <;> first | rfl | rw [hc]

private theorem optVmeet_comm (cf : V → V → V) (hc : ∀ x y, cf x y = cf y x) (ox oy : Option V) :
    optVmeet cf ox oy = optVmeet cf oy ox := by
  cases ox <;> cases oy <;> simp only [optVmeet] <;> first | rfl | rw [hc]

private theorem optRel_refl (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (ox : Option V) :
    optRel rel ox ox = true := by
  cases ox with
  | none => rfl
  | some x => exact hrefl x

private theorem optRel_trans (rel : V → V → Bool)
    (htrans : ∀ x y z, rel x y = true → rel y z = true → rel x z = true)
    (oa ob oc : Option V) (h1 : optRel rel oa ob = true) (h2 : optRel rel ob oc = true) :
    optRel rel oa oc = true := by
  cases oa with
  | none => rfl
  | some x => cases ob with
    | none => simp [optRel] at h1
    | some y => cases oc with
      | none => simp [optRel] at h2
      | some z => simp only [optRel] at h1 h2 ⊢; exact htrans x y z h1 h2

private theorem optRel_antisymm (rel : V → V → Bool)
    (hanti : ∀ x y, rel x y = true → rel y x = true → x = y)
    (oa ob : Option V) (h1 : optRel rel oa ob = true) (h2 : optRel rel ob oa = true) :
    oa = ob := by
  cases oa with
  | none => cases ob with
    | none => rfl
    | some y => simp [optRel] at h2
  | some x => cases ob with
    | none => simp [optRel] at h1
    | some y => simp only [optRel] at h1 h2; rw [hanti x y h1 h2]

/-- `union` with the empty map on the right is the identity. -/
theorem union_empty (cf : V → V → V) (a : PTree L) (hwa : WF a) : union cf a empty = a :=
  ext_get? (union cf a empty) a (WF_union cf a empty hwa WF_empty) hwa (fun j => by
    rw [get?_union cf j a empty hwa WF_empty, get?_empty, optVjoin_none_right])

/-- `union` with the empty map on the left is the identity. -/
theorem empty_union (cf : V → V → V) (a : PTree L) (hwa : WF a) : union cf empty a = a :=
  ext_get? (union cf empty a) a (WF_union cf empty a WF_empty hwa) hwa (fun j => by
    rw [get?_union cf j empty a WF_empty hwa, get?_empty, optVjoin_none_left])

/-- `meet` with the empty map is empty (annihilator). -/
theorem meet_empty (cf : V → V → V) (a : PTree L) (hwa : WF a) : meet cf a empty = empty :=
  ext_get? (meet cf a empty) empty (WF_meet cf a empty hwa WF_empty) WF_empty (fun j => by
    rw [get?_meet cf j a empty hwa WF_empty, get?_empty, optVmeet_none_right])

/-- `meet` with the empty map on the left is empty. -/
theorem empty_meet (cf : V → V → V) (a : PTree L) (hwa : WF a) : meet cf empty a = empty :=
  ext_get? (meet cf empty a) empty (WF_meet cf empty a WF_empty hwa) WF_empty (fun j => by
    rw [get?_meet cf j empty a WF_empty hwa, get?_empty, optVmeet_none_left])

/-- `union` is commutative when its combine is. -/
theorem union_comm (cf : V → V → V) (hc : ∀ x y, cf x y = cf y x) (a b : PTree L)
    (hwa : WF a) (hwb : WF b) : union cf a b = union cf b a :=
  ext_get? (union cf a b) (union cf b a) (WF_union cf a b hwa hwb) (WF_union cf b a hwb hwa)
    (fun j => by rw [get?_union cf j a b hwa hwb, get?_union cf j b a hwb hwa, optVjoin_comm cf hc])

/-- `meet` is commutative when its combine is. -/
theorem meet_comm (cf : V → V → V) (hc : ∀ x y, cf x y = cf y x) (a b : PTree L)
    (hwa : WF a) (hwb : WF b) : meet cf a b = meet cf b a :=
  ext_get? (meet cf a b) (meet cf b a) (WF_meet cf a b hwa hwb) (WF_meet cf b a hwb hwa)
    (fun j => by rw [get?_meet cf j a b hwa hwb, get?_meet cf j b a hwb hwa, optVmeet_comm cf hc])

/-- `union` is idempotent when its combine is. -/
theorem union_self (cf : V → V → V) (hidem : ∀ x, cf x x = x) (a : PTree L) (hwa : WF a) :
    union cf a a = a :=
  ext_get? (union cf a a) a (WF_union cf a a hwa hwa) hwa
    (fun j => by rw [get?_union cf j a a hwa hwa, optVjoin_idem cf hidem])

/-- `meet` is idempotent when its combine is. -/
theorem meet_self (cf : V → V → V) (hidem : ∀ x, cf x x = x) (a : PTree L) (hwa : WF a) :
    meet cf a a = a :=
  ext_get? (meet cf a a) a (WF_meet cf a a hwa hwa) hwa
    (fun j => by rw [get?_meet cf j a a hwa hwa, optVmeet_idem cf hidem])

/-- The restriction order is reflexive (when `rel` is). -/
theorem subset_refl (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (a : PTree L) (hwa : WF a) :
    subset rel a a = true :=
  (subset_iff_eq rel hrefl a a hwa hwa).mpr (fun k => optRel_refl rel hrefl (get? k a))

/-- The restriction order is transitive (when `rel` is). -/
theorem subset_trans (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (htrans : ∀ x y z, rel x y = true → rel y z = true → rel x z = true)
    (a b c : PTree L) (hwa : WF a) (hwb : WF b) (hwc : WF c)
    (hab : subset rel a b = true) (hbc : subset rel b c = true) : subset rel a c = true :=
  (subset_iff_eq rel hrefl a c hwa hwc).mpr (fun k =>
    optRel_trans rel htrans (get? k a) (get? k b) (get? k c)
      ((subset_iff_eq rel hrefl a b hwa hwb).mp hab k)
      ((subset_iff_eq rel hrefl b c hwb hwc).mp hbc k))

/-- The restriction order is antisymmetric (when `rel` is): mutual restriction forces equality. -/
theorem subset_antisymm (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (hanti : ∀ x y, rel x y = true → rel y x = true → x = y)
    (a b : PTree L) (hwa : WF a) (hwb : WF b)
    (hab : subset rel a b = true) (hba : subset rel b a = true) : a = b :=
  ext_get? a b hwa hwb (fun j => optRel_antisymm rel hanti (get? j a) (get? j b)
    ((subset_iff_eq rel hrefl a b hwa hwb).mp hab j)
    ((subset_iff_eq rel hrefl b a hwb hwa).mp hba j))

end PTree
end NatCol
