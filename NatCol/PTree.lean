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
import NatCol.Node

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
@[inline] private def prefixAbove (k level : Nat) : Nat := k >>> (5 * (level + 1))

/-- The highest 5-bit chunk index at which `a` and `b` differ (meaningful only for `a ≠ b`):
the chunk holding the top set bit of `a ^^^ b`. -/
@[inline] private def branchLevel (a b : Nat) : Nat := requiredHeight (a ^^^ b)

/-- An arbitrary member key (O(1); bits below the node's level are left `0`, which is all
`branchLevel`/prefix comparisons need). A `tip`'s representative slot comes from the leaf
(`LeafOps.someSlot`). -/
private def someKey : PTree L → Nat
  | .nil                  => 0
  | .tip pfx leaf         => (pfx <<< 5) ||| (LeafOps.someSlot leaf).toNat
  | .bin pfx level mask _ => (pfx <<< (5 * (level + 1))) ||| ((lowestSetIdx mask).toNat <<< (5 * level))

/-- The empty collection. -/
@[inline] def empty : PTree L := .nil

/-- The singleton `{k ↦ v}` — a single `tip`, no interior nodes. -/
@[inline] private def singleton (k : Nat) (v : V) : PTree L :=
  .tip (k >>> 5) (LeafOps.insert LeafOps.empty (chunk k 0) v)

/-- Combine two subtrees with **disjoint** prefixes (representative keys `ka ≠ kb`) under a fresh
`bin` branching at their first differing chunk. -/
@[inline] private def join (ka : Nat) (a : PTree L) (kb : Nat) (b : PTree L) : PTree L :=
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

/-- Append every `(key, value)` pair to `acc`, in ascending key order. A `tip` enumerates its leaf
(`LeafOps.toArray`, ascending slots), reconstructing each full key from the tip's prefix; a `bin`
visits its children left-to-right (children sit in ascending chunk-at-level order), so the whole
walk is ascending. -/
private def toArrayAux : Array (Nat × V) → PTree L → Array (Nat × V)
  | acc, .nil            => acc
  | acc, .tip pfx leaf   =>
      (LeafOps.toArray leaf).foldl (fun a sv => a.push ((pfx <<< 5) ||| sv.1.toNat, sv.2)) acc
  | acc, .bin _ _ _ kids => kids.attach.foldl (fun a ⟨c, _⟩ => toArrayAux a c) acc
termination_by _ t => sizeOf t
decreasing_by
  simp_wf
  rename_i c hc
  have := Array.sizeOf_lt_of_mem hc
  omega

/-- All `(key, value)` pairs of the trie, ascending by key. -/
@[inline] def toArray (t : PTree L) : Array (Nat × V) := toArrayAux #[] t

-- Structural traversals: the fold family walks the trie directly (same ascending order as
-- `toArrayAux`, whose key reconstruction the `tip` cases reuse) instead of materializing
-- `toArray` first. `all`/`any` thread a `Bool` accumulator through `&&`/`||`, whose lazy second
-- argument skips both the predicate and the child recursion once the answer is decided (the
-- `restrictsLoop` shape); the monadic pair skips the predicate the same way, explicitly.

/-- Fold `f` over all present `(key, value)` pairs, ascending by key, starting from `init`. -/
@[specialize] def foldl {β : Type w} (f : β → Nat → V → β) (init : β) : PTree L → β
  | .nil            => init
  | .tip pfx leaf   =>
      (LeafOps.toArray leaf).foldl (fun acc sv => f acc ((pfx <<< 5) ||| sv.1.toNat) sv.2) init
  | .bin _ _ _ kids => kids.attach.foldl (fun acc ⟨c, _⟩ => foldl f acc c) init
termination_by t => sizeOf t
decreasing_by
  simp_wf
  rename_i c hc
  have := Array.sizeOf_lt_of_mem hc
  omega

/-- Monadic fold over all present `(key, value)` pairs, ascending by key, starting from `init`. -/
@[specialize] def foldlM {β : Type w} {m : Type w → Type w'} [Monad m] (f : β → Nat → V → m β)
    (init : β) : PTree L → m β
  | .nil            => pure init
  | .tip pfx leaf   =>
      (LeafOps.toArray leaf).foldlM (fun acc sv => f acc ((pfx <<< 5) ||| sv.1.toNat) sv.2) init
  | .bin _ _ _ kids => kids.attach.foldlM (fun acc ⟨c, _⟩ => foldlM f acc c) init
termination_by t => sizeOf t
decreasing_by
  simp_wf
  rename_i c hc
  have := Array.sizeOf_lt_of_mem hc
  omega

/-- Whether every present `(key, value)` pair satisfies `p`, short-circuiting at the first
failure. -/
@[specialize] def all (p : Nat → V → Bool) : PTree L → Bool
  | .nil            => true
  | .tip pfx leaf   => (LeafOps.toArray leaf).all (fun sv => p ((pfx <<< 5) ||| sv.1.toNat) sv.2)
  | .bin _ _ _ kids => kids.attach.foldl (fun acc ⟨c, _⟩ => acc && all p c) true
termination_by t => sizeOf t
decreasing_by
  simp_wf
  rename_i c hc
  have := Array.sizeOf_lt_of_mem hc
  omega

/-- Whether some present `(key, value)` pair satisfies `p`, short-circuiting at the first
success. -/
@[specialize] def any (p : Nat → V → Bool) : PTree L → Bool
  | .nil            => false
  | .tip pfx leaf   => (LeafOps.toArray leaf).any (fun sv => p ((pfx <<< 5) ||| sv.1.toNat) sv.2)
  | .bin _ _ _ kids => kids.attach.foldl (fun acc ⟨c, _⟩ => acc || any p c) false
termination_by t => sizeOf t
decreasing_by
  simp_wf
  rename_i c hc
  have := Array.sizeOf_lt_of_mem hc
  omega

/-- Monadic `all`: threads effects in ascending key order, skipping `p` once a failure is seen. -/
@[specialize] def allM {m : Type → Type w} [Monad m] (p : Nat → V → m Bool) : PTree L → m Bool
  | .nil            => pure true
  | .tip pfx leaf   => (LeafOps.toArray leaf).allM (fun sv => p ((pfx <<< 5) ||| sv.1.toNat) sv.2)
  | .bin _ _ _ kids =>
      kids.attach.foldlM (fun acc ⟨c, _⟩ => if acc then allM p c else pure false) true
termination_by t => sizeOf t
decreasing_by
  simp_wf
  rename_i c hc
  have := Array.sizeOf_lt_of_mem hc
  omega

/-- Monadic `any`: threads effects in ascending key order, skipping `p` once a success is seen. -/
@[specialize] def anyM {m : Type → Type w} [Monad m] (p : Nat → V → m Bool) : PTree L → m Bool
  | .nil            => pure false
  | .tip pfx leaf   => (LeafOps.toArray leaf).anyM (fun sv => p ((pfx <<< 5) ||| sv.1.toNat) sv.2)
  | .bin _ _ _ kids =>
      kids.attach.foldlM (fun acc ⟨c, _⟩ => if acc then pure true else anyM p c) false
termination_by t => sizeOf t
decreasing_by
  simp_wf
  rename_i c hc
  have := Array.sizeOf_lt_of_mem hc
  omega

-- Structural equality. On WF (canonical) tries this coincides with logical equality
-- (`eq_of_beq`/`beq_refl`), which is what makes the `NatCollection` `BEq` lawful. Children are
-- compared via `beqList` on `kids.toList`, so the lawfulness proofs are clean structural inductions
-- (`Array.toList` is injective).
mutual
/-- Structural equality of two tries (see the note above the `mutual` block). -/
@[specialize] def beq [BEq L] : PTree L → PTree L → Bool
  | .nil,             .nil             => true
  | .tip p1 l1,       .tip p2 l2       => (p1 == p2) && (l1 == l2)
  | .bin p1 v1 m1 k1, .bin p2 v2 m2 k2 =>
      (p1 == p2) && (v1 == v2) && (m1 == m2) && beqList k1.toList k2.toList
  | _,                _                => false
/-- Element-wise structural equality of two child lists (the `beq` companion). -/
@[specialize] private def beqList [BEq L] : List (PTree L) → List (PTree L) → Bool
  | [],       []       => true
  | c1 :: r1, c2 :: r2 => beq c1 c2 && beqList r1 r2
  | _,        _        => false
end

/-- Total child accessor: the subtree a `bin`'s mask routes slot `c` to, `nil` when the slot is
absent (or the compact index is out of range). Gives every membership/merge proof one total
accessor in place of the raw `dite` bounds juggling. -/
@[inline] private def childAt (mask : UInt32) (kids : Array (PTree L)) (c : UInt32) : PTree L :=
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
private def unionU (c : V → V → V) : PTree L → PTree L → PTree L
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
      .bin p1 l1 (m1 ||| m2)
        (mergeKids c m1 k1 m2 k2 (m1 ||| m2) (Array.emptyWithCapacity (popCount (m1 ||| m2))))
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
private def mergeChild (c : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32) (k2 : Array (PTree L)) (i : UInt32) : PTree L :=
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
private def mergeKids (c : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32) (k2 : Array (PTree L))
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
         toNat_clearLowest_lt rem (by simp_all); omega)
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
private def subsetKids (rel : V → V → Bool) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32) (k2 : Array (PTree L)) (rem : UInt32) :
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
         toNat_clearLowest_lt rem (by simp_all); omega)
    | omega
end

/-- `a ⊆ b`: every key of `a` is in `b` (with values related by `rel` at coinciding keys), via the
structural Patricia walk. -/
@[inline] def subset (rel : V → V → Bool) (a b : PTree L) : Bool := subsetU rel a b

-- Disjointness — the intersection's routing without the intersection: the walk answers `true` the
-- moment two shapes cannot share a key (prefix mismatch, off mask), compares aligned leaves with
-- one occupancy-mask `AND` (`LeafOps.disjoint`), and short-circuits the whole remaining scan at
-- the first shared key. Never allocates, unlike `isEmpty (meet …)`, which builds the intersection
-- only to discard it.
set_option linter.unusedVariables false in
mutual
/-- Disjointness driver — `meetU`'s case analysis returning `Bool`: `nil` is disjoint from
everything, aligned `tip`s compare leaf masks, a `tip` or off-level `bin` descends into the one
routed child (absent ⇒ vacuously disjoint), equal-level `bin`s scan only the shared mask
(`disjointKids`). -/
private def disjointU : PTree L → PTree L → Bool
  | .nil, _ => true
  | _, .nil => true
  | .tip p1 b1, .tip p2 b2 => p1 != p2 || LeafOps.disjoint b1 b2
  | .tip p1 b1, .bin bp bl bm bk =>
    if prefixAbove (someKey (.tip p1 b1)) bl == bp
        && testBit bm (chunk (someKey (.tip p1 b1)) bl) then
      if h : arrayIndex bm (chunk (someKey (.tip p1 b1)) bl) < bk.size then
        disjointU (.tip p1 b1) (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h)
      else true
    else true
  | .bin bp bl bm bk, .tip p2 b2 =>
    if prefixAbove (someKey (.tip p2 b2)) bl == bp
        && testBit bm (chunk (someKey (.tip p2 b2)) bl) then
      if h : arrayIndex bm (chunk (someKey (.tip p2 b2)) bl) < bk.size then
        disjointU (bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h) (.tip p2 b2)
      else true
    else true
  | .bin p1 l1 m1 k1, .bin p2 l2 m2 k2 =>
    if l1 == l2 then
      if prefixAbove (someKey (.bin p1 l1 m1 k1)) l1
          == prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 then
        disjointKids m1 k1 m2 k2 (m1 &&& m2)
      else true
    else if l2 < l1 then
      if prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 == p1
          && testBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) then
        if h : arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) < k1.size then
          disjointU (k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h) (.bin p2 l2 m2 k2)
        else true
      else true
    else
      if prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 == p2
          && testBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) then
        if h : arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) < k2.size then
          disjointU (.bin p1 l1 m1 k1) (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h)
        else true
      else true
termination_by a b => (sizeOf a + sizeOf b, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := Array.sizeOf_lt_of_mem (Array.getElem_mem h); omega)

/-- Confirm pairwise disjointness at every shared slot of two aligned bins, bit-scanning the
shared mask `rem` (= `m1 &&& m2`) lowest-first; `&&`'s lazy right argument skips the remaining
subtree walks the moment a shared key is found. An empty shared mask is vacuously disjoint. -/
private def disjointKids (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) (rem : UInt32) : Bool :=
  if hrem : rem == 0 then true
  else
    (if h1 : arrayIndex m1 (lowestSetIdx rem) < k1.size then
      if h2 : arrayIndex m2 (lowestSetIdx rem) < k2.size then
        disjointU (k1[arrayIndex m1 (lowestSetIdx rem)]'h1) (k2[arrayIndex m2 (lowestSetIdx rem)]'h2)
      else true
    else true)
      && disjointKids m1 k1 m2 k2 (clearLowest rem)
termination_by (sizeOf k1 + sizeOf k2 + 1, rem.toNat)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := Array.sizeOf_lt_of_mem (Array.getElem_mem h1)
       have := Array.sizeOf_lt_of_mem (Array.getElem_mem h2); omega)
    | (have : (clearLowest rem).toNat < rem.toNat :=
         toNat_clearLowest_lt rem (by simp_all); omega)
    | omega
end

/-- Whether `a` and `b` share no key: the structural disjointness walk (allocation-free,
short-circuiting at the first shared key). -/
@[inline] def isDisjoint (a b : PTree L) : Bool := disjointU a b

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
private def compactify (mask : UInt32) (kids : Array (PTree L)) (rem : UInt32) (accM : UInt32)
    (acc : Array (PTree L)) : UInt32 × Array (PTree L) :=
  if _hrem : rem == 0 then (accM, acc)
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
      toNat_clearLowest_lt rem (by simp_all)
    omega

/-- Re-wrap a re-compressed branch: empty → `nil`, a single survivor → that child (lift the
collapsed level — the path-compression step), otherwise a `bin`. -/
private def finalize (p l : Nat) (mask : UInt32) (kids : Array (PTree L)) : PTree L :=
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
private def meetU (c : V → V → V) : PTree L → PTree L → PTree L
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
        finalize p1 l1 (m1 &&& m2)
          (meetKids c m1 k1 m2 k2 (m1 &&& m2) (Array.emptyWithCapacity (popCount (m1 &&& m2))))
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
private def meetChild (c : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32) (k2 : Array (PTree L)) (i : UInt32) :
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
private def meetKids (c : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32) (k2 : Array (PTree L))
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
         toNat_clearLowest_lt rem (by simp_all); omega)
end

/-- Intersection `a ∩ b`, resolving coinciding keys with `c`. -/
@[inline] def meet (c : V → V → V) (a b : PTree L) : PTree L := meetU c a b

-- Filter & erase — both can empty children, leaving a branch non-minimal, so both reuse the
-- intersection's re-compression (`finalize`). `filterU` rebuilds every child under the bin's mask
-- (`filterKids`/`filterChild`, the single-operand `meetKids`/`meetChild` twins); `eraseU` descends
-- only the routed path (`insert`'s routing) and re-finalizes the touched branch. The mutual
-- measure tags `filterU` with `1` in the second component: its hand-off to `filterKids` drops to
-- the strictly-smaller `kids`, and `filterChild`'s hand-back enters a strictly-smaller child.

set_option linter.unusedVariables false in
mutual
/-- Keep only the `(key, value)` pairs satisfying `p`: filter each `tip`'s leaf (dropping the tip
if it empties), rebuild each branch's children under its mask, and re-compress (`finalize`). -/
private def filterU (p : Nat → V → Bool) : PTree L → PTree L
  | .nil          => .nil
  | .tip pfx leaf =>
    if LeafOps.isEmpty (LeafOps.filter (fun s v => p ((pfx <<< 5) ||| s.toNat) v) leaf) then .nil
    else .tip pfx (LeafOps.filter (fun s v => p ((pfx <<< 5) ||| s.toNat) v) leaf)
  | .bin pfx level mask kids =>
    finalize pfx level mask
      (filterKids p mask kids mask (Array.emptyWithCapacity (popCount mask)))
termination_by t => (sizeOf t, 1)
decreasing_by
  simp_wf
  omega

/-- The filtered child at a present slot `i` (the single-operand `meetChild`). -/
private def filterChild (p : Nat → V → Bool) (mask : UInt32) (kids : Array (PTree L))
    (i : UInt32) : PTree L :=
  if h : arrayIndex mask i < kids.size then filterU p (kids[arrayIndex mask i]'h)
  else .nil
termination_by (sizeOf kids, 0)
decreasing_by
  simp_wf
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem h)
  omega

/-- Fold over the mask `rem`, appending each slot's `filterChild` (lowest first): compact under
the bin's mask, `nil` where the filter emptied a child (those are pruned by `compactify`). -/
private def filterKids (p : Nat → V → Bool) (mask : UInt32) (kids : Array (PTree L))
    (rem : UInt32) (acc : Array (PTree L)) : Array (PTree L) :=
  if hrem : rem == 0 then acc
  else
    filterKids p mask kids (clearLowest rem)
      (acc.push (filterChild p mask kids (lowestSetIdx rem)))
termination_by (sizeOf kids, rem.toNat)
decreasing_by
  all_goals simp_wf
  all_goals
    have hrem0 : rem ≠ 0 := by simp_all
  · have : rem.toNat ≠ 0 := fun hh => hrem0 (UInt32.toNat_inj.mp (by rw [hh]; rfl))
    omega
  · have := toNat_clearLowest_lt rem hrem0
    omega
end

set_option linter.unusedVariables false in
/-- Erase key `k`: descend the routed path (`insert`'s routing), erase the bottom chunk's slot at
the `tip` (dropping the tip if its leaf empties), and re-compress the touched branch (`finalize` —
the erased child may have emptied or collapsed, leaving the branch non-minimal). Off-path shapes
are returned unchanged, so erasing an absent key is a no-op. -/
private def eraseU (k : Nat) : PTree L → PTree L
  | .nil          => .nil
  | .tip pfx leaf =>
    if k >>> 5 == pfx then
      if LeafOps.isEmpty (LeafOps.erase leaf (chunk k 0)) then .nil
      else .tip pfx (LeafOps.erase leaf (chunk k 0))
    else .tip pfx leaf
  | .bin pfx level mask kids =>
    if prefixAbove k level == pfx && testBit mask (chunk k level) then
      if hb : arrayIndex mask (chunk k level) < kids.size then
        finalize pfx level mask
          (kids.set (arrayIndex mask (chunk k level))
            (eraseU k (kids[arrayIndex mask (chunk k level)]'hb)) hb)
      else .bin pfx level mask kids
    else .bin pfx level mask kids
decreasing_by
  simp_wf
  rename_i hb
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb)
  omega

/-- Keep only the `(key, value)` pairs satisfying `p` — one structural pass; the result is
canonical (`WF_filter`). -/
@[inline] def filter (p : Nat → V → Bool) (t : PTree L) : PTree L := filterU p t

/-- Erase key `k` (an absent key is a no-op) — descends just the routed path; the result is
canonical (`WF_erase`). -/
@[inline] def erase (k : Nat) (t : PTree L) : PTree L := eraseU k t

-- Difference — a structural merge, not a per-key probe: wherever the two prefixes cannot meet,
-- the left subtree is kept whole (and shared) in O(1); only genuinely overlapping paths are
-- walked. Aligned leaves subtract through `LeafOps.diff`. Like intersection, the result only
-- shrinks, so the touched branches re-compress through `finalize` (an aligned scan rebuilds all
-- of `m1`'s children via `diffKids`/`diffChild`, a routed hit splices one child via `set` +
-- `finalize`, the eraseU shape). The mutual measure is `meetU`'s.
set_option linter.unusedVariables false in
mutual
/-- Difference driver: `a \ b` keyed on shapes — `nil` minus anything is `nil`, anything minus
`nil` is itself; aligned `tip`s subtract leaves (dropping an emptied tip); a `b`-subtree routed
inside one child of `a` splices that child's difference back in (`finalize`); an `a`-subtree
routed inside one child of `b` descends; disjoint prefixes return `a` untouched. -/
private def diffU : PTree L → PTree L → PTree L
  | .nil, _ => .nil
  | .tip p1 b1, .nil => .tip p1 b1
  | .bin bp bl bm bk, .nil => .bin bp bl bm bk
  | .tip p1 b1, .tip p2 b2 =>
    if p1 == p2 then
      if LeafOps.isEmpty (LeafOps.diff b1 b2) then .nil else .tip p1 (LeafOps.diff b1 b2)
    else .tip p1 b1
  | .tip p1 b1, .bin bp bl bm bk =>
    if prefixAbove (someKey (.tip p1 b1)) bl == bp
        && testBit bm (chunk (someKey (.tip p1 b1)) bl) then
      if h : arrayIndex bm (chunk (someKey (.tip p1 b1)) bl) < bk.size then
        diffU (.tip p1 b1) (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h)
      else .tip p1 b1
    else .tip p1 b1
  | .bin bp bl bm bk, .tip p2 b2 =>
    if prefixAbove (someKey (.tip p2 b2)) bl == bp
        && testBit bm (chunk (someKey (.tip p2 b2)) bl) then
      if h : arrayIndex bm (chunk (someKey (.tip p2 b2)) bl) < bk.size then
        finalize bp bl bm
          (bk.set (arrayIndex bm (chunk (someKey (.tip p2 b2)) bl))
            (diffU (bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h) (.tip p2 b2)) h)
      else .bin bp bl bm bk
    else .bin bp bl bm bk
  | .bin p1 l1 m1 k1, .bin p2 l2 m2 k2 =>
    if l1 == l2 then
      if prefixAbove (someKey (.bin p1 l1 m1 k1)) l1
          == prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 then
        finalize p1 l1 m1
          (diffKids m1 k1 m2 k2 m1 (Array.emptyWithCapacity (popCount m1)))
      else .bin p1 l1 m1 k1
    else if l2 < l1 then
      if prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 == p1
          && testBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) then
        if h : arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) < k1.size then
          finalize p1 l1 m1
            (k1.set (arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1))
              (diffU (k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h)
                (.bin p2 l2 m2 k2)) h)
        else .bin p1 l1 m1 k1
      else .bin p1 l1 m1 k1
    else
      if prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 == p2
          && testBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) then
        if h : arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) < k2.size then
          diffU (.bin p1 l1 m1 k1) (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h)
        else .bin p1 l1 m1 k1
      else .bin p1 l1 m1 k1
termination_by a b => (sizeOf a + sizeOf b, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := Array.sizeOf_lt_of_mem (Array.getElem_mem h); omega)

/-- The differenced child at one of `m1`'s slots `i`: also present in `m2` → recurse with
`diffU`; present in `m1` alone → carry `a`'s child over whole (shared, untouched). -/
private def diffChild (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32) (k2 : Array (PTree L))
    (i : UInt32) : PTree L :=
  if h1 : arrayIndex m1 i < k1.size then
    if testBit m2 i then
      if h2 : arrayIndex m2 i < k2.size then
        diffU (k1[arrayIndex m1 i]'h1) (k2[arrayIndex m2 i]'h2)
      else k1[arrayIndex m1 i]'h1
    else k1[arrayIndex m1 i]'h1
  else .nil
termination_by (sizeOf k1 + sizeOf k2, 0)
decreasing_by
  all_goals simp_wf
  all_goals (have := Array.sizeOf_lt_of_mem (Array.getElem_mem h1)
             have := Array.sizeOf_lt_of_mem (Array.getElem_mem h2); omega)

/-- Fold over the leftover left mask `rem` (= `m1`), appending each present slot's `diffChild` to
`acc` (lowest first): compact under `m1`, `nil` where the subtraction emptied a child (pruned
later by `compactify`). -/
private def diffKids (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32) (k2 : Array (PTree L))
    (rem : UInt32) (acc : Array (PTree L)) : Array (PTree L) :=
  if hrem : rem == 0 then acc
  else
    diffKids m1 k1 m2 k2 (clearLowest rem) (acc.push (diffChild m1 k1 m2 k2 (lowestSetIdx rem)))
termination_by (sizeOf k1 + sizeOf k2 + 1, rem.toNat)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have : (clearLowest rem).toNat < rem.toNat :=
         toNat_clearLowest_lt rem (by simp_all); omega)
end

/-- Difference `a \ b`: the entries of `a` whose key is absent from `b` (`b`'s values are
irrelevant). A structural merge — subtrees of `a` that cannot meet `b` are kept whole (and
shared), never rebuilt or probed per key; the result is canonical (`WF_diff`). -/
@[inline] def diff (a b : PTree L) : PTree L := diffU a b

-- Symmetric difference — `unionU`'s skeleton with shrink handling: one-sided subtrees are carried
-- over whole (shared) exactly like union's, but where the operands genuinely overlap the entries
-- CANCEL (leaf case `LeafOps.symmDiff`; equal subtrees vanish entirely), so every recursion that
-- can shrink routes its result through `finalize` (the `set`+`finalize` splice, never union's
-- bare `setIfInBounds`), and the aligned-bin scan (`symmKids`/`symmChild`, `mergeKids`' twins
-- over `m1 ||| m2`) re-compresses through `finalize` too.
set_option linter.unusedVariables false in
mutual
/-- Symmetric-difference driver: entries whose key is in exactly one operand. `nil` is the
identity; aligned `tip`s cancel shared slots (dropping an emptied tip); an operand routed to a
present slot splices the recursive result back through `finalize` (it may have shrunk); one
routed to an absent slot is inserted whole; divergent prefixes `join` both operands whole; two
aligned `bin`s rebuild the union mask's children (`symmKids`) and re-compress. -/
private def symmDiffU : PTree L → PTree L → PTree L
  | .nil, t => t
  | .tip p1 b1, .nil => .tip p1 b1
  | .bin bp bl bm bk, .nil => .bin bp bl bm bk
  | .tip p1 b1, .tip p2 b2 =>
    if p1 == p2 then
      if LeafOps.isEmpty (LeafOps.symmDiff b1 b2) then .nil
      else .tip p1 (LeafOps.symmDiff b1 b2)
    else join (someKey (.tip p1 b1)) (.tip p1 b1) (someKey (.tip p2 b2)) (.tip p2 b2)
  | .tip p1 b1, .bin bp bl bm bk =>
    if prefixAbove (someKey (.tip p1 b1)) bl == bp then
      if testBit bm (chunk (someKey (.tip p1 b1)) bl) then
        if h : arrayIndex bm (chunk (someKey (.tip p1 b1)) bl) < bk.size then
          finalize bp bl bm
            (bk.set (arrayIndex bm (chunk (someKey (.tip p1 b1)) bl))
              (symmDiffU (.tip p1 b1) (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h)) h)
        else .bin bp bl bm bk
      else .bin bp bl (setBit bm (chunk (someKey (.tip p1 b1)) bl))
        (bk.insertIdx! (arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)) (.tip p1 b1))
    else join (someKey (.bin bp bl bm bk)) (.bin bp bl bm bk) (someKey (.tip p1 b1)) (.tip p1 b1)
  | .bin bp bl bm bk, .tip p2 b2 =>
    if prefixAbove (someKey (.tip p2 b2)) bl == bp then
      if testBit bm (chunk (someKey (.tip p2 b2)) bl) then
        if h : arrayIndex bm (chunk (someKey (.tip p2 b2)) bl) < bk.size then
          finalize bp bl bm
            (bk.set (arrayIndex bm (chunk (someKey (.tip p2 b2)) bl))
              (symmDiffU (bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h) (.tip p2 b2)) h)
        else .bin bp bl bm bk
      else .bin bp bl (setBit bm (chunk (someKey (.tip p2 b2)) bl))
        (bk.insertIdx! (arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)) (.tip p2 b2))
    else join (someKey (.bin bp bl bm bk)) (.bin bp bl bm bk) (someKey (.tip p2 b2)) (.tip p2 b2)
  | .bin p1 l1 m1 k1, .bin p2 l2 m2 k2 =>
    if l1 == l2 && p1 == p2 then
      finalize p1 l1 (m1 ||| m2)
        (symmKids m1 k1 m2 k2 (m1 ||| m2) (Array.emptyWithCapacity (popCount (m1 ||| m2))))
    else if l1 == l2 then
      join (someKey (.bin p1 l1 m1 k1)) (.bin p1 l1 m1 k1)
        (someKey (.bin p2 l2 m2 k2)) (.bin p2 l2 m2 k2)
    else if l2 < l1 then
      if prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 == p1 then
        if testBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) then
          if h : arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) < k1.size then
            finalize p1 l1 m1
              (k1.set (arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1))
                (symmDiffU (k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h)
                  (.bin p2 l2 m2 k2)) h)
          else .bin p1 l1 m1 k1
        else .bin p1 l1 (setBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1))
          (k1.insertIdx! (arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)) (.bin p2 l2 m2 k2))
      else join (someKey (.bin p1 l1 m1 k1)) (.bin p1 l1 m1 k1)
        (someKey (.bin p2 l2 m2 k2)) (.bin p2 l2 m2 k2)
    else
      if prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 == p2 then
        if testBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) then
          if h : arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) < k2.size then
            finalize p2 l2 m2
              (k2.set (arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2))
                (symmDiffU (.bin p1 l1 m1 k1)
                  (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h)) h)
          else .bin p2 l2 m2 k2
        else .bin p2 l2 (setBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2))
          (k2.insertIdx! (arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)) (.bin p1 l1 m1 k1))
      else join (someKey (.bin p2 l2 m2 k2)) (.bin p2 l2 m2 k2)
        (someKey (.bin p1 l1 m1 k1)) (.bin p1 l1 m1 k1)
termination_by a b => (sizeOf a + sizeOf b, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := Array.sizeOf_lt_of_mem (Array.getElem_mem h); omega)

/-- The symmetric-difference child at one union-mask slot `i`: present in both → recurse with
`symmDiffU` (the result may be `nil` — equal subtrees cancel; pruned later by `compactify`);
present in one → carry that side over whole. `mergeChild`'s shape. -/
private def symmChild (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32) (k2 : Array (PTree L))
    (i : UInt32) : PTree L :=
  if testBit m1 i then
    if testBit m2 i then
      if h1 : arrayIndex m1 i < k1.size then
        if h2 : arrayIndex m2 i < k2.size then
          symmDiffU (k1[arrayIndex m1 i]'h1) (k2[arrayIndex m2 i]'h2)
        else k1[arrayIndex m1 i]'h1
      else .nil
    else if h1 : arrayIndex m1 i < k1.size then k1[arrayIndex m1 i]'h1 else .nil
  else if h2 : arrayIndex m2 i < k2.size then k2[arrayIndex m2 i]'h2 else .nil
termination_by (sizeOf k1 + sizeOf k2, 0)
decreasing_by
  all_goals simp_wf
  all_goals (have := Array.sizeOf_lt_of_mem (Array.getElem_mem h1)
             have := Array.sizeOf_lt_of_mem (Array.getElem_mem h2); omega)

/-- Fold over the leftover union mask `rem`, appending each present slot's `symmChild` to `acc`
(lowest first): compact under `m1 ||| m2`, `nil` where the two children cancelled (pruned later
by `compactify`). -/
private def symmKids (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32) (k2 : Array (PTree L))
    (rem : UInt32) (acc : Array (PTree L)) : Array (PTree L) :=
  if hrem : rem == 0 then acc
  else
    symmKids m1 k1 m2 k2 (clearLowest rem) (acc.push (symmChild m1 k1 m2 k2 (lowestSetIdx rem)))
termination_by (sizeOf k1 + sizeOf k2 + 1, rem.toNat)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have : (clearLowest rem).toNat < rem.toNat :=
         toNat_clearLowest_lt rem (by simp_all); omega)
end

/-- Symmetric difference: the entries whose key is in exactly one of `a`, `b`. Shared keys cancel
at the leaves (one `XOR` for the set leaf), equal subtrees cancel to nothing and the surrounding
branch re-compresses; one-sided subtrees are carried over whole (shared, untouched). The result
is canonical (`WF_symmDiff`). -/
@[inline] def symmDiff (a b : PTree L) : PTree L := symmDiffU a b

-- Range restriction — `filterLt`/`filterGE` prune against a key bound structurally: a node whose
-- covered range lies wholly on one side of the bound is kept whole (shared) or dropped in O(1),
-- so only the bins along the bound's routed path are rebuilt (`ltKids`/`geKids`, the
-- `filterKids` twins with a slot-interval action) and re-compressed (`finalize`).
-- `split`/`range` are compositions at the collection layer.

set_option linter.unusedVariables false in
mutual
/-- Keep the keys `< k`: whole subtrees below the bound survive untouched, whole subtrees above
vanish, and the one routed path is rebuilt slot-interval-wise. -/
private def filterLtU (k : Nat) : PTree L → PTree L
  | .nil => .nil
  | .tip pfx leaf =>
    if k >>> 5 < pfx then .nil
    else if pfx < k >>> 5 then .tip pfx leaf
    else
      if LeafOps.isEmpty (LeafOps.filter (fun s _ => decide (s < chunk k 0)) leaf) then .nil
      else .tip pfx (LeafOps.filter (fun s _ => decide (s < chunk k 0)) leaf)
  | .bin pfx level mask kids =>
    if prefixAbove k level < pfx then .nil
    else if pfx < prefixAbove k level then .bin pfx level mask kids
    else
      finalize pfx level mask
        (ltKids k level mask kids mask (Array.emptyWithCapacity (popCount mask)))
termination_by t => (sizeOf t, 1)
decreasing_by
  simp_wf
  omega

/-- The bound-restricted child at present slot `i`: below the bound's slot → kept whole, at it →
recurse, above → dropped (pruned later by `compactify`). -/
private def ltChild (k : Nat) (level : Nat) (mask : UInt32) (kids : Array (PTree L))
    (i : UInt32) : PTree L :=
  if i < chunk k level then
    if h : arrayIndex mask i < kids.size then kids[arrayIndex mask i]'h else .nil
  else if i == chunk k level then
    if h : arrayIndex mask i < kids.size then filterLtU k (kids[arrayIndex mask i]'h) else .nil
  else .nil
termination_by (sizeOf kids, 0)
decreasing_by
  simp_wf
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem h)
  omega

/-- Fold over the mask `rem`, appending each slot's `ltChild` (lowest first). -/
private def ltKids (k : Nat) (level : Nat) (mask : UInt32) (kids : Array (PTree L))
    (rem : UInt32) (acc : Array (PTree L)) : Array (PTree L) :=
  if hrem : rem == 0 then acc
  else
    ltKids k level mask kids (clearLowest rem)
      (acc.push (ltChild k level mask kids (lowestSetIdx rem)))
termination_by (sizeOf kids, rem.toNat)
decreasing_by
  all_goals simp_wf
  all_goals
    have hrem0 : rem ≠ 0 := by simp_all
  · have : rem.toNat ≠ 0 := fun hh => hrem0 (UInt32.toNat_inj.mp (by rw [hh]; rfl))
    omega
  · have := toNat_clearLowest_lt rem hrem0
    omega
end

set_option linter.unusedVariables false in
mutual
/-- Keep the keys `≥ k` (the mirror of `filterLtU`): whole subtrees above the bound survive,
whole subtrees below vanish, the routed path is rebuilt. -/
private def filterGEU (k : Nat) : PTree L → PTree L
  | .nil => .nil
  | .tip pfx leaf =>
    if k >>> 5 < pfx then .tip pfx leaf
    else if pfx < k >>> 5 then .nil
    else
      if LeafOps.isEmpty (LeafOps.filter (fun s _ => decide (chunk k 0 ≤ s)) leaf) then .nil
      else .tip pfx (LeafOps.filter (fun s _ => decide (chunk k 0 ≤ s)) leaf)
  | .bin pfx level mask kids =>
    if prefixAbove k level < pfx then .bin pfx level mask kids
    else if pfx < prefixAbove k level then .nil
    else
      finalize pfx level mask
        (geKids k level mask kids mask (Array.emptyWithCapacity (popCount mask)))
termination_by t => (sizeOf t, 1)
decreasing_by
  simp_wf
  omega

/-- The bound-restricted child at present slot `i`: above the bound's slot → kept whole, at it →
recurse, below → dropped. -/
private def geChild (k : Nat) (level : Nat) (mask : UInt32) (kids : Array (PTree L))
    (i : UInt32) : PTree L :=
  if chunk k level < i then
    if h : arrayIndex mask i < kids.size then kids[arrayIndex mask i]'h else .nil
  else if i == chunk k level then
    if h : arrayIndex mask i < kids.size then filterGEU k (kids[arrayIndex mask i]'h) else .nil
  else .nil
termination_by (sizeOf kids, 0)
decreasing_by
  simp_wf
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem h)
  omega

/-- Fold over the mask `rem`, appending each slot's `geChild` (lowest first). -/
private def geKids (k : Nat) (level : Nat) (mask : UInt32) (kids : Array (PTree L))
    (rem : UInt32) (acc : Array (PTree L)) : Array (PTree L) :=
  if hrem : rem == 0 then acc
  else
    geKids k level mask kids (clearLowest rem)
      (acc.push (geChild k level mask kids (lowestSetIdx rem)))
termination_by (sizeOf kids, rem.toNat)
decreasing_by
  all_goals simp_wf
  all_goals
    have hrem0 : rem ≠ 0 := by simp_all
  · have : rem.toNat ≠ 0 := fun hh => hrem0 (UInt32.toNat_inj.mp (by rw [hh]; rfl))
    omega
  · have := toNat_clearLowest_lt rem hrem0
    omega
end

/-- Keep the keys `< k` — a structural prune: subtrees wholly below the bound are kept whole
(shared), wholly above are dropped in O(1); only the bound's routed path is rebuilt. The result
is canonical (`WF_filterLt`). -/
@[inline] def filterLt (k : Nat) (t : PTree L) : PTree L := filterLtU k t

/-- Keep the keys `≥ k` — the mirror prune of `filterLt`. Canonical (`WF_filterGE`). -/
@[inline] def filterGE (k : Nat) (t : PTree L) : PTree L := filterGEU k t

-- Ordered queries — min/max and successor/predecessor. Children sit in ascending slot order and a
-- leaf's occupancy is a bitmap (`LeafOps.slotsMask`), so the least/greatest key under any node is
-- an O(1)-per-level descent (first/last child, lowest/highest set slot), and `entryGT?`/`entryLT?`
-- are single routed descents with a next-sibling fallback — O(depth), where a hash structure
-- scans all n keys.

set_option linter.unusedVariables false in
/-- The least `(key, value)` pair, `none` on the empty trie. O(depth): the first child of each
`bin` roots the least subtree; at the `tip`, the lowest present slot is the least key. -/
def minEntry? : PTree L → Option (Nat × V)
  | .nil          => none
  | .tip pfx leaf =>
    let s := lowestSetIdx (LeafOps.slotsMask leaf)
    (LeafOps.get? leaf s).map (fun v => ((pfx <<< 5) ||| s.toNat, v))
  | .bin _ _ _ kids =>
    if hb : 0 < kids.size then minEntry? (kids[0]'hb) else none
decreasing_by
  simp_wf
  rename_i hb
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb)
  omega

set_option linter.unusedVariables false in
/-- The greatest `(key, value)` pair, `none` on the empty trie. O(depth): the last child of each
`bin` roots the greatest subtree; at the `tip`, the highest present slot is the greatest key. -/
def maxEntry? : PTree L → Option (Nat × V)
  | .nil          => none
  | .tip pfx leaf =>
    let s := highestSetIdx (LeafOps.slotsMask leaf)
    (LeafOps.get? leaf s).map (fun v => ((pfx <<< 5) ||| s.toNat, v))
  | .bin _ _ _ kids =>
    if hb : kids.size - 1 < kids.size then maxEntry? (kids[kids.size - 1]'hb) else none
decreasing_by
  simp_wf
  rename_i hb
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb)
  omega

/-- The least entry among a `bin`'s children at slots strictly above `c` (`none` when no such slot
is present). The next-sibling fallback of `entryGT?`'s descent. -/
private def minEntryAbove (mask : UInt32) (kids : Array (PTree L)) (c : UInt32) :
    Option (Nat × V) :=
  let m := mask &&& upperMask c
  if m == 0 then none else minEntry? (childAt mask kids (lowestSetIdx m))

/-- The greatest entry among a `bin`'s children at slots strictly below `c` (`none` when no such
slot is present). The previous-sibling fallback of `entryLT?`'s descent. -/
private def maxEntryBelow (mask : UInt32) (kids : Array (PTree L)) (c : UInt32) :
    Option (Nat × V) :=
  let m := mask &&& lowerMask c
  if m == 0 then none else maxEntry? (childAt mask kids (highestSetIdx m))

set_option linter.unusedVariables false in
/-- The least `(key, value)` pair whose key is strictly greater than `k` (the successor query),
`none` if there is none. O(depth): a node whose covered range lies wholly above `k` answers with
its minimum, one wholly below answers `none`, and an aligned `bin` recurses into the routed child
with the next-present-sibling minimum as the fallback (taken lazily through `<|>`, so the walk
touches one path plus at most one sibling descent). -/
def entryGT? (k : Nat) : PTree L → Option (Nat × V)
  | .nil          => none
  | .tip pfx leaf =>
    if k >>> 5 < pfx then minEntry? (.tip pfx leaf)
    else if pfx < k >>> 5 then none
    else
      let m := LeafOps.slotsMask leaf &&& upperMask (chunk k 0)
      if m == 0 then none
      else (LeafOps.get? leaf (lowestSetIdx m)).map
        (fun v => ((pfx <<< 5) ||| (lowestSetIdx m).toNat, v))
  | .bin pfx level mask kids =>
    if prefixAbove k level < pfx then minEntry? (.bin pfx level mask kids)
    else if pfx < prefixAbove k level then none
    else if testBit mask (chunk k level) then
      if hb : arrayIndex mask (chunk k level) < kids.size then
        entryGT? k (kids[arrayIndex mask (chunk k level)]'hb)
          <|> minEntryAbove mask kids (chunk k level)
      else minEntryAbove mask kids (chunk k level)
    else minEntryAbove mask kids (chunk k level)
decreasing_by
  simp_wf
  rename_i hb
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb)
  omega

set_option linter.unusedVariables false in
/-- The greatest `(key, value)` pair whose key is strictly less than `k` (the predecessor query),
`none` if there is none. The mirror of `entryGT?`: ranges wholly below `k` answer with their
maximum, and the fallback takes the greatest entry below the routed slot. -/
def entryLT? (k : Nat) : PTree L → Option (Nat × V)
  | .nil          => none
  | .tip pfx leaf =>
    if pfx < k >>> 5 then maxEntry? (.tip pfx leaf)
    else if k >>> 5 < pfx then none
    else
      let m := LeafOps.slotsMask leaf &&& lowerMask (chunk k 0)
      if m == 0 then none
      else (LeafOps.get? leaf (highestSetIdx m)).map
        (fun v => ((pfx <<< 5) ||| (highestSetIdx m).toNat, v))
  | .bin pfx level mask kids =>
    if pfx < prefixAbove k level then maxEntry? (.bin pfx level mask kids)
    else if prefixAbove k level < pfx then none
    else if testBit mask (chunk k level) then
      if hb : arrayIndex mask (chunk k level) < kids.size then
        entryLT? k (kids[arrayIndex mask (chunk k level)]'hb)
          <|> maxEntryBelow mask kids (chunk k level)
      else maxEntryBelow mask kids (chunk k level)
    else maxEntryBelow mask kids (chunk k level)
decreasing_by
  simp_wf
  rename_i hb
  have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb)
  omega

----------------------------------------------------------------------------------------------------
-- Validation: `PTree`'s set ops must agree with a plain-list reference semantics — an oracle
-- independent of the trie, at the `UInt32`/`Unit` set instance (proofs are added in later stages).
-- The set-specialized helpers fix the trivial `Unit` combine/relation so the checks read like the
-- original set ops; `refCount` counts distinct keys via a `List.contains` fold (the `size` oracle).
----------------------------------------------------------------------------------------------------

private def ofSet (ks : List Nat) : PTree UInt32 := ks.foldl (fun s k => s.insert k ()) .nil
private def unionSet (a b : PTree UInt32) : PTree UInt32 := union (fun _ _ => ()) a b
private def meetSet (a b : PTree UInt32) : PTree UInt32 := meet (fun _ _ => ()) a b
private def subsetSet (a b : PTree UInt32) : Bool := subset (fun _ _ => true) a b
/-- Number of distinct keys in `xs` — the reference `size` oracle (no trie involved). -/
private def refCount (xs : List Nat) : Nat :=
  (xs.foldl (fun acc k => if acc.contains k then acc else k :: acc) []).length

private def seqK : List Nat := List.range 1000
private def sparseK : List Nat :=
  [0, 31, 32, 1023, 1024, 42, 1000000, 999999999, 4294967296, 9223372036854775807, 7]

#guard (ofSet seqK).size == refCount seqK
#guard (ofSet seqK).size == 1000
#guard (ofSet sparseK).size == refCount sparseK
-- membership agrees for present keys
#guard sparseK.all fun k => (ofSet sparseK).contains k == sparseK.contains k
-- …and for absent keys (incl. a near-miss of the 63-bit key)
#guard [1, 33, 1025, 5, 123456, 8, 12345, 9223372036854775806].all fun k =>
  (ofSet sparseK).contains k == sparseK.contains k
-- idempotent re-insert
#guard (((empty : PTree UInt32).insert 42 ()).insert 42 ()).size == 1

private def evenK : List Nat := (List.range 400).map (2 * ·)
private def oddK : List Nat := (List.range 400).map (2 * · + 1)

-- union sizes agree with the reference across dense/overlapping/sparse mixes
#guard (unionSet (ofSet evenK) (ofSet oddK)).size == refCount (evenK ++ oddK)
#guard (unionSet (ofSet sparseK) (ofSet (List.range 50))).size == refCount (sparseK ++ List.range 50)
#guard (unionSet (ofSet sparseK) (ofSet sparseK)).size == (ofSet sparseK).size       -- idempotent
#guard (unionSet (ofSet (List.range 500)) (ofSet ((List.range 500).map (· + 250)))).size == 750
#guard (unionSet (ofSet sparseK) (ofSet evenK)).size == refCount (sparseK ++ evenK)
-- membership after union: every key of either operand is present
#guard (sparseK ++ List.range 50).all fun k =>
  (unionSet (ofSet sparseK) (ofSet (List.range 50))).contains k == true

-- subset agrees with the reference (`a ⊆ b` iff every key of `a` lies in `b`), both directions
private def subsetCorpus : List (List Nat) :=
  [[], [0], List.range 500, seqK, sparseK, evenK, oddK, sparseK ++ List.range 50,
   (List.range 300).map (· + 1)]
/-- Probe keys for the bound/neighbor oracles: chunk seams (0/31/32), in-corpus hits and
near-misses, and the deep sparse extremes. -/
private def probeK : List Nat :=
  [0, 1, 7, 30, 31, 32, 33, 41, 42, 43, 499, 500, 999, 1023, 1024, 1025, 999999, 1000000,
   999999998, 999999999, 4294967295, 4294967296, 9223372036854775806, 9223372036854775807]
#guard subsetCorpus.all fun a => subsetCorpus.all fun b =>
  subsetSet (ofSet a) (ofSet b) == a.all (b.contains ·)
-- explicit anchors: dense reflexive (the prototype's regression cell), proper ⊆, and a near-miss
#guard subsetSet (ofSet seqK) (ofSet seqK)
#guard subsetSet (ofSet (List.range 500)) (ofSet seqK)
#guard !(subsetSet (ofSet seqK) (ofSet (List.range 500)))
#guard !(subsetSet (ofSet sparseK) (ofSet (List.range 50)))

-- disjointness agrees with the reference (no shared key), across the whole corpus product
#guard subsetCorpus.all fun a => subsetCorpus.all fun b =>
  isDisjoint (ofSet a) (ofSet b) == !(a.any (b.contains ·))
#guard isDisjoint (ofSet evenK) (ofSet oddK)            -- interleaved: every leaf pair compared
#guard !(isDisjoint (ofSet [1, 5000]) (ofSet [5000]))   -- deep shared key
#guard isDisjoint (ofSet []) (ofSet seqK)
#guard isDisjoint (ofSet seqK) (ofSet [])

-- difference agrees with the reference (keys of `a` absent from `b`) and re-canonicalizes
-- (structural `beq` against a direct build of the survivors)
#guard subsetCorpus.all fun a => subsetCorpus.all fun b =>
  beq (diff (ofSet a) (ofSet b)) (ofSet (a.filter (fun k => !(b.contains k))))
#guard beq (diff (ofSet sparseK) (ofSet [])) (ofSet sparseK)        -- empty subtrahend: identity
#guard (diff (ofSet seqK) (ofSet seqK)).size == 0                   -- self-difference: nil
#guard beq (diff (ofSet [0, 32, 64]) (ofSet [32])) (ofSet [0, 64])
#guard beq (diff (ofSet [7, 5000]) (ofSet [5000])) (ofSet [7])      -- lone survivor lifts
#guard beq (diff (ofSet sparseK) (ofSet seqK))                       -- deep keys survive a dense cut
  (ofSet (sparseK.filter (· ≥ 1000)))

-- symmetric difference agrees with the reference (keys in exactly one operand), re-canonicalizes,
-- and matches its (a \ b) ∪ (b \ a) decomposition
#guard subsetCorpus.all fun a => subsetCorpus.all fun b =>
  beq (symmDiff (ofSet a) (ofSet b))
    (ofSet (a.filter (fun k => !(b.contains k)) ++ b.filter (fun k => !(a.contains k))))
#guard subsetCorpus.all fun a => subsetCorpus.all fun b =>
  beq (symmDiff (ofSet a) (ofSet b))
    (unionSet (diff (ofSet a) (ofSet b)) (diff (ofSet b) (ofSet a)))
#guard (symmDiff (ofSet seqK) (ofSet seqK)).size == 0                -- total cancellation → nil
#guard beq (symmDiff (ofSet sparseK) (ofSet [])) (ofSet sparseK)     -- right identity
#guard beq (symmDiff (ofSet []) (ofSet sparseK)) (ofSet sparseK)     -- left identity
#guard beq (symmDiff (ofSet [1, 5000]) (ofSet [5000])) (ofSet [1])   -- deep cancel, height collapses
#guard beq (symmDiff (symmDiff (ofSet sparseK) (ofSet evenK)) (ofSet evenK)) (ofSet sparseK)
  -- involution: (a △ b) △ b = a

-- range restriction agrees with the list oracle and re-canonicalizes, across corpus × probes
#guard subsetCorpus.all fun ks => probeK.all fun k =>
  beq (filterLt k (ofSet ks)) (ofSet (ks.filter (· < k)))
#guard subsetCorpus.all fun ks => probeK.all fun k =>
  beq (filterGE k (ofSet ks)) (ofSet (ks.filter (k ≤ ·)))
#guard beq (filterLt 33 (ofSet [0, 32, 64])) (ofSet [0, 32])      -- prune at a bin boundary
#guard beq (filterGE 33 (ofSet [0, 32, 64])) (ofSet [64])         -- lone survivor lifts
#guard beq (filterLt 32 (ofSet [0, 31, 32])) (ofSet [0, 31])      -- chunk-31 seam
#guard (filterGE 9223372036854775808 (ofSet sparseK)).size == 0   -- bound above everything

-- intersection sizes agree with the reference (distinct keys of `a` that also lie in `b`)
#guard subsetCorpus.all fun a => subsetCorpus.all fun b =>
  (meetSet (ofSet a) (ofSet b)).size == refCount (a.filter (b.contains ·))
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

-- `toArray` enumerates keys in ascending order regardless of insertion order or key spread
private def strictlyAscending (xs : List Nat) : Bool := (xs.zip (xs.drop 1)).all (fun p => p.1 < p.2)
#guard (ofSet [3, 1, 2]).toArray.toList.map Prod.fst == [1, 2, 3]
#guard (ofSet [5, 1000, 0, 32]).toArray.toList.map Prod.fst == [0, 5, 32, 1000]   -- across leaves
#guard (ofSet sparseK).toArray.size == refCount sparseK                            -- count matches
#guard strictlyAscending ((ofSet sparseK).toArray.toList.map Prod.fst)            -- sparse, ascending
#guard strictlyAscending ((ofSet seqK).toArray.toList.map Prod.fst)              -- dense, ascending

-- structural `beq` matches set equality on canonical tries (same set built two ways compares equal)
#guard beq (ofSet [1, 2, 3]) (ofSet [3, 2, 1, 2])
#guard !beq (ofSet [1, 2]) (ofSet [1, 2, 3])
#guard beq (ofSet sparseK) (ofSet sparseK.reverse)                                -- order-independent

-- filter agrees with the list-filter oracle and re-canonicalizes (`beq` against a direct build)
private def filterSet (p : Nat → Bool) (a : PTree UInt32) : PTree UInt32 :=
  filter (fun k _ => p k) a
#guard beq (filterSet (· % 2 == 0) (ofSet seqK)) (ofSet (seqK.filter (· % 2 == 0)))
#guard beq (filterSet (· < 50) (ofSet sparseK)) (ofSet (sparseK.filter (· < 50)))
#guard beq (filterSet (fun _ => true) (ofSet sparseK)) (ofSet sparseK)            -- keep all: identity
#guard (filterSet (fun _ => false) (ofSet sparseK)).size == 0                     -- drop all → nil
#guard beq (filterSet (· == 0) (ofSet [0, 32, 64])) (ofSet [0])                  -- collapse to one tip
-- erase removes exactly the key; absent keys are no-ops; the touched branch re-compresses
private def eraseSet (a : PTree UInt32) (k : Nat) : PTree UInt32 := erase k a
#guard sparseK.all fun k => (eraseSet (ofSet sparseK) 42).contains k == (k != 42)
#guard (eraseSet (ofSet sparseK) 42).size == refCount sparseK - 1
#guard beq (eraseSet (ofSet sparseK) 5) (ofSet sparseK)                           -- absent: no-op
#guard beq (eraseSet (ofSet [7, 5000]) 5000) (ofSet [7])                          -- hoist lone survivor
#guard beq (eraseSet (ofSet [7]) 7) .nil                                          -- last key → nil
#guard beq (sparseK.foldl eraseSet (ofSet sparseK)) .nil                          -- erase everything
#guard beq (eraseSet (ofSet sparseK) 9223372036854775807)                         -- deep sparse key
  (ofSet (sparseK.filter (· != 9223372036854775807)))

-- ordered queries agree with the ascending-list oracle: min/max = head/last of `toArray`,
-- successor/predecessor = first-above/last-below in the sorted key list
private def keysOf (a : PTree UInt32) : List Nat := a.toArray.toList.map Prod.fst
#guard subsetCorpus.all fun ks =>
  let t := ofSet ks
  t.minEntry?.map Prod.fst == (keysOf t).head?
#guard subsetCorpus.all fun ks =>
  let t := ofSet ks
  t.maxEntry?.map Prod.fst == (keysOf t).getLast?
#guard subsetCorpus.all fun ks =>
  let t := ofSet ks
  probeK.all fun k => (entryGT? k t).map Prod.fst == (keysOf t).find? (fun j => k < j)
#guard subsetCorpus.all fun ks =>
  let t := ofSet ks
  probeK.all fun k => (entryLT? k t).map Prod.fst == ((keysOf t).filter (· < k)).getLast?
-- slot-31 anchors (`upperMask 31 = 0`/`lowerMask 0 = 0`: no in-leaf neighbor; the next leaf answers)
#guard (entryGT? 31 (ofSet [31])).isNone
#guard (entryGT? 31 (ofSet [31, 32])).map Prod.fst == some 32
#guard (entryLT? 32 (ofSet [31, 32])).map Prod.fst == some 31
#guard (entryLT? 0 (ofSet [0, 1])).isNone

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
private theorem contains_bin (k pfx level : Nat) (mask : UInt32) (kids : Array (PTree L)) :
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
private theorem get?_bin (k pfx level : Nat) (mask : UInt32) (kids : Array (PTree L)) :
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
private def AlignedAt (l : Nat) (c : UInt32) (p : Nat) (t : PTree L) : Prop :=
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
private theorem WF_singleton (k : Nat) (v : V) : WF (singleton k v : PTree L) := by
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
private theorem contains_singleton (k j : Nat) (v : V) : contains k (singleton j v : PTree L) = true ↔ k = j := by
  rw [singleton, contains_tip,
      leaf_contains_singleton (chunk j 0) (chunk k 0) v (chunk_lt _ _) (chunk_lt _ _),
      Bool.and_eq_true, beq_iff_eq, beq_iff_eq, key_eq_iff k j]

/-! ### Non-emptiness

The canonical invariant `WF` forbids `nil` children (a `nil` child at a present slot would carry no
keys, so it could be dropped without changing membership — exactly what would break `ext`). These
structural facts let the merge/insert proofs discharge that clause: the operations never produce a
`nil`. -/

/-- A singleton is a `tip`, never empty. -/
private theorem singleton_ne_nil (k : Nat) (v : V) : (singleton k v : PTree L) ≠ .nil := by
  simp [singleton]

/-- `insert` always yields a `tip` or a `bin`, never `nil`. -/
theorem insert_ne_nil (k : Nat) (v : V) (t : PTree L) : insert k v t ≠ .nil := by
  cases t <;> simp only [insert] <;> (repeat' split) <;> simp [join, singleton]

/-- Union with a non-empty operand is non-empty: every non-`nil` shape feeds a `tip`/`bin`/`join`
result. -/
private theorem unionU_ne_nil_of_left (c : V → V → V) (a b : PTree L) (h : a ≠ .nil) :
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
  rcases UInt32.lt_or_lt_of_ne hne with hlt | hgt
  · rw [if_pos hlt, arrayIndex_setBit_of_le (setBit 0 ca) cb ca hcb hca (UInt32.le_of_lt hlt),
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
  rcases UInt32.lt_or_lt_of_ne hne with hlt | hgt
  · rw [if_pos hlt, arrayIndex_setBit_self,
        arrayIndex_setBit_of_gt 0 ca cb hca hcb hlt (testBit_zero ca), arrayIndex_zero]
    rfl
  · rw [if_neg (uint32_not_lt_of_gt hgt), arrayIndex_setBit_self,
        arrayIndex_setBit_of_le 0 ca cb hca hcb (UInt32.le_of_lt hgt), arrayIndex_zero]
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
private theorem contains_join (j p l : Nat) (ca cb : UInt32) (a b : PTree L)
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
private theorem WF_join (p l : Nat) (ca cb : UInt32) (a b : PTree L)
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
  exact UInt32.lt_iff_toNat_lt.mp (LeafOps.someSlot_lt leaf hb)

/-- A `bin`'s representative key carries the branch prefix `pfx` above `level`. -/
private theorem someKey_bin_prefixAbove (pfx level : Nat) (mask : UInt32) (kids : Array (PTree L))
    (hm : mask ≠ 0) : prefixAbove (someKey (.bin pfx level mask kids)) level = pfx := by
  show ((pfx <<< (5 * (level + 1))) ||| ((lowestSetIdx mask).toNat <<< (5 * level)))
        >>> (5 * (level + 1)) = pfx
  apply shiftLeft_lor_shiftRight
  have hlsi : (lowestSetIdx mask).toNat < 32 := UInt32.lt_iff_toNat_lt.mp (lowestSetIdx_lt mask hm)
  rw [Nat.shiftLeft_eq, show 5 * (level + 1) = 5 * level + 5 from by omega, Nat.pow_add]
  calc (lowestSetIdx mask).toNat * 2 ^ (5 * level)
      < 32 * 2 ^ (5 * level) :=
        Nat.mul_lt_mul_of_pos_right hlsi (Nat.pow_pos (by decide))
    _ = 2 ^ (5 * level) * 2 ^ 5 := by rw [Nat.mul_comm]

/-- A non-empty `tip` is aligned at every level `≥ 1`: all its keys agree with the representative
above the bottom chunk. -/
private theorem aligned_tip (pfx : Nat) (leaf : L) (hb : LeafOps.isEmpty leaf = false) (l : Nat) (hl : 0 < l) :
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
private theorem aligned_bin (pfx level : Nat) (mask : UInt32) (kids : Array (PTree L))
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
private theorem prefixAbove_branchLevel_eq (ka kb : Nat) :
    prefixAbove ka (branchLevel ka kb) = prefixAbove kb (branchLevel ka kb) := by
  unfold prefixAbove branchLevel
  apply shiftRight_eq_of_xor_lt
  rw [← pow32_eq]
  exact lt_pow_of_requiredHeight_le (Nat.le_refl _)

/-- A high-bit divergence forces a positive branch level (the tip join always branches at `≥ 1`). -/
private theorem branchLevel_pos (k kb : Nat) (h : k >>> 5 ≠ kb >>> 5) : 0 < branchLevel k kb := by
  rcases Nat.eq_zero_or_pos (branchLevel k kb) with hz | hp
  · refine absurd ?_ h
    apply shiftRight_eq_of_xor_lt (m := 5)
    unfold branchLevel at hz
    have hlt := lt_pow_of_requiredHeight_le (h := 0) (Nat.le_of_eq hz)
    rw [pow32_eq] at hlt
    simpa using hlt
  · exact hp

/-- Divergence above a bin's level forces the branch level past it (the bin join branches deeper). -/
private theorem lt_branchLevel (k kb level : Nat)
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
private theorem chunk_branchLevel_ne (ka kb : Nat) (h : ka ≠ kb) :
    chunk ka (branchLevel ka kb) ≠ chunk kb (branchLevel ka kb) := fun heq =>
  chunk_branchLevel_xor_ne_zero ka kb h (chunk_xor_eq_zero_of_chunk_eq heq)

/-- Membership in a singleton, as a `Bool` (the `decide`-free form the extensionality proofs use). -/
private theorem contains_singleton_eq (j k : Nat) (v : V) : contains j (singleton k v : PTree L) = (j == k) := by
  rw [Bool.eq_iff_iff, contains_singleton, beq_iff_eq]

/-- Membership in a `join` of two slot-aligned subtrees, stated directly on `join` (unfolds the
branch arithmetic once so the call sites need only supply the alignments). -/
private theorem contains_join_eq (j ka kb : Nat) (a b : PTree L) (hne : ka ≠ kb)
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
  rcases UInt32.lt_or_lt_of_ne hne with hlt | hgt
  · rw [arrayIndex_setBit_of_le mask c cj hc hcj (UInt32.le_of_lt hlt),
        Array.getElem?_insertIdx_of_lt hle (arrayIndex_lt_of_lt mask cj c hcj hc htcj hlt)]
  · rw [arrayIndex_setBit_of_gt mask c cj hc hcj hgt htc, Array.getElem?_insertIdx hle,
        if_neg (by have := arrayIndex_le_of_le mask c cj hc hcj (UInt32.le_of_lt hgt); omega),
        if_neg (by have := arrayIndex_le_of_le mask c cj hc hcj (UInt32.le_of_lt hgt); omega),
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
        rw [← hrem]; exact toNat_clearLowest_lt rem hrem0
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
private theorem childAt_mergeKids (cf : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) (c : UInt32) (hc : c < 32) (htb : testBit (m1 ||| m2) c = true) :
    childAt (m1 ||| m2) (mergeKids cf m1 k1 m2 k2 (m1 ||| m2) #[]) c = mergeChild cf m1 k1 m2 k2 c := by
  obtain ⟨_, _, hthird⟩ := mergeKids_spec cf m1 k1 m2 k2 (m1 ||| m2).toNat (m1 ||| m2) rfl #[]
  have hc' := hthird c hc htb
  unfold childAt
  rw [show (#[] : Array (PTree L)).size = 0 from rfl, Nat.zero_add] at hc'
  rw [hc', Option.getD_some]

/-- The rebuilt child array has exactly one slot per present bit of the merged mask — the compact
size invariant the merged `bin` needs to stay well-formed. -/
private theorem size_mergeKids (cf : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
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
        rw [← hrem]; exact toNat_clearLowest_lt rem hrem0
      rcases IH (clearLowest rem).toNat hlt (clearLowest rem) rfl
          (acc.push (mergeChild cf m1 k1 m2 k2 (lowestSetIdx rem))) x hx with hacc | hex
      · rcases Array.mem_push.mp hacc with hin | heq
        · exact Or.inl hin
        · exact Or.inr ⟨lowestSetIdx rem, testBit_lowestSetIdx rem hrem0, heq⟩
      · obtain ⟨c, htb, hxc⟩ := hex
        exact Or.inr ⟨c, testBit_of_clearLowest rem c htb, hxc⟩

/-- A `bin`'s children, well-formed, non-`nil`, and compactly stored — the part of `WF` the per-slot
union reasoning (`mergeChild`/`mergeKids`) consumes, abstracted so the motives can carry it. -/
private def KidsWF (mask : UInt32) (kids : Array (PTree L)) : Prop :=
  kids.size = popCount mask ∧ (∀ c ∈ kids, WF c) ∧ (∀ c ∈ kids, c ≠ .nil)

/-- A key routing to a slot other than the one a subtree is aligned under is not in that subtree. -/
private theorem contains_false_of_aligned {j : Nat} (l : Nat) (c : UInt32) (p : Nat) (t : PTree L)
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
private theorem contains_unionU (cf : V → V → V) (j : Nat) : ∀ (a b : PTree L), WF a → WF b →
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
    rw [unionU, if_pos heq, Array.emptyWithCapacity_eq, contains_bin, contains_bin, contains_bin]
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
private theorem contains_mergeChild (cf : V → V → V) (j : Nat) (m1 : UInt32) (k1 : Array (PTree L))
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
private theorem mergeChild_ne_nil (cf : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
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
private theorem WF_unionU (cf : V → V → V) : ∀ (a b : PTree L), WF a → WF b → WF (unionU cf a b) := by
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
    rw [unionU, if_pos heq, Array.emptyWithCapacity_eq, WF]
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
        rw [← hrem]; exact toNat_clearLowest_lt rem hrem0
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
            exact UInt32.lt_of_le_of_ne (lowestSetIdx_le_of_testBit rem c' hc' hc'rem)
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
                  (UInt32.le_of_lt (hbelow c hc haccc)),
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
private theorem contains_finalize (j : Nat) (p l : Nat) (mask : UInt32) (kids : Array (PTree L))
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
        rw [← hrem]; exact toNat_clearLowest_lt rem hrem0
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
private theorem WF_finalize (p l : Nat) (mask : UInt32) (kids : Array (PTree L)) (hl : 0 < l)
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
        rw [← hrem]; exact toNat_clearLowest_lt rem hrem0
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
private theorem childAt_meetKids (cf : V → V → V) (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) (c : UInt32) (hc : c < 32) (htb : testBit (m1 &&& m2) c = true) :
    childAt (m1 &&& m2) (meetKids cf m1 k1 m2 k2 (m1 &&& m2) #[]) c = meetChild cf m1 k1 m2 k2 c := by
  obtain ⟨_, _, hthird⟩ := meetKids_spec cf m1 k1 m2 k2 (m1 &&& m2).toNat (m1 &&& m2) rfl #[]
  have hc' := hthird c hc htb
  unfold childAt
  rw [show (#[] : Array (PTree L)).size = 0 from rfl, Nat.zero_add] at hc'
  rw [hc', Option.getD_some]

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
private theorem meet_WF_contains (cf : V → V → V) : ∀ (a b : PTree L), WF a → WF b →
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
      rw [meetU, if_pos heq, if_pos hpfx, Array.emptyWithCapacity_eq]
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
    have hlo : (LeafOps.someSlot leaf).toNat < 32 := UInt32.lt_iff_toNat_lt.mp (LeafOps.someSlot_lt leaf hb)
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

/-! ### Filter & erase

Both rebuild a touched branch through `finalize`, so `WF` follows from `WF_finalize` once the
rebuilt children are known well-formed and aligned. Alignment transfers because filtering/erasing
only ever *removes* keys — but the leaf interface has no removal law, so the inductions carry a
weaker fact instead: every surviving key shares its high bits (`>>> 5`) with some original key.
At a branch level (always `≥ 1`) the routing data (`chunk`, `prefixAbove`) reads only those high
bits, so that is exactly enough to transfer `AlignedAt`. -/

/-- Routing above the bottom level reads only a key's high bits: equal `>>> 5` ⇒ equal prefix. -/
private theorem prefixAbove_eq_of_hi {j j' : Nat} (l : Nat) (h : j >>> 5 = j' >>> 5) :
    prefixAbove j l = prefixAbove j' l := by
  unfold prefixAbove
  rw [show 5 * (l + 1) = 5 + 5 * l from by omega, Nat.shiftRight_add, Nat.shiftRight_add, h]

/-- Routing above the bottom level reads only a key's high bits: equal `>>> 5` ⇒ equal chunk at
any branch level (`≥ 1`). -/
private theorem chunk_eq_of_hi {j j' : Nat} (l : Nat) (hl : 0 < l) (h : j >>> 5 = j' >>> 5) :
    chunk j l = chunk j' l := by
  unfold chunk
  rw [show 5 * l = 5 + 5 * (l - 1) from by omega, Nat.shiftRight_add, Nat.shiftRight_add, h]

/-- A `tip`'s keys all carry its prefix as their high bits. -/
private theorem hi_eq_of_contains_tip {j pfx : Nat} {leaf : L}
    (h : contains j (.tip pfx leaf) = true) : j >>> 5 = pfx := by
  rw [contains_tip] at h
  exact beq_iff_eq.mp (and_split h).1

/-- `filterKids`' fold invariant — the verbatim `meetKids_spec` shape for a single operand. -/
private theorem filterKids_spec (p : Nat → V → Bool) (mask : UInt32) (kids : Array (PTree L)) :
    ∀ (n : Nat) (rem : UInt32), rem.toNat = n → ∀ (acc : Array (PTree L)),
      (filterKids p mask kids rem acc).size = acc.size + popCount rem
      ∧ (∀ i, i < acc.size → (filterKids p mask kids rem acc)[i]? = acc[i]?)
      ∧ (∀ c, c < 32 → testBit rem c = true →
           (filterKids p mask kids rem acc)[acc.size + arrayIndex rem c]?
             = some (filterChild p mask kids c)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro rem hrem acc
    by_cases h0 : (rem == 0) = true
    · have hr0 : rem = 0 := by simpa using h0
      rw [filterKids, dif_pos h0]
      refine ⟨?_, ?_, ?_⟩
      · rw [hr0, show popCount (0 : UInt32) = 0 from rfl, Nat.add_zero]
      · intro i hi; rfl
      · intro c hc htb; rw [hr0, testBit_zero] at htb; exact absurd htb (by decide)
    · have hrem0 : rem ≠ 0 := by intro h; exact h0 (by rw [h]; rfl)
      have hstep : filterKids p mask kids rem acc
          = filterKids p mask kids (clearLowest rem)
              (acc.push (filterChild p mask kids (lowestSetIdx rem))) := by
        rw [filterKids, dif_neg h0]
      have hlt : (clearLowest rem).toNat < n := by
        rw [← hrem]; exact toNat_clearLowest_lt rem hrem0
      obtain ⟨ihsize, ihpref, ihthird⟩ :=
        IH (clearLowest rem).toNat hlt (clearLowest rem) rfl
          (acc.push (filterChild p mask kids (lowestSetIdx rem)))
      have hpc : popCount (clearLowest rem) + 1 = popCount rem := popCount_clearLowest rem hrem0
      have haccsz : (acc.push (filterChild p mask kids (lowestSetIdx rem))).size = acc.size + 1 :=
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

/-- Reading a present slot of the rebuilt child array recovers that slot's `filterChild`. -/
private theorem childAt_filterKids (p : Nat → V → Bool) (mask : UInt32) (kids : Array (PTree L))
    (c : UInt32) (hc : c < 32) (htb : testBit mask c = true) :
    childAt mask (filterKids p mask kids mask #[]) c = filterChild p mask kids c := by
  obtain ⟨_, _, hthird⟩ := filterKids_spec p mask kids mask.toNat mask rfl #[]
  have hc' := hthird c hc htb
  unfold childAt
  rw [show (#[] : Array (PTree L)).size = 0 from rfl, Nat.zero_add] at hc'
  rw [hc', Option.getD_some]

/-- `filterChild` is `filterU` of the routed child (`nil` reads stay `nil`). -/
private theorem filterChild_eq (p : Nat → V → Bool) (mask : UInt32) (kids : Array (PTree L))
    (c : UInt32) : filterChild p mask kids c = filterU p (childAt mask kids c) := by
  rw [filterChild]
  unfold childAt
  by_cases h : arrayIndex mask c < kids.size
  · rw [dif_pos h, Array.getElem?_eq_getElem h, Option.getD_some]
  · rw [dif_neg h, Array.getElem?_eq_none (Nat.le_of_not_lt h), Option.getD_none, filterU]

/-- `filterU` preserves `WF`, and every surviving key shares its high bits with an original key
(see the section note: that is the `AlignedAt`-transfer `WF_finalize` needs). One combined
member-recursion, the single-operand `meet_WF_contains`. -/
private theorem filter_WF_keys (p : Nat → V → Bool) : (t : PTree L) → WF t →
    WF (filterU p t)
      ∧ ∀ j, contains j (filterU p t) = true → ∃ j', contains j' t = true ∧ j >>> 5 = j' >>> 5
  | .nil => fun _ => by
      rw [filterU]
      exact ⟨by rw [WF]; trivial,
             fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
  | .tip pfx leaf => fun hwf => by
      rw [filterU]
      by_cases he : LeafOps.isEmpty
          (LeafOps.filter (fun s v => p ((pfx <<< 5) ||| s.toNat) v) leaf) = true
      · rw [if_pos he]
        exact ⟨by rw [WF]; trivial,
               fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
      · rw [if_neg he]
        refine ⟨by rw [WF]; simpa using he, ?_⟩
        intro j hj
        obtain ⟨j', hj'⟩ := exists_mem (.tip pfx leaf) hwf (by simp)
        exact ⟨j', hj', (hi_eq_of_contains_tip hj).trans (hi_eq_of_contains_tip hj').symm⟩
  | .bin pfx level mask kids => fun hwf => by
      rw [filterU, Array.emptyWithCapacity_eq]
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, _, hwfk, _, hal⟩ := hwf'
      have hslot : ∀ c, c < 32 → testBit mask c = true →
          WF (filterU p (childAt mask kids c))
          ∧ ∀ j, contains j (filterU p (childAt mask kids c)) = true →
              ∃ j', contains j' (childAt mask kids c) = true ∧ j >>> 5 = j' >>> 5 := by
        intro c hc htc
        have hbc : arrayIndex mask c < kids.size := by
          rw [hsz]; exact arrayIndex_lt mask c htc
        have hcA : childAt mask kids c = kids[arrayIndex mask c]'hbc := by
          unfold childAt; rw [Array.getElem?_eq_getElem hbc, Option.getD_some]
        rw [hcA]
        exact filter_WF_keys p (kids[arrayIndex mask c]'hbc) (hwfk _ (Array.getElem_mem hbc))
      have hchA : ∀ c, c < 32 → testBit mask c = true →
          childAt mask (filterKids p mask kids mask #[]) c = filterU p (childAt mask kids c) := by
        intro c hc htc
        rw [childAt_filterKids p mask kids c hc htc, filterChild_eq]
      have hal' : ∀ c, c < 32 → testBit mask c = true →
          AlignedAt level c pfx (childAt mask (filterKids p mask kids mask #[]) c) := by
        intro c hc htc
        rw [hchA c hc htc]
        intro j hj
        obtain ⟨j', hj', h5⟩ := (hslot c hc htc).2 j hj
        obtain ⟨hch, hpf⟩ := hal c hc htc j' hj'
        exact ⟨(chunk_eq_of_hi level hl h5).trans hch, (prefixAbove_eq_of_hi level h5).trans hpf⟩
      refine ⟨WF_finalize pfx level mask _ hl ?_ hal', ?_⟩
      · intro c hc htc
        rw [hchA c hc htc]
        exact (hslot c hc htc).1
      · intro j hj
        rw [contains_finalize j pfx level mask _ hal'] at hj
        obtain ⟨htj, hcj⟩ := and_split hj
        rw [hchA (chunk j level) (chunk_lt j level) htj] at hcj
        obtain ⟨j', hj', h5⟩ := (hslot (chunk j level) (chunk_lt j level) htj).2 j hcj
        refine ⟨j', ?_, h5⟩
        rw [contains_bin]
        obtain ⟨hch, _⟩ := hal (chunk j level) (chunk_lt j level) htj j' hj'
        rw [hch, htj, Bool.true_and]
        exact hj'
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hbc); omega

/-- `eraseU` preserves `WF`, and every surviving key shares its high bits with an original key —
the erase mirror of `filter_WF_keys`, member-recursion down the one routed path. -/
private theorem erase_WF_keys (k : Nat) : (t : PTree L) → WF t →
    WF (eraseU k t)
      ∧ ∀ j, contains j (eraseU k t) = true → ∃ j', contains j' t = true ∧ j >>> 5 = j' >>> 5
  | .nil => fun _ => by
      rw [eraseU]
      exact ⟨by rw [WF]; trivial,
             fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
  | .tip pfx leaf => fun hwf => by
      rw [eraseU]
      by_cases hp : (k >>> 5 == pfx) = true
      · rw [if_pos hp]
        by_cases he : LeafOps.isEmpty (LeafOps.erase leaf (chunk k 0)) = true
        · rw [if_pos he]
          exact ⟨by rw [WF]; trivial,
                 fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
        · rw [if_neg he]
          refine ⟨by rw [WF]; simpa using he, ?_⟩
          intro j hj
          obtain ⟨j', hj'⟩ := exists_mem (.tip pfx leaf) hwf (by simp)
          exact ⟨j', hj', (hi_eq_of_contains_tip hj).trans (hi_eq_of_contains_tip hj').symm⟩
      · rw [if_neg hp]
        exact ⟨hwf, fun j hj => ⟨j, hj, rfl⟩⟩
  | .bin pfx level mask kids => fun hwf => by
      rw [eraseU]
      by_cases hroute : ((prefixAbove k level == pfx) && testBit mask (chunk k level)) = true
      · rw [if_pos hroute]
        by_cases hb : arrayIndex mask (chunk k level) < kids.size
        · rw [dif_pos hb]
          have hwf' := hwf
          rw [WF] at hwf'
          obtain ⟨hl, hsz, _, hwfk, _, hal⟩ := hwf'
          obtain ⟨_, htb⟩ := and_split hroute
          obtain ⟨ihwf, ihkeys⟩ :=
            erase_WF_keys k (kids[arrayIndex mask (chunk k level)]'hb)
              (hwfk _ (Array.getElem_mem hb))
          have hcA : childAt mask kids (chunk k level)
              = kids[arrayIndex mask (chunk k level)]'hb := by
            unfold childAt; rw [Array.getElem?_eq_getElem hb, Option.getD_some]
          have hset : ∀ c, c < 32 → testBit mask c = true →
              childAt mask (kids.set (arrayIndex mask (chunk k level))
                  (eraseU k (kids[arrayIndex mask (chunk k level)]'hb)) hb) c
                = if c = chunk k level
                    then eraseU k (kids[arrayIndex mask (chunk k level)]'hb)
                    else childAt mask kids c := by
            intro c hc htc
            unfold childAt
            rw [Array.getElem?_set hb]
            by_cases hcc : c = chunk k level
            · subst hcc
              rw [if_pos rfl, if_pos rfl, Option.getD_some]
            · rw [if_neg hcc,
                  if_neg (arrayIndex_inj mask (chunk k level) c (chunk_lt k level) hc htb htc
                    (fun hh => hcc hh.symm))]
          have hal' : ∀ c, c < 32 → testBit mask c = true →
              AlignedAt level c pfx (childAt mask (kids.set (arrayIndex mask (chunk k level))
                  (eraseU k (kids[arrayIndex mask (chunk k level)]'hb)) hb) c) := by
            intro c hc htc
            rw [hset c hc htc]
            by_cases hcc : c = chunk k level
            · rw [if_pos hcc]
              intro j hj
              obtain ⟨j', hj', h5⟩ := ihkeys j hj
              have hj'A : contains j' (childAt mask kids c) = true := by
                rw [hcc, hcA]; exact hj'
              obtain ⟨hch, hpf⟩ := hal c hc htc j' hj'A
              exact ⟨(chunk_eq_of_hi level hl h5).trans hch,
                     (prefixAbove_eq_of_hi level h5).trans hpf⟩
            · rw [if_neg hcc]
              exact hal c hc htc
          refine ⟨WF_finalize pfx level mask _ hl ?_ hal', ?_⟩
          · intro c hc htc
            rw [hset c hc htc]
            by_cases hcc : c = chunk k level
            · rw [if_pos hcc]; exact ihwf
            · rw [if_neg hcc]
              have hbc : arrayIndex mask c < kids.size := by
                rw [hsz]; exact arrayIndex_lt mask c htc
              have hcA' : childAt mask kids c = kids[arrayIndex mask c]'hbc := by
                unfold childAt; rw [Array.getElem?_eq_getElem hbc, Option.getD_some]
              rw [hcA']
              exact hwfk _ (Array.getElem_mem hbc)
          · intro j hj
            rw [contains_finalize j pfx level mask _ hal'] at hj
            obtain ⟨htj, hcj⟩ := and_split hj
            rw [hset (chunk j level) (chunk_lt j level) htj] at hcj
            by_cases hcc : chunk j level = chunk k level
            · rw [if_pos hcc] at hcj
              obtain ⟨j', hj', h5⟩ := ihkeys j hcj
              refine ⟨j', ?_, h5⟩
              rw [contains_bin]
              have hj'A : contains j' (childAt mask kids (chunk k level)) = true := by
                rw [hcA]; exact hj'
              obtain ⟨hch, _⟩ := hal (chunk k level) (chunk_lt k level) htb j' hj'A
              rw [hch, htb, Bool.true_and, hcA]
              exact hj'
            · rw [if_neg hcc] at hcj
              refine ⟨j, ?_, rfl⟩
              rw [contains_bin, htj, Bool.true_and]
              exact hcj
        · rw [dif_neg hb]
          exact ⟨hwf, fun j hj => ⟨j, hj, rfl⟩⟩
      · rw [if_neg hroute]
        exact ⟨hwf, fun j hj => ⟨j, hj, rfl⟩⟩
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- `filter` preserves canonical shape. -/
theorem WF_filter (p : Nat → V → Bool) (t : PTree L) (hwf : WF t) : WF (filter p t) :=
  (filter_WF_keys p t hwf).1

/-- `erase` preserves canonical shape. -/
theorem WF_erase (k : Nat) (t : PTree L) (hwf : WF t) : WF (erase k t) :=
  (erase_WF_keys k t hwf).1

/-! ### Difference

`diffU` only removes keys from the left operand, so its `WF` proof carries the same one-sided
high-bits provenance as filter/erase (every surviving key shares its `>>> 5` with an original
left key) — no leaf removal law needed. The aligned-`bin` case mirrors `filter_WF_keys` (a full
`diffKids` rebuild under `m1`), the routed cases mirror `erase_WF_keys`' splice, factored below
into `splice_WF_keys` so the symmetric difference can reuse it. -/

/-- `diffKids`' fold invariant — the verbatim `filterKids_spec` shape for two operands. -/
private theorem diffKids_spec (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) :
    ∀ (n : Nat) (rem : UInt32), rem.toNat = n → ∀ (acc : Array (PTree L)),
      (diffKids m1 k1 m2 k2 rem acc).size = acc.size + popCount rem
      ∧ (∀ i, i < acc.size → (diffKids m1 k1 m2 k2 rem acc)[i]? = acc[i]?)
      ∧ (∀ c, c < 32 → testBit rem c = true →
           (diffKids m1 k1 m2 k2 rem acc)[acc.size + arrayIndex rem c]?
             = some (diffChild m1 k1 m2 k2 c)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro rem hrem acc
    by_cases h0 : (rem == 0) = true
    · have hr0 : rem = 0 := by simpa using h0
      rw [diffKids, dif_pos h0]
      refine ⟨?_, ?_, ?_⟩
      · rw [hr0, show popCount (0 : UInt32) = 0 from rfl, Nat.add_zero]
      · intro i hi; rfl
      · intro c hc htb; rw [hr0, testBit_zero] at htb; exact absurd htb (by decide)
    · have hrem0 : rem ≠ 0 := by intro h; exact h0 (by rw [h]; rfl)
      have hstep : diffKids m1 k1 m2 k2 rem acc
          = diffKids m1 k1 m2 k2 (clearLowest rem)
              (acc.push (diffChild m1 k1 m2 k2 (lowestSetIdx rem))) := by
        rw [diffKids, dif_neg h0]
      have hlt : (clearLowest rem).toNat < n := by
        rw [← hrem]; exact toNat_clearLowest_lt rem hrem0
      obtain ⟨ihsize, ihpref, ihthird⟩ :=
        IH (clearLowest rem).toNat hlt (clearLowest rem) rfl
          (acc.push (diffChild m1 k1 m2 k2 (lowestSetIdx rem)))
      have hpc : popCount (clearLowest rem) + 1 = popCount rem := popCount_clearLowest rem hrem0
      have haccsz : (acc.push (diffChild m1 k1 m2 k2 (lowestSetIdx rem))).size = acc.size + 1 :=
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

/-- Reading a present slot of the rebuilt child array recovers that slot's `diffChild`. -/
private theorem childAt_diffKids (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) (c : UInt32) (hc : c < 32) (htb : testBit m1 c = true) :
    childAt m1 (diffKids m1 k1 m2 k2 m1 #[]) c = diffChild m1 k1 m2 k2 c := by
  obtain ⟨_, _, hthird⟩ := diffKids_spec m1 k1 m2 k2 m1.toNat m1 rfl #[]
  have hc' := hthird c hc htb
  unfold childAt
  rw [show (#[] : Array (PTree L)).size = 0 from rfl, Nat.zero_add] at hc'
  rw [hc', Option.getD_some]

/-- `diffChild` at a present left slot: recurse on both children when `m2` also has the slot,
else carry `a`'s child over whole. -/
private theorem diffChild_eq (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) (c : UInt32) (hsz1 : k1.size = popCount m1)
    (hsz2 : k2.size = popCount m2) (htb1 : testBit m1 c = true) :
    diffChild m1 k1 m2 k2 c
      = if testBit m2 c then diffU (childAt m1 k1 c) (childAt m2 k2 c)
        else childAt m1 k1 c := by
  have h1 : arrayIndex m1 c < k1.size := by rw [hsz1]; exact arrayIndex_lt m1 c htb1
  have hcA1 : childAt m1 k1 c = k1[arrayIndex m1 c]'h1 := by
    unfold childAt; rw [Array.getElem?_eq_getElem h1, Option.getD_some]
  by_cases hm2 : testBit m2 c = true
  · have h2 : arrayIndex m2 c < k2.size := by rw [hsz2]; exact arrayIndex_lt m2 c hm2
    have hcA2 : childAt m2 k2 c = k2[arrayIndex m2 c]'h2 := by
      unfold childAt; rw [Array.getElem?_eq_getElem h2, Option.getD_some]
    rw [diffChild, dif_pos h1, if_pos hm2, dif_pos h2, if_pos hm2, hcA1, hcA2]
  · rw [diffChild, dif_pos h1, if_neg hm2, if_neg hm2, hcA1]

/-- Splicing any `WF` replacement `t'` over one routed child of a well-formed `bin` (then
re-compressing) preserves `WF`, provided `t'`'s keys share their high bits with the replaced
child's keys; and every key of the result shares its high bits with one of the `bin`'s keys.
`erase_WF_keys`' `bin` case factored over the replacement subtree, so the subtraction merges
(`diffU`, `symmDiffU`) can splice their recursive results through it. -/
private theorem splice_WF_keys (bp bl : Nat) (bm : UInt32) (bk : Array (PTree L)) (c0 : UInt32)
    (hc0 : c0 < 32) (htb : testBit bm c0 = true) (h : arrayIndex bm c0 < bk.size) (t' : PTree L)
    (hwf : WF (.bin bp bl bm bk)) (ihwf : WF t')
    (ihkeys : ∀ j, contains j t' = true →
        ∃ j', contains j' (bk[arrayIndex bm c0]'h) = true ∧ j >>> 5 = j' >>> 5) :
    WF (finalize bp bl bm (bk.set (arrayIndex bm c0) t' h))
      ∧ ∀ j, contains j (finalize bp bl bm (bk.set (arrayIndex bm c0) t' h)) = true →
          ∃ j', contains j' (.bin bp bl bm bk) = true ∧ j >>> 5 = j' >>> 5 := by
  have hwf' := hwf
  rw [WF] at hwf'
  obtain ⟨hl, hsz, _, hwfk, _, hal⟩ := hwf'
  have hcA : childAt bm bk c0 = bk[arrayIndex bm c0]'h := by
    unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
  have hset : ∀ c, c < 32 → testBit bm c = true →
      childAt bm (bk.set (arrayIndex bm c0) t' h) c
        = if c = c0 then t' else childAt bm bk c := by
    intro c hc htc
    unfold childAt
    rw [Array.getElem?_set h]
    by_cases hcc : c = c0
    · subst hcc
      rw [if_pos rfl, if_pos rfl, Option.getD_some]
    · rw [if_neg hcc,
          if_neg (arrayIndex_inj bm c0 c hc0 hc htb htc (fun hh => hcc hh.symm))]
  have hal' : ∀ c, c < 32 → testBit bm c = true →
      AlignedAt bl c bp (childAt bm (bk.set (arrayIndex bm c0) t' h) c) := by
    intro c hc htc
    rw [hset c hc htc]
    by_cases hcc : c = c0
    · rw [if_pos hcc]
      intro j hj
      obtain ⟨j', hj', h5⟩ := ihkeys j hj
      have hj'A : contains j' (childAt bm bk c) = true := by
        rw [hcc, hcA]; exact hj'
      obtain ⟨hch, hpf⟩ := hal c hc htc j' hj'A
      exact ⟨(chunk_eq_of_hi bl hl h5).trans hch,
             (prefixAbove_eq_of_hi bl h5).trans hpf⟩
    · rw [if_neg hcc]
      exact hal c hc htc
  refine ⟨WF_finalize bp bl bm _ hl ?_ hal', ?_⟩
  · intro c hc htc
    rw [hset c hc htc]
    by_cases hcc : c = c0
    · rw [if_pos hcc]; exact ihwf
    · rw [if_neg hcc]
      have hbc : arrayIndex bm c < bk.size := by
        rw [hsz]; exact arrayIndex_lt bm c htc
      have hcA' : childAt bm bk c = bk[arrayIndex bm c]'hbc := by
        unfold childAt; rw [Array.getElem?_eq_getElem hbc, Option.getD_some]
      rw [hcA']
      exact hwfk _ (Array.getElem_mem hbc)
  · intro j hj
    rw [contains_finalize j bp bl bm _ hal'] at hj
    obtain ⟨htj, hcj⟩ := and_split hj
    rw [hset (chunk j bl) (chunk_lt j bl) htj] at hcj
    by_cases hcc : chunk j bl = c0
    · rw [if_pos hcc] at hcj
      obtain ⟨j', hj', h5⟩ := ihkeys j hcj
      refine ⟨j', ?_, h5⟩
      rw [contains_bin]
      have hj'A : contains j' (childAt bm bk c0) = true := by
        rw [hcA]; exact hj'
      obtain ⟨hch, _⟩ := hal c0 hc0 htb j' hj'A
      rw [hch, htb, Bool.true_and, hcA]
      exact hj'
    · rw [if_neg hcc] at hcj
      refine ⟨j, ?_, rfl⟩
      rw [contains_bin, htj, Bool.true_and]
      exact hcj

set_option maxHeartbeats 400000 in
/-- `diffU` preserves `WF`, and every surviving key shares its high bits with one of the LEFT
operand's keys (the `AlignedAt`-transfer fact `finalize` needs — see the filter/erase section
note). Member recursion on the combined size, mirroring the walk's routing. -/
private theorem diff_WF_keys : (a b : PTree L) → WF a → WF b →
    WF (diffU a b)
      ∧ ∀ j, contains j (diffU a b) = true → ∃ j', contains j' a = true ∧ j >>> 5 = j' >>> 5
  | .nil, _ => fun _ _ => by
      rw [diffU]
      exact ⟨by rw [WF]; trivial,
             fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
  | .tip p1 b1, .nil => fun hwa _ => by
      rw [diffU]
      exact ⟨hwa, fun j hj => ⟨j, hj, rfl⟩⟩
  | .bin bp bl bm bk, .nil => fun hwa _ => by
      rw [diffU]
      exact ⟨hwa, fun j hj => ⟨j, hj, rfl⟩⟩
  | .tip p1 b1, .tip p2 b2 => fun hwa _ => by
      rw [diffU]
      by_cases hp : (p1 == p2) = true
      · rw [if_pos hp]
        by_cases he : LeafOps.isEmpty (LeafOps.diff b1 b2) = true
        · rw [if_pos he]
          exact ⟨by rw [WF]; trivial,
                 fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
        · rw [if_neg he]
          refine ⟨by rw [WF]; simpa using he, ?_⟩
          intro j hj
          obtain ⟨j', hj'⟩ := exists_mem (.tip p1 b1) hwa (by simp)
          exact ⟨j', hj', (hi_eq_of_contains_tip hj).trans (hi_eq_of_contains_tip hj').symm⟩
      · rw [if_neg hp]
        exact ⟨hwa, fun j hj => ⟨j, hj, rfl⟩⟩
  | .tip p1 b1, .bin bp bl bm bk => fun hwa hwb => by
      rw [diffU]
      by_cases hcond : ((prefixAbove (someKey (.tip p1 b1)) bl == bp)
          && testBit bm (chunk (someKey (.tip p1 b1)) bl)) = true
      · rw [if_pos hcond]
        by_cases h : arrayIndex bm (chunk (someKey (.tip p1 b1)) bl) < bk.size
        · rw [dif_pos h]
          have hwfchild : WF (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h) := by
            rw [WF] at hwb; exact hwb.2.2.2.1 _ (Array.getElem_mem h)
          exact diff_WF_keys (.tip p1 b1)
            (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h) hwa hwfchild
        · rw [dif_neg h]
          exact ⟨hwa, fun j hj => ⟨j, hj, rfl⟩⟩
      · rw [if_neg hcond]
        exact ⟨hwa, fun j hj => ⟨j, hj, rfl⟩⟩
  | .bin bp bl bm bk, .tip p2 b2 => fun hwa hwb => by
      rw [diffU]
      by_cases hcond : ((prefixAbove (someKey (.tip p2 b2)) bl == bp)
          && testBit bm (chunk (someKey (.tip p2 b2)) bl)) = true
      · rw [if_pos hcond]
        by_cases h : arrayIndex bm (chunk (someKey (.tip p2 b2)) bl) < bk.size
        · rw [dif_pos h]
          have hwfchild : WF (bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h) := by
            rw [WF] at hwa; exact hwa.2.2.2.1 _ (Array.getElem_mem h)
          obtain ⟨ihwf, ihkeys⟩ :=
            diff_WF_keys (bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h)
              (.tip p2 b2) hwfchild hwb
          exact splice_WF_keys bp bl bm bk (chunk (someKey (.tip p2 b2)) bl)
            (chunk_lt _ _) (and_split hcond).2 h _ hwa ihwf ihkeys
        · rw [dif_neg h]
          exact ⟨hwa, fun j hj => ⟨j, hj, rfl⟩⟩
      · rw [if_neg hcond]
        exact ⟨hwa, fun j hj => ⟨j, hj, rfl⟩⟩
  | .bin p1 l1 m1 k1, .bin p2 l2 m2 k2 => fun hwa hwb => by
      by_cases heq : (l1 == l2) = true
      · have hleq : l1 = l2 := by simpa using heq
        subst hleq
        by_cases hpfx : (prefixAbove (someKey (.bin p1 l1 m1 k1)) l1
            == prefixAbove (someKey (.bin p2 l1 m2 k2)) l1) = true
        · rw [diffU, if_pos heq, if_pos hpfx, Array.emptyWithCapacity_eq]
          have hwa' := hwa
          rw [WF] at hwa'
          obtain ⟨hl1, hsz1, _, hwfk1, _, hal1⟩ := hwa'
          have hwb' := hwb
          rw [WF] at hwb'
          obtain ⟨_, hsz2, _, hwfk2, _, _⟩ := hwb'
          have hslot : ∀ c, c < 32 → testBit m1 c = true →
              WF (diffChild m1 k1 m2 k2 c)
              ∧ ∀ j, contains j (diffChild m1 k1 m2 k2 c) = true →
                  ∃ j', contains j' (childAt m1 k1 c) = true ∧ j >>> 5 = j' >>> 5 := by
            intro c hc htc
            have hb1 : arrayIndex m1 c < k1.size := by
              rw [hsz1]; exact arrayIndex_lt m1 c htc
            have hcA1 : childAt m1 k1 c = k1[arrayIndex m1 c]'hb1 := by
              unfold childAt; rw [Array.getElem?_eq_getElem hb1, Option.getD_some]
            by_cases hm2 : testBit m2 c = true
            · have hb2 : arrayIndex m2 c < k2.size := by
                rw [hsz2]; exact arrayIndex_lt m2 c hm2
              have hcA2 : childAt m2 k2 c = k2[arrayIndex m2 c]'hb2 := by
                unfold childAt; rw [Array.getElem?_eq_getElem hb2, Option.getD_some]
              rw [diffChild_eq m1 k1 m2 k2 c hsz1 hsz2 htc, if_pos hm2, hcA1, hcA2]
              exact diff_WF_keys (k1[arrayIndex m1 c]'hb1) (k2[arrayIndex m2 c]'hb2)
                (hwfk1 _ (Array.getElem_mem hb1)) (hwfk2 _ (Array.getElem_mem hb2))
            · rw [diffChild_eq m1 k1 m2 k2 c hsz1 hsz2 htc, if_neg hm2, hcA1]
              exact ⟨hwfk1 _ (Array.getElem_mem hb1), fun j hj => ⟨j, hj, rfl⟩⟩
          have hal' : ∀ c, c < 32 → testBit m1 c = true →
              AlignedAt l1 c p1 (childAt m1 (diffKids m1 k1 m2 k2 m1 #[]) c) := by
            intro c hc htc
            rw [childAt_diffKids m1 k1 m2 k2 c hc htc]
            intro j hj
            obtain ⟨j', hj', h5⟩ := (hslot c hc htc).2 j hj
            obtain ⟨hch, hpf⟩ := hal1 c hc htc j' hj'
            exact ⟨(chunk_eq_of_hi l1 hl1 h5).trans hch,
                   (prefixAbove_eq_of_hi l1 h5).trans hpf⟩
          refine ⟨WF_finalize p1 l1 m1 _ hl1 ?_ hal', ?_⟩
          · intro c hc htc
            rw [childAt_diffKids m1 k1 m2 k2 c hc htc]
            exact (hslot c hc htc).1
          · intro j hj
            rw [contains_finalize j p1 l1 m1 _ hal'] at hj
            obtain ⟨htj, hcj⟩ := and_split hj
            rw [childAt_diffKids m1 k1 m2 k2 (chunk j l1) (chunk_lt j l1) htj] at hcj
            obtain ⟨j', hj', h5⟩ := (hslot (chunk j l1) (chunk_lt j l1) htj).2 j hcj
            refine ⟨j', ?_, h5⟩
            rw [contains_bin]
            obtain ⟨hch, _⟩ := hal1 (chunk j l1) (chunk_lt j l1) htj j' hj'
            rw [hch, htj, Bool.true_and]
            exact hj'
        · rw [diffU, if_pos heq, if_neg hpfx]
          exact ⟨hwa, fun j hj => ⟨j, hj, rfl⟩⟩
      · by_cases hlt : l2 < l1
        · by_cases hcond : ((prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 == p1)
              && testBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)) = true
          · rw [diffU, if_neg heq, if_pos hlt, if_pos hcond]
            by_cases h : arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) < k1.size
            · rw [dif_pos h]
              have hwfchild :
                  WF (k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h) := by
                rw [WF] at hwa; exact hwa.2.2.2.1 _ (Array.getElem_mem h)
              obtain ⟨ihwf, ihkeys⟩ :=
                diff_WF_keys (k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h)
                  (.bin p2 l2 m2 k2) hwfchild hwb
              exact splice_WF_keys p1 l1 m1 k1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)
                (chunk_lt _ _) (and_split hcond).2 h _ hwa ihwf ihkeys
            · rw [dif_neg h]
              exact ⟨hwa, fun j hj => ⟨j, hj, rfl⟩⟩
          · rw [diffU, if_neg heq, if_pos hlt, if_neg hcond]
            exact ⟨hwa, fun j hj => ⟨j, hj, rfl⟩⟩
        · by_cases hcond : ((prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 == p2)
              && testBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)) = true
          · rw [diffU, if_neg heq, if_neg hlt, if_pos hcond]
            by_cases h : arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) < k2.size
            · rw [dif_pos h]
              have hwfchild :
                  WF (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h) := by
                rw [WF] at hwb; exact hwb.2.2.2.1 _ (Array.getElem_mem h)
              exact diff_WF_keys (.bin p1 l1 m1 k1)
                (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h) hwa hwfchild
            · rw [dif_neg h]
              exact ⟨hwa, fun j hj => ⟨j, hj, rfl⟩⟩
          · rw [diffU, if_neg heq, if_neg hlt, if_neg hcond]
            exact ⟨hwa, fun j hj => ⟨j, hj, rfl⟩⟩
termination_by a b => sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := Array.sizeOf_lt_of_mem (Array.getElem_mem h); omega)
    | (have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb1)
       have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb2); omega)
    | omega

/-- `diff` preserves canonical shape. -/
theorem WF_diff (a b : PTree L) (hwa : WF a) (hwb : WF b) : WF (diff a b) := by
  rw [diff]; exact (diff_WF_keys a b hwa hwb).1

/-! ### Symmetric difference

`symmDiffU` removes AND adds keys (one-sided subtrees survive, shared keys cancel), so its `WF`
proof carries a two-sided provenance: every surviving key shares its high bits with a key of one
OPERAND. The aligned-`bin` case rebuilds the union mask's children (the `diffKids` pattern over
`m1 ||| m2`), the routed shrink cases go through `splice2_WF_keys` (the two-sided
`splice_WF_keys`), the grow cases through union's `WF_splice`/`contains_splice`, and the
divergence cases through `join_WF_keys`. -/

/-- `symmKids`' fold invariant — the verbatim `diffKids_spec` shape for the union mask. -/
private theorem symmKids_spec (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) :
    ∀ (n : Nat) (rem : UInt32), rem.toNat = n → ∀ (acc : Array (PTree L)),
      (symmKids m1 k1 m2 k2 rem acc).size = acc.size + popCount rem
      ∧ (∀ i, i < acc.size → (symmKids m1 k1 m2 k2 rem acc)[i]? = acc[i]?)
      ∧ (∀ c, c < 32 → testBit rem c = true →
           (symmKids m1 k1 m2 k2 rem acc)[acc.size + arrayIndex rem c]?
             = some (symmChild m1 k1 m2 k2 c)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro rem hrem acc
    by_cases h0 : (rem == 0) = true
    · have hr0 : rem = 0 := by simpa using h0
      rw [symmKids, dif_pos h0]
      refine ⟨?_, ?_, ?_⟩
      · rw [hr0, show popCount (0 : UInt32) = 0 from rfl, Nat.add_zero]
      · intro i hi; rfl
      · intro c hc htb; rw [hr0, testBit_zero] at htb; exact absurd htb (by decide)
    · have hrem0 : rem ≠ 0 := by intro h; exact h0 (by rw [h]; rfl)
      have hstep : symmKids m1 k1 m2 k2 rem acc
          = symmKids m1 k1 m2 k2 (clearLowest rem)
              (acc.push (symmChild m1 k1 m2 k2 (lowestSetIdx rem))) := by
        rw [symmKids, dif_neg h0]
      have hlt : (clearLowest rem).toNat < n := by
        rw [← hrem]; exact toNat_clearLowest_lt rem hrem0
      obtain ⟨ihsize, ihpref, ihthird⟩ :=
        IH (clearLowest rem).toNat hlt (clearLowest rem) rfl
          (acc.push (symmChild m1 k1 m2 k2 (lowestSetIdx rem)))
      have hpc : popCount (clearLowest rem) + 1 = popCount rem := popCount_clearLowest rem hrem0
      have haccsz : (acc.push (symmChild m1 k1 m2 k2 (lowestSetIdx rem))).size = acc.size + 1 :=
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

/-- Reading a present slot of the rebuilt union-mask array recovers that slot's `symmChild`. -/
private theorem childAt_symmKids (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) (c : UInt32) (hc : c < 32) (htb : testBit (m1 ||| m2) c = true) :
    childAt (m1 ||| m2) (symmKids m1 k1 m2 k2 (m1 ||| m2) #[]) c = symmChild m1 k1 m2 k2 c := by
  obtain ⟨_, _, hthird⟩ := symmKids_spec m1 k1 m2 k2 (m1 ||| m2).toNat (m1 ||| m2) rfl #[]
  have hc' := hthird c hc htb
  unfold childAt
  rw [show (#[] : Array (PTree L)).size = 0 from rfl, Nat.zero_add] at hc'
  rw [hc', Option.getD_some]

/-- `symmChild` reads as the three-way slot split: shared → recurse, one-sided → that side's
child whole. -/
private theorem symmChild_eq (m1 : UInt32) (k1 : Array (PTree L)) (m2 : UInt32)
    (k2 : Array (PTree L)) (c : UInt32) (hsz1 : k1.size = popCount m1)
    (hsz2 : k2.size = popCount m2) :
    symmChild m1 k1 m2 k2 c
      = if testBit m1 c then
          (if testBit m2 c then symmDiffU (childAt m1 k1 c) (childAt m2 k2 c)
           else childAt m1 k1 c)
        else childAt m2 k2 c := by
  by_cases ht1 : testBit m1 c = true
  · have h1 : arrayIndex m1 c < k1.size := by rw [hsz1]; exact arrayIndex_lt m1 c ht1
    have hcA1 : childAt m1 k1 c = k1[arrayIndex m1 c]'h1 := by
      unfold childAt; rw [Array.getElem?_eq_getElem h1, Option.getD_some]
    by_cases ht2 : testBit m2 c = true
    · have h2 : arrayIndex m2 c < k2.size := by rw [hsz2]; exact arrayIndex_lt m2 c ht2
      have hcA2 : childAt m2 k2 c = k2[arrayIndex m2 c]'h2 := by
        unfold childAt; rw [Array.getElem?_eq_getElem h2, Option.getD_some]
      rw [symmChild, if_pos ht1, if_pos ht2, dif_pos h1, dif_pos h2,
          if_pos ht1, if_pos ht2, hcA1, hcA2]
    · rw [symmChild, if_pos ht1, if_neg ht2, dif_pos h1, if_pos ht1, if_neg ht2, hcA1]
  · rw [symmChild, if_neg ht1, if_neg ht1]
    unfold childAt
    by_cases h2 : arrayIndex m2 c < k2.size
    · rw [dif_pos h2, Array.getElem?_eq_getElem h2, Option.getD_some]
    · rw [dif_neg h2, Array.getElem?_eq_none (Nat.le_of_not_lt h2), Option.getD_none]

/-- The two-sided `splice_WF_keys`: the replacement `t'` may also carry keys of a routed operand
`op` (aligned at the spliced slot), and the provenance disjunction tracks both sources. The
routed-shrink cases of `symmDiffU` splice through this. -/
private theorem splice2_WF_keys (bp bl : Nat) (bm : UInt32) (bk : Array (PTree L)) (c0 : UInt32)
    (hc0 : c0 < 32) (htb : testBit bm c0 = true) (h : arrayIndex bm c0 < bk.size)
    (t' op : PTree L) (hwf : WF (.bin bp bl bm bk)) (ihwf : WF t')
    (hopal : AlignedAt bl c0 bp op)
    (ihkeys : ∀ j, contains j t' = true →
        (∃ j', contains j' (bk[arrayIndex bm c0]'h) = true ∧ j >>> 5 = j' >>> 5)
        ∨ (∃ j', contains j' op = true ∧ j >>> 5 = j' >>> 5)) :
    WF (finalize bp bl bm (bk.set (arrayIndex bm c0) t' h))
      ∧ ∀ j, contains j (finalize bp bl bm (bk.set (arrayIndex bm c0) t' h)) = true →
          (∃ j', contains j' (.bin bp bl bm bk) = true ∧ j >>> 5 = j' >>> 5)
          ∨ (∃ j', contains j' op = true ∧ j >>> 5 = j' >>> 5) := by
  have hwf' := hwf
  rw [WF] at hwf'
  obtain ⟨hl, hsz, _, hwfk, _, hal⟩ := hwf'
  have hcA : childAt bm bk c0 = bk[arrayIndex bm c0]'h := by
    unfold childAt; rw [Array.getElem?_eq_getElem h, Option.getD_some]
  have hset : ∀ c, c < 32 → testBit bm c = true →
      childAt bm (bk.set (arrayIndex bm c0) t' h) c
        = if c = c0 then t' else childAt bm bk c := by
    intro c hc htc
    unfold childAt
    rw [Array.getElem?_set h]
    by_cases hcc : c = c0
    · subst hcc
      rw [if_pos rfl, if_pos rfl, Option.getD_some]
    · rw [if_neg hcc,
          if_neg (arrayIndex_inj bm c0 c hc0 hc htb htc (fun hh => hcc hh.symm))]
  have hal' : ∀ c, c < 32 → testBit bm c = true →
      AlignedAt bl c bp (childAt bm (bk.set (arrayIndex bm c0) t' h) c) := by
    intro c hc htc
    rw [hset c hc htc]
    by_cases hcc : c = c0
    · rw [if_pos hcc]
      intro j hj
      rcases ihkeys j hj with ⟨j', hj', h5⟩ | ⟨j', hj', h5⟩
      · have hj'A : contains j' (childAt bm bk c) = true := by
          rw [hcc, hcA]; exact hj'
        obtain ⟨hch, hpf⟩ := hal c hc htc j' hj'A
        exact ⟨(chunk_eq_of_hi bl hl h5).trans hch,
               (prefixAbove_eq_of_hi bl h5).trans hpf⟩
      · obtain ⟨hch, hpf⟩ := hopal j' hj'
        rw [hcc]
        exact ⟨(chunk_eq_of_hi bl hl h5).trans hch,
               (prefixAbove_eq_of_hi bl h5).trans hpf⟩
    · rw [if_neg hcc]
      exact hal c hc htc
  refine ⟨WF_finalize bp bl bm _ hl ?_ hal', ?_⟩
  · intro c hc htc
    rw [hset c hc htc]
    by_cases hcc : c = c0
    · rw [if_pos hcc]; exact ihwf
    · rw [if_neg hcc]
      have hbc : arrayIndex bm c < bk.size := by
        rw [hsz]; exact arrayIndex_lt bm c htc
      have hcA' : childAt bm bk c = bk[arrayIndex bm c]'hbc := by
        unfold childAt; rw [Array.getElem?_eq_getElem hbc, Option.getD_some]
      rw [hcA']
      exact hwfk _ (Array.getElem_mem hbc)
  · intro j hj
    rw [contains_finalize j bp bl bm _ hal'] at hj
    obtain ⟨htj, hcj⟩ := and_split hj
    rw [hset (chunk j bl) (chunk_lt j bl) htj] at hcj
    by_cases hcc : chunk j bl = c0
    · rw [if_pos hcc] at hcj
      rcases ihkeys j hcj with ⟨j', hj', h5⟩ | ⟨j', hj', h5⟩
      · refine Or.inl ⟨j', ?_, h5⟩
        rw [contains_bin]
        have hj'A : contains j' (childAt bm bk c0) = true := by
          rw [hcA]; exact hj'
        obtain ⟨hch, _⟩ := hal c0 hc0 htb j' hj'A
        rw [hch, htb, Bool.true_and, hcA]
        exact hj'
      · exact Or.inr ⟨j', hj', h5⟩
    · rw [if_neg hcc] at hcj
      refine Or.inl ⟨j, ?_, rfl⟩
      rw [contains_bin, htj, Bool.true_and]
      exact hcj

/-- A divergent-prefix `join` of two aligned, well-formed, non-`nil` subtrees is well-formed, and
its keys are exactly the operands' keys. The shared tail of every prefix-mismatch case of the
symmetric difference. -/
private theorem join_WF_keys (ka kb : Nat) (A B : PTree L) (hkne : ka ≠ kb)
    (hl0 : 0 < branchLevel ka kb)
    (ha : AlignedAt (branchLevel ka kb) (chunk ka (branchLevel ka kb))
            (prefixAbove ka (branchLevel ka kb)) A)
    (hb : AlignedAt (branchLevel ka kb) (chunk kb (branchLevel ka kb))
            (prefixAbove ka (branchLevel ka kb)) B)
    (hwa : WF A) (hwb : WF B) (hane : A ≠ .nil) (hbne : B ≠ .nil) :
    WF (join ka A kb B)
      ∧ ∀ j, contains j (join ka A kb B) = true →
          contains j A = true ∨ contains j B = true := by
  constructor
  · rw [join]
    exact WF_join _ _ _ _ A B hl0 (chunk_lt _ _) (chunk_lt _ _)
      (chunk_branchLevel_ne ka kb hkne) ha hb hwa hwb hane hbne
  · intro j hj
    rw [contains_join_eq j ka kb A B hkne ha hb, Bool.or_eq_true] at hj
    exact hj

set_option maxHeartbeats 800000 in
/-- `symmDiffU` preserves `WF`, and every surviving key shares its high bits with a key of one of
the operands (two-sided provenance — the `AlignedAt`-transfer fact `finalize` and the splices
need). Member recursion on the combined size, mirroring the walk's routing. -/
private theorem symmDiff_WF_keys : (a b : PTree L) → WF a → WF b →
    WF (symmDiffU a b)
      ∧ ∀ j, contains j (symmDiffU a b) = true →
          (∃ j', contains j' a = true ∧ j >>> 5 = j' >>> 5)
          ∨ (∃ j', contains j' b = true ∧ j >>> 5 = j' >>> 5)
  | .nil, t => fun _ hwb => by
      rw [symmDiffU]
      exact ⟨hwb, fun j hj => Or.inr ⟨j, hj, rfl⟩⟩
  | .tip p1 b1, .nil => fun hwa _ => by
      rw [symmDiffU]
      exact ⟨hwa, fun j hj => Or.inl ⟨j, hj, rfl⟩⟩
  | .bin bp bl bm bk, .nil => fun hwa _ => by
      rw [symmDiffU]
      exact ⟨hwa, fun j hj => Or.inl ⟨j, hj, rfl⟩⟩
  | .tip p1 b1, .tip p2 b2 => fun hwa hwb => by
      have hb1 : LeafOps.isEmpty b1 = false := by rw [WF] at hwa; exact hwa
      have hb2 : LeafOps.isEmpty b2 = false := by rw [WF] at hwb; exact hwb
      rw [symmDiffU]
      by_cases hp : (p1 == p2) = true
      · rw [if_pos hp]
        by_cases he : LeafOps.isEmpty (LeafOps.symmDiff b1 b2) = true
        · rw [if_pos he]
          exact ⟨by rw [WF]; trivial,
                 fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
        · rw [if_neg he]
          refine ⟨by rw [WF]; simpa using he, ?_⟩
          intro j hj
          obtain ⟨j', hj'⟩ := exists_mem (.tip p1 b1) hwa (by simp)
          exact Or.inl ⟨j', hj', (hi_eq_of_contains_tip hj).trans (hi_eq_of_contains_tip hj').symm⟩
      · rw [if_neg hp]
        have hpne : p1 ≠ p2 := fun h => hp (by rw [h]; exact beq_self_eq_true p2)
        have hsk1 : someKey (.tip p1 b1) >>> 5 = p1 := someKey_tip_shiftRight5 p1 b1 hb1
        have hsk2 : someKey (.tip p2 b2) >>> 5 = p2 := someKey_tip_shiftRight5 p2 b2 hb2
        have hkne : someKey (.tip p1 b1) ≠ someKey (.tip p2 b2) := by
          intro h; apply hpne; rw [← hsk1, ← hsk2, h]
        have hkne5 : someKey (.tip p1 b1) >>> 5 ≠ someKey (.tip p2 b2) >>> 5 := by
          rw [hsk1, hsk2]; exact hpne
        have hl0 : 0 < branchLevel (someKey (.tip p1 b1)) (someKey (.tip p2 b2)) :=
          branchLevel_pos _ _ hkne5
        obtain ⟨jwf, jkeys⟩ := join_WF_keys (someKey (.tip p1 b1)) (someKey (.tip p2 b2))
          (.tip p1 b1) (.tip p2 b2) hkne hl0 (aligned_tip p1 b1 hb1 _ hl0)
          (by rw [prefixAbove_branchLevel_eq (someKey (.tip p1 b1)) (someKey (.tip p2 b2))]
              exact aligned_tip p2 b2 hb2 _ hl0)
          hwa hwb (by simp) (by simp)
        refine ⟨jwf, fun j hj => ?_⟩
        rcases jkeys j hj with hA | hB
        · exact Or.inl ⟨j, hA, rfl⟩
        · exact Or.inr ⟨j, hB, rfl⟩
  | .tip p1 b1, .bin bp bl bm bk => fun hwa hwb => by
      have hb1 : LeafOps.isEmpty b1 = false := by rw [WF] at hwa; exact hwa
      have hbl0 : 0 < bl := by rw [WF] at hwb; exact hwb.1
      by_cases hpfx : (prefixAbove (someKey (.tip p1 b1)) bl == bp) = true
      · have hpfxeq : prefixAbove (someKey (.tip p1 b1)) bl = bp := by simpa using hpfx
        have halign : AlignedAt bl (chunk (someKey (.tip p1 b1)) bl) bp (.tip p1 b1) :=
          by rw [← hpfxeq]; exact aligned_tip p1 b1 hb1 bl hbl0
        by_cases htb : testBit bm (chunk (someKey (.tip p1 b1)) bl) = true
        · by_cases h : arrayIndex bm (chunk (someKey (.tip p1 b1)) bl) < bk.size
          · rw [symmDiffU, if_pos hpfx, if_pos htb, dif_pos h]
            have hwfchild : WF (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h) := by
              rw [WF] at hwb; exact hwb.2.2.2.1 _ (Array.getElem_mem h)
            obtain ⟨ihwf, ihkeys⟩ :=
              symmDiff_WF_keys (.tip p1 b1)
                (bk[arrayIndex bm (chunk (someKey (.tip p1 b1)) bl)]'h) hwa hwfchild
            obtain ⟨swf, skeys⟩ := splice2_WF_keys bp bl bm bk
              (chunk (someKey (.tip p1 b1)) bl) (chunk_lt _ _) htb h _ (.tip p1 b1)
              hwb ihwf halign (fun j hj => (ihkeys j hj).elim Or.inr Or.inl)
            exact ⟨swf, fun j hj => (skeys j hj).elim Or.inr Or.inl⟩
          · rw [symmDiffU, if_pos hpfx, if_pos htb, dif_neg h]
            exact ⟨hwb, fun j hj => Or.inr ⟨j, hj, rfl⟩⟩
        · rw [symmDiffU, if_pos hpfx, if_neg htb]
          have htbf : testBit bm (chunk (someKey (.tip p1 b1)) bl) = false := by simpa using htb
          refine ⟨WF_splice (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl)
            (chunk_lt _ _) hwb halign hwa (by simp) htbf, ?_⟩
          intro j hj
          rw [contains_splice j (.tip p1 b1) bp bl bm bk (chunk (someKey (.tip p1 b1)) bl)
              (chunk_lt _ _) hwb halign htbf, Bool.or_eq_true] at hj
          rcases hj with hj1 | hj2
          · exact Or.inl ⟨j, hj1, rfl⟩
          · exact Or.inr ⟨j, hj2, rfl⟩
      · rw [symmDiffU, if_neg hpfx]
        have hmne : bm ≠ 0 := by
          rw [WF] at hwb; obtain ⟨_, _, hpc, _, _, _⟩ := hwb
          intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
        have hskbin : prefixAbove (someKey (.bin bp bl bm bk)) bl = bp :=
          someKey_bin_prefixAbove bp bl bm bk hmne
        have hpfxne : prefixAbove (someKey (.tip p1 b1)) bl ≠ bp := by
          intro h; exact hpfx (by rw [h]; exact beq_self_eq_true bp)
        have hdiv : someKey (.bin bp bl bm bk) >>> (5 * (bl + 1))
            ≠ someKey (.tip p1 b1) >>> (5 * (bl + 1)) := by
          show prefixAbove (someKey (.bin bp bl bm bk)) bl ≠ prefixAbove (someKey (.tip p1 b1)) bl
          rw [hskbin]; exact fun h => hpfxne h.symm
        have hkne : someKey (.bin bp bl bm bk) ≠ someKey (.tip p1 b1) := fun h => hdiv (by rw [h])
        have hbl_lt : bl < branchLevel (someKey (.bin bp bl bm bk)) (someKey (.tip p1 b1)) :=
          lt_branchLevel _ _ bl hdiv
        have hl0 : 0 < branchLevel (someKey (.bin bp bl bm bk)) (someKey (.tip p1 b1)) :=
          Nat.lt_trans hbl0 hbl_lt
        obtain ⟨jwf, jkeys⟩ := join_WF_keys (someKey (.bin bp bl bm bk)) (someKey (.tip p1 b1))
          (.bin bp bl bm bk) (.tip p1 b1) hkne hl0
          (aligned_bin bp bl bm bk hwb _ hbl_lt)
          (by rw [prefixAbove_branchLevel_eq (someKey (.bin bp bl bm bk)) (someKey (.tip p1 b1))]
              exact aligned_tip p1 b1 hb1 _ hl0)
          hwb hwa (by simp) (by simp)
        refine ⟨jwf, fun j hj => ?_⟩
        rcases jkeys j hj with hB | hA
        · exact Or.inr ⟨j, hB, rfl⟩
        · exact Or.inl ⟨j, hA, rfl⟩
  | .bin bp bl bm bk, .tip p2 b2 => fun hwa hwb => by
      have hb2 : LeafOps.isEmpty b2 = false := by rw [WF] at hwb; exact hwb
      have hbl0 : 0 < bl := by rw [WF] at hwa; exact hwa.1
      by_cases hpfx : (prefixAbove (someKey (.tip p2 b2)) bl == bp) = true
      · have hpfxeq : prefixAbove (someKey (.tip p2 b2)) bl = bp := by simpa using hpfx
        have halign : AlignedAt bl (chunk (someKey (.tip p2 b2)) bl) bp (.tip p2 b2) :=
          by rw [← hpfxeq]; exact aligned_tip p2 b2 hb2 bl hbl0
        by_cases htb : testBit bm (chunk (someKey (.tip p2 b2)) bl) = true
        · by_cases h : arrayIndex bm (chunk (someKey (.tip p2 b2)) bl) < bk.size
          · rw [symmDiffU, if_pos hpfx, if_pos htb, dif_pos h]
            have hwfchild : WF (bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h) := by
              rw [WF] at hwa; exact hwa.2.2.2.1 _ (Array.getElem_mem h)
            obtain ⟨ihwf, ihkeys⟩ :=
              symmDiff_WF_keys (bk[arrayIndex bm (chunk (someKey (.tip p2 b2)) bl)]'h)
                (.tip p2 b2) hwfchild hwb
            exact splice2_WF_keys bp bl bm bk (chunk (someKey (.tip p2 b2)) bl)
              (chunk_lt _ _) htb h _ (.tip p2 b2) hwa ihwf halign ihkeys
          · rw [symmDiffU, if_pos hpfx, if_pos htb, dif_neg h]
            exact ⟨hwa, fun j hj => Or.inl ⟨j, hj, rfl⟩⟩
        · rw [symmDiffU, if_pos hpfx, if_neg htb]
          have htbf : testBit bm (chunk (someKey (.tip p2 b2)) bl) = false := by simpa using htb
          refine ⟨WF_splice (.tip p2 b2) bp bl bm bk (chunk (someKey (.tip p2 b2)) bl)
            (chunk_lt _ _) hwa halign hwb (by simp) htbf, ?_⟩
          intro j hj
          rw [contains_splice j (.tip p2 b2) bp bl bm bk (chunk (someKey (.tip p2 b2)) bl)
              (chunk_lt _ _) hwa halign htbf, Bool.or_eq_true] at hj
          rcases hj with hj2 | hj1
          · exact Or.inr ⟨j, hj2, rfl⟩
          · exact Or.inl ⟨j, hj1, rfl⟩
      · rw [symmDiffU, if_neg hpfx]
        have hmne : bm ≠ 0 := by
          rw [WF] at hwa; obtain ⟨_, _, hpc, _, _, _⟩ := hwa
          intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
        have hskbin : prefixAbove (someKey (.bin bp bl bm bk)) bl = bp :=
          someKey_bin_prefixAbove bp bl bm bk hmne
        have hpfxne : prefixAbove (someKey (.tip p2 b2)) bl ≠ bp := by
          intro h; exact hpfx (by rw [h]; exact beq_self_eq_true bp)
        have hdiv : someKey (.bin bp bl bm bk) >>> (5 * (bl + 1))
            ≠ someKey (.tip p2 b2) >>> (5 * (bl + 1)) := by
          show prefixAbove (someKey (.bin bp bl bm bk)) bl ≠ prefixAbove (someKey (.tip p2 b2)) bl
          rw [hskbin]; exact fun h => hpfxne h.symm
        have hkne : someKey (.bin bp bl bm bk) ≠ someKey (.tip p2 b2) := fun h => hdiv (by rw [h])
        have hbl_lt : bl < branchLevel (someKey (.bin bp bl bm bk)) (someKey (.tip p2 b2)) :=
          lt_branchLevel _ _ bl hdiv
        have hl0 : 0 < branchLevel (someKey (.bin bp bl bm bk)) (someKey (.tip p2 b2)) :=
          Nat.lt_trans hbl0 hbl_lt
        obtain ⟨jwf, jkeys⟩ := join_WF_keys (someKey (.bin bp bl bm bk)) (someKey (.tip p2 b2))
          (.bin bp bl bm bk) (.tip p2 b2) hkne hl0
          (aligned_bin bp bl bm bk hwa _ hbl_lt)
          (by rw [prefixAbove_branchLevel_eq (someKey (.bin bp bl bm bk)) (someKey (.tip p2 b2))]
              exact aligned_tip p2 b2 hb2 _ hl0)
          hwa hwb (by simp) (by simp)
        refine ⟨jwf, fun j hj => ?_⟩
        rcases jkeys j hj with hA | hB
        · exact Or.inl ⟨j, hA, rfl⟩
        · exact Or.inr ⟨j, hB, rfl⟩
  | .bin p1 l1 m1 k1, .bin p2 l2 m2 k2 => fun hwa hwb => by
      by_cases hcond1 : (l1 == l2 && p1 == p2) = true
      · obtain ⟨hleq, hpeq⟩ : l1 = l2 ∧ p1 = p2 := by
          rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hcond1; exact hcond1
        subst hleq; subst hpeq
        rw [symmDiffU, if_pos hcond1, Array.emptyWithCapacity_eq]
        have hwa' := hwa
        rw [WF] at hwa'
        obtain ⟨hl0, hsz1, _, hwfk1, _, hrout1⟩ := hwa'
        have hwb' := hwb
        rw [WF] at hwb'
        obtain ⟨_, hsz2, _, hwfk2, _, hrout2⟩ := hwb'
        have hslot : ∀ c, c < 32 → testBit (m1 ||| m2) c = true →
            WF (symmChild m1 k1 m2 k2 c)
            ∧ ∀ j, contains j (symmChild m1 k1 m2 k2 c) = true →
                (testBit m1 c = true
                  ∧ ∃ j', contains j' (childAt m1 k1 c) = true ∧ j >>> 5 = j' >>> 5)
                ∨ (testBit m2 c = true
                  ∧ ∃ j', contains j' (childAt m2 k2 c) = true ∧ j >>> 5 = j' >>> 5) := by
          intro c hc htc
          by_cases ht1 : testBit m1 c = true
          · have hb1c : arrayIndex m1 c < k1.size := by
              rw [hsz1]; exact arrayIndex_lt m1 c ht1
            have hcA1 : childAt m1 k1 c = k1[arrayIndex m1 c]'hb1c := by
              unfold childAt; rw [Array.getElem?_eq_getElem hb1c, Option.getD_some]
            by_cases ht2 : testBit m2 c = true
            · have hb2c : arrayIndex m2 c < k2.size := by
                rw [hsz2]; exact arrayIndex_lt m2 c ht2
              have hcA2 : childAt m2 k2 c = k2[arrayIndex m2 c]'hb2c := by
                unfold childAt; rw [Array.getElem?_eq_getElem hb2c, Option.getD_some]
              rw [symmChild_eq m1 k1 m2 k2 c hsz1 hsz2, if_pos ht1, if_pos ht2, hcA1, hcA2]
              obtain ⟨ihwf, ihkeys⟩ :=
                symmDiff_WF_keys (k1[arrayIndex m1 c]'hb1c) (k2[arrayIndex m2 c]'hb2c)
                  (hwfk1 _ (Array.getElem_mem hb1c)) (hwfk2 _ (Array.getElem_mem hb2c))
              refine ⟨ihwf, fun j hj => ?_⟩
              rcases ihkeys j hj with ⟨j', hj', h5⟩ | ⟨j', hj', h5⟩
              · exact Or.inl ⟨ht1, j', hj', h5⟩
              · exact Or.inr ⟨ht2, j', hj', h5⟩
            · rw [symmChild_eq m1 k1 m2 k2 c hsz1 hsz2, if_pos ht1, if_neg ht2, hcA1]
              exact ⟨hwfk1 _ (Array.getElem_mem hb1c),
                     fun j hj => Or.inl ⟨ht1, j, hj, rfl⟩⟩
          · have hf1 : testBit m1 c = false := by simpa using ht1
            have ht2 : testBit m2 c = true := by
              rw [testBit_or, hf1, Bool.false_or] at htc; exact htc
            have hb2c : arrayIndex m2 c < k2.size := by
              rw [hsz2]; exact arrayIndex_lt m2 c ht2
            have hcA2 : childAt m2 k2 c = k2[arrayIndex m2 c]'hb2c := by
              unfold childAt; rw [Array.getElem?_eq_getElem hb2c, Option.getD_some]
            rw [symmChild_eq m1 k1 m2 k2 c hsz1 hsz2, if_neg ht1, hcA2]
            exact ⟨hwfk2 _ (Array.getElem_mem hb2c),
                   fun j hj => Or.inr ⟨ht2, j, hj, rfl⟩⟩
        have hal' : ∀ c, c < 32 → testBit (m1 ||| m2) c = true →
            AlignedAt l1 c p1 (childAt (m1 ||| m2) (symmKids m1 k1 m2 k2 (m1 ||| m2) #[]) c) := by
          intro c hc htc
          rw [childAt_symmKids m1 k1 m2 k2 c hc htc]
          intro j hj
          rcases (hslot c hc htc).2 j hj with ⟨ht1, j', hj', h5⟩ | ⟨ht2, j', hj', h5⟩
          · obtain ⟨hch, hpf⟩ := hrout1 c hc ht1 j' hj'
            exact ⟨(chunk_eq_of_hi l1 hl0 h5).trans hch,
                   (prefixAbove_eq_of_hi l1 h5).trans hpf⟩
          · obtain ⟨hch, hpf⟩ := hrout2 c hc ht2 j' hj'
            exact ⟨(chunk_eq_of_hi l1 hl0 h5).trans hch,
                   (prefixAbove_eq_of_hi l1 h5).trans hpf⟩
        refine ⟨WF_finalize p1 l1 (m1 ||| m2) _ hl0 ?_ hal', ?_⟩
        · intro c hc htc
          rw [childAt_symmKids m1 k1 m2 k2 c hc htc]
          exact (hslot c hc htc).1
        · intro j hj
          rw [contains_finalize j p1 l1 (m1 ||| m2) _ hal'] at hj
          obtain ⟨htj, hcj⟩ := and_split hj
          rw [childAt_symmKids m1 k1 m2 k2 (chunk j l1) (chunk_lt j l1) htj] at hcj
          rcases (hslot (chunk j l1) (chunk_lt j l1) htj).2 j hcj with
            ⟨ht1, j', hj', h5⟩ | ⟨ht2, j', hj', h5⟩
          · refine Or.inl ⟨j', ?_, h5⟩
            rw [contains_bin]
            obtain ⟨hch, _⟩ := hrout1 (chunk j l1) (chunk_lt j l1) ht1 j' hj'
            rw [hch, ht1, Bool.true_and]
            exact hj'
          · refine Or.inr ⟨j', ?_, h5⟩
            rw [contains_bin]
            obtain ⟨hch, _⟩ := hrout2 (chunk j l1) (chunk_lt j l1) ht2 j' hj'
            rw [hch, ht2, Bool.true_and]
            exact hj'
      · by_cases hcond2 : (l1 == l2) = true
        · have hleq : l1 = l2 := by simpa using hcond2
          subst hleq
          rw [symmDiffU, if_neg hcond1, if_pos hcond2]
          have hpne : p1 ≠ p2 := by
            intro h; apply hcond1
            rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]; exact ⟨rfl, h⟩
          have hl0 : 0 < l1 := by rw [WF] at hwa; exact hwa.1
          have hm1ne : m1 ≠ 0 := by
            rw [WF] at hwa; obtain ⟨_, _, hpc, _, _, _⟩ := hwa
            intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
          have hm2ne : m2 ≠ 0 := by
            rw [WF] at hwb; obtain ⟨_, _, hpc, _, _, _⟩ := hwb
            intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
          have hsk1 : prefixAbove (someKey (.bin p1 l1 m1 k1)) l1 = p1 :=
            someKey_bin_prefixAbove p1 l1 m1 k1 hm1ne
          have hsk2 : prefixAbove (someKey (.bin p2 l1 m2 k2)) l1 = p2 :=
            someKey_bin_prefixAbove p2 l1 m2 k2 hm2ne
          have hdiv : someKey (.bin p1 l1 m1 k1) >>> (5 * (l1 + 1))
              ≠ someKey (.bin p2 l1 m2 k2) >>> (5 * (l1 + 1)) := by
            show prefixAbove (someKey (.bin p1 l1 m1 k1)) l1
              ≠ prefixAbove (someKey (.bin p2 l1 m2 k2)) l1
            rw [hsk1, hsk2]; exact hpne
          have hkne : someKey (.bin p1 l1 m1 k1) ≠ someKey (.bin p2 l1 m2 k2) :=
            fun h => hdiv (by rw [h])
          have hbl_lt : l1 < branchLevel (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l1 m2 k2)) :=
            lt_branchLevel _ _ l1 hdiv
          have hl0' : 0 < branchLevel (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l1 m2 k2)) :=
            Nat.lt_trans hl0 hbl_lt
          obtain ⟨jwf, jkeys⟩ := join_WF_keys (someKey (.bin p1 l1 m1 k1))
            (someKey (.bin p2 l1 m2 k2)) (.bin p1 l1 m1 k1) (.bin p2 l1 m2 k2) hkne hl0'
            (aligned_bin p1 l1 m1 k1 hwa _ hbl_lt)
            (by rw [prefixAbove_branchLevel_eq (someKey (.bin p1 l1 m1 k1))
                  (someKey (.bin p2 l1 m2 k2))]
                exact aligned_bin p2 l1 m2 k2 hwb _ hbl_lt)
            hwa hwb (by simp) (by simp)
          refine ⟨jwf, fun j hj => ?_⟩
          rcases jkeys j hj with hA | hB
          · exact Or.inl ⟨j, hA, rfl⟩
          · exact Or.inr ⟨j, hB, rfl⟩
        · by_cases hlt : l2 < l1
          · have hbl0 : 0 < l1 := by rw [WF] at hwa; exact hwa.1
            by_cases hpfx : (prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 == p1) = true
            · have hpfxeq : prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 = p1 := by
                simpa using hpfx
              have halign : AlignedAt l1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) p1
                  (.bin p2 l2 m2 k2) :=
                by rw [← hpfxeq]; exact aligned_bin p2 l2 m2 k2 hwb l1 hlt
              by_cases htb : testBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) = true
              · by_cases h : arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) < k1.size
                · rw [symmDiffU, if_neg hcond1, if_neg hcond2, if_pos hlt, if_pos hpfx,
                      if_pos htb, dif_pos h]
                  have hwfchild :
                      WF (k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h) := by
                    rw [WF] at hwa; exact hwa.2.2.2.1 _ (Array.getElem_mem h)
                  obtain ⟨ihwf, ihkeys⟩ :=
                    symmDiff_WF_keys (k1[arrayIndex m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)]'h)
                      (.bin p2 l2 m2 k2) hwfchild hwb
                  exact splice2_WF_keys p1 l1 m1 k1 (chunk (someKey (.bin p2 l2 m2 k2)) l1)
                    (chunk_lt _ _) htb h _ (.bin p2 l2 m2 k2) hwa ihwf halign ihkeys
                · rw [symmDiffU, if_neg hcond1, if_neg hcond2, if_pos hlt, if_pos hpfx,
                      if_pos htb, dif_neg h]
                  exact ⟨hwa, fun j hj => Or.inl ⟨j, hj, rfl⟩⟩
              · rw [symmDiffU, if_neg hcond1, if_neg hcond2, if_pos hlt, if_pos hpfx, if_neg htb]
                have htbf : testBit m1 (chunk (someKey (.bin p2 l2 m2 k2)) l1) = false := by
                  simpa using htb
                refine ⟨WF_splice (.bin p2 l2 m2 k2) p1 l1 m1 k1
                  (chunk (someKey (.bin p2 l2 m2 k2)) l1) (chunk_lt _ _) hwa halign hwb
                  (by simp) htbf, ?_⟩
                intro j hj
                rw [contains_splice j (.bin p2 l2 m2 k2) p1 l1 m1 k1
                    (chunk (someKey (.bin p2 l2 m2 k2)) l1) (chunk_lt _ _) hwa halign htbf,
                    Bool.or_eq_true] at hj
                rcases hj with hj2 | hj1
                · exact Or.inr ⟨j, hj2, rfl⟩
                · exact Or.inl ⟨j, hj1, rfl⟩
            · rw [symmDiffU, if_neg hcond1, if_neg hcond2, if_pos hlt, if_neg hpfx]
              have hm1ne : m1 ≠ 0 := by
                rw [WF] at hwa; obtain ⟨_, _, hpc, _, _, _⟩ := hwa
                intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
              have hsk1 : prefixAbove (someKey (.bin p1 l1 m1 k1)) l1 = p1 :=
                someKey_bin_prefixAbove p1 l1 m1 k1 hm1ne
              have hpfxne : prefixAbove (someKey (.bin p2 l2 m2 k2)) l1 ≠ p1 := by
                intro h; exact hpfx (by rw [h]; exact beq_self_eq_true p1)
              have hdiv : someKey (.bin p1 l1 m1 k1) >>> (5 * (l1 + 1))
                  ≠ someKey (.bin p2 l2 m2 k2) >>> (5 * (l1 + 1)) := by
                show prefixAbove (someKey (.bin p1 l1 m1 k1)) l1
                  ≠ prefixAbove (someKey (.bin p2 l2 m2 k2)) l1
                rw [hsk1]; exact fun h => hpfxne h.symm
              have hkne : someKey (.bin p1 l1 m1 k1) ≠ someKey (.bin p2 l2 m2 k2) :=
                fun h => hdiv (by rw [h])
              have hbl_lt :
                  l1 < branchLevel (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l2 m2 k2)) :=
                lt_branchLevel _ _ l1 hdiv
              have hl0' :
                  0 < branchLevel (someKey (.bin p1 l1 m1 k1)) (someKey (.bin p2 l2 m2 k2)) :=
                Nat.lt_trans hbl0 hbl_lt
              obtain ⟨jwf, jkeys⟩ := join_WF_keys (someKey (.bin p1 l1 m1 k1))
                (someKey (.bin p2 l2 m2 k2)) (.bin p1 l1 m1 k1) (.bin p2 l2 m2 k2) hkne hl0'
                (aligned_bin p1 l1 m1 k1 hwa _ hbl_lt)
                (by rw [prefixAbove_branchLevel_eq (someKey (.bin p1 l1 m1 k1))
                      (someKey (.bin p2 l2 m2 k2))]
                    exact aligned_bin p2 l2 m2 k2 hwb _ (Nat.lt_trans hlt hbl_lt))
                hwa hwb (by simp) (by simp)
              refine ⟨jwf, fun j hj => ?_⟩
              rcases jkeys j hj with hA | hB
              · exact Or.inl ⟨j, hA, rfl⟩
              · exact Or.inr ⟨j, hB, rfl⟩
          · have hl12 : l1 < l2 := by
              have hne12 : l1 ≠ l2 := by simpa using hcond2
              omega
            have hbl0 : 0 < l2 := by rw [WF] at hwb; exact hwb.1
            by_cases hpfx : (prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 == p2) = true
            · have hpfxeq : prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 = p2 := by
                simpa using hpfx
              have halign : AlignedAt l2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) p2
                  (.bin p1 l1 m1 k1) :=
                by rw [← hpfxeq]; exact aligned_bin p1 l1 m1 k1 hwa l2 hl12
              by_cases htb : testBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) = true
              · by_cases h : arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) < k2.size
                · rw [symmDiffU, if_neg hcond1, if_neg hcond2, if_neg hlt, if_pos hpfx,
                      if_pos htb, dif_pos h]
                  have hwfchild :
                      WF (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h) := by
                    rw [WF] at hwb; exact hwb.2.2.2.1 _ (Array.getElem_mem h)
                  obtain ⟨ihwf, ihkeys⟩ :=
                    symmDiff_WF_keys (.bin p1 l1 m1 k1)
                      (k2[arrayIndex m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2)]'h) hwa hwfchild
                  obtain ⟨swf, skeys⟩ := splice2_WF_keys p2 l2 m2 k2
                    (chunk (someKey (.bin p1 l1 m1 k1)) l2) (chunk_lt _ _) htb h _
                    (.bin p1 l1 m1 k1) hwb ihwf halign
                    (fun j hj => (ihkeys j hj).elim Or.inr Or.inl)
                  exact ⟨swf, fun j hj => (skeys j hj).elim Or.inr Or.inl⟩
                · rw [symmDiffU, if_neg hcond1, if_neg hcond2, if_neg hlt, if_pos hpfx,
                      if_pos htb, dif_neg h]
                  exact ⟨hwb, fun j hj => Or.inr ⟨j, hj, rfl⟩⟩
              · rw [symmDiffU, if_neg hcond1, if_neg hcond2, if_neg hlt, if_pos hpfx, if_neg htb]
                have htbf : testBit m2 (chunk (someKey (.bin p1 l1 m1 k1)) l2) = false := by
                  simpa using htb
                refine ⟨WF_splice (.bin p1 l1 m1 k1) p2 l2 m2 k2
                  (chunk (someKey (.bin p1 l1 m1 k1)) l2) (chunk_lt _ _) hwb halign hwa
                  (by simp) htbf, ?_⟩
                intro j hj
                rw [contains_splice j (.bin p1 l1 m1 k1) p2 l2 m2 k2
                    (chunk (someKey (.bin p1 l1 m1 k1)) l2) (chunk_lt _ _) hwb halign htbf,
                    Bool.or_eq_true] at hj
                rcases hj with hj1 | hj2
                · exact Or.inl ⟨j, hj1, rfl⟩
                · exact Or.inr ⟨j, hj2, rfl⟩
            · rw [symmDiffU, if_neg hcond1, if_neg hcond2, if_neg hlt, if_neg hpfx]
              have hm2ne : m2 ≠ 0 := by
                rw [WF] at hwb; obtain ⟨_, _, hpc, _, _, _⟩ := hwb
                intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
              have hsk2 : prefixAbove (someKey (.bin p2 l2 m2 k2)) l2 = p2 :=
                someKey_bin_prefixAbove p2 l2 m2 k2 hm2ne
              have hpfxne : prefixAbove (someKey (.bin p1 l1 m1 k1)) l2 ≠ p2 := by
                intro h; exact hpfx (by rw [h]; exact beq_self_eq_true p2)
              have hdiv : someKey (.bin p2 l2 m2 k2) >>> (5 * (l2 + 1))
                  ≠ someKey (.bin p1 l1 m1 k1) >>> (5 * (l2 + 1)) := by
                show prefixAbove (someKey (.bin p2 l2 m2 k2)) l2
                  ≠ prefixAbove (someKey (.bin p1 l1 m1 k1)) l2
                rw [hsk2]; exact fun h => hpfxne h.symm
              have hkne : someKey (.bin p2 l2 m2 k2) ≠ someKey (.bin p1 l1 m1 k1) :=
                fun h => hdiv (by rw [h])
              have hbl_lt :
                  l2 < branchLevel (someKey (.bin p2 l2 m2 k2)) (someKey (.bin p1 l1 m1 k1)) :=
                lt_branchLevel _ _ l2 hdiv
              have hl0' :
                  0 < branchLevel (someKey (.bin p2 l2 m2 k2)) (someKey (.bin p1 l1 m1 k1)) :=
                Nat.lt_trans hbl0 hbl_lt
              obtain ⟨jwf, jkeys⟩ := join_WF_keys (someKey (.bin p2 l2 m2 k2))
                (someKey (.bin p1 l1 m1 k1)) (.bin p2 l2 m2 k2) (.bin p1 l1 m1 k1) hkne hl0'
                (aligned_bin p2 l2 m2 k2 hwb _ hbl_lt)
                (by rw [prefixAbove_branchLevel_eq (someKey (.bin p2 l2 m2 k2))
                      (someKey (.bin p1 l1 m1 k1))]
                    exact aligned_bin p1 l1 m1 k1 hwa _ (Nat.lt_trans hl12 hbl_lt))
                hwb hwa (by simp) (by simp)
              refine ⟨jwf, fun j hj => ?_⟩
              rcases jkeys j hj with hB | hA
              · exact Or.inr ⟨j, hB, rfl⟩
              · exact Or.inl ⟨j, hA, rfl⟩
termination_by a b => sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := Array.sizeOf_lt_of_mem (Array.getElem_mem h); omega)
    | (have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb1c)
       have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb2c); omega)
    | omega

/-- `symmDiff` preserves canonical shape. -/
theorem WF_symmDiff (a b : PTree L) (hwa : WF a) (hwb : WF b) : WF (symmDiff a b) := by
  rw [symmDiff]; exact (symmDiff_WF_keys a b hwa hwb).1

/-! ### Range restriction

`filterLtU`/`filterGEU` only remove keys, so their `WF` proofs are `filter_WF_keys` verbatim with
a slot-interval `hslot`: below-the-bound children are originals (identity provenance), the routed
slot recurses, above-the-bound children are `nil` (vacuous). -/

/-- `ltKids`' fold invariant — the verbatim `filterKids_spec` shape. -/
private theorem ltKids_spec (k : Nat) (level : Nat) (mask : UInt32) (kids : Array (PTree L)) :
    ∀ (n : Nat) (rem : UInt32), rem.toNat = n → ∀ (acc : Array (PTree L)),
      (ltKids k level mask kids rem acc).size = acc.size + popCount rem
      ∧ (∀ i, i < acc.size → (ltKids k level mask kids rem acc)[i]? = acc[i]?)
      ∧ (∀ c, c < 32 → testBit rem c = true →
           (ltKids k level mask kids rem acc)[acc.size + arrayIndex rem c]?
             = some (ltChild k level mask kids c)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro rem hrem acc
    by_cases h0 : (rem == 0) = true
    · have hr0 : rem = 0 := by simpa using h0
      rw [ltKids, dif_pos h0]
      refine ⟨?_, ?_, ?_⟩
      · rw [hr0, show popCount (0 : UInt32) = 0 from rfl, Nat.add_zero]
      · intro i hi; rfl
      · intro c hc htb; rw [hr0, testBit_zero] at htb; exact absurd htb (by decide)
    · have hrem0 : rem ≠ 0 := by intro h; exact h0 (by rw [h]; rfl)
      have hstep : ltKids k level mask kids rem acc
          = ltKids k level mask kids (clearLowest rem)
              (acc.push (ltChild k level mask kids (lowestSetIdx rem))) := by
        rw [ltKids, dif_neg h0]
      have hlt : (clearLowest rem).toNat < n := by
        rw [← hrem]; exact toNat_clearLowest_lt rem hrem0
      obtain ⟨ihsize, ihpref, ihthird⟩ :=
        IH (clearLowest rem).toNat hlt (clearLowest rem) rfl
          (acc.push (ltChild k level mask kids (lowestSetIdx rem)))
      have hpc : popCount (clearLowest rem) + 1 = popCount rem := popCount_clearLowest rem hrem0
      have haccsz : (acc.push (ltChild k level mask kids (lowestSetIdx rem))).size = acc.size + 1 :=
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

/-- Reading a present slot of the rebuilt child array recovers that slot's `ltChild`. -/
private theorem childAt_ltKids (k : Nat) (level : Nat) (mask : UInt32) (kids : Array (PTree L))
    (c : UInt32) (hc : c < 32) (htb : testBit mask c = true) :
    childAt mask (ltKids k level mask kids mask #[]) c = ltChild k level mask kids c := by
  obtain ⟨_, _, hthird⟩ := ltKids_spec k level mask kids mask.toNat mask rfl #[]
  have hc' := hthird c hc htb
  unfold childAt
  rw [show (#[] : Array (PTree L)).size = 0 from rfl, Nat.zero_add] at hc'
  rw [hc', Option.getD_some]

/-- `ltChild` reads as the slot-interval split on `childAt`. -/
private theorem ltChild_eq (k : Nat) (level : Nat) (mask : UInt32) (kids : Array (PTree L))
    (c : UInt32) :
    ltChild k level mask kids c
      = if c < chunk k level then childAt mask kids c
        else if c == chunk k level then filterLtU k (childAt mask kids c)
        else .nil := by
  rw [ltChild]
  by_cases hlt : c < chunk k level
  · rw [if_pos hlt, if_pos hlt]
    unfold childAt
    by_cases h : arrayIndex mask c < kids.size
    · rw [dif_pos h, Array.getElem?_eq_getElem h, Option.getD_some]
    · rw [dif_neg h, Array.getElem?_eq_none (Nat.le_of_not_lt h), Option.getD_none]
  · rw [if_neg hlt, if_neg hlt]
    by_cases heq : (c == chunk k level) = true
    · rw [if_pos heq, if_pos heq]
      unfold childAt
      by_cases h : arrayIndex mask c < kids.size
      · rw [dif_pos h, Array.getElem?_eq_getElem h, Option.getD_some]
      · rw [dif_neg h, Array.getElem?_eq_none (Nat.le_of_not_lt h), Option.getD_none, filterLtU]
    · rw [if_neg heq, if_neg heq]

/-- `geKids`' fold invariant — the verbatim `ltKids_spec` mirror. -/
private theorem geKids_spec (k : Nat) (level : Nat) (mask : UInt32) (kids : Array (PTree L)) :
    ∀ (n : Nat) (rem : UInt32), rem.toNat = n → ∀ (acc : Array (PTree L)),
      (geKids k level mask kids rem acc).size = acc.size + popCount rem
      ∧ (∀ i, i < acc.size → (geKids k level mask kids rem acc)[i]? = acc[i]?)
      ∧ (∀ c, c < 32 → testBit rem c = true →
           (geKids k level mask kids rem acc)[acc.size + arrayIndex rem c]?
             = some (geChild k level mask kids c)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro rem hrem acc
    by_cases h0 : (rem == 0) = true
    · have hr0 : rem = 0 := by simpa using h0
      rw [geKids, dif_pos h0]
      refine ⟨?_, ?_, ?_⟩
      · rw [hr0, show popCount (0 : UInt32) = 0 from rfl, Nat.add_zero]
      · intro i hi; rfl
      · intro c hc htb; rw [hr0, testBit_zero] at htb; exact absurd htb (by decide)
    · have hrem0 : rem ≠ 0 := by intro h; exact h0 (by rw [h]; rfl)
      have hstep : geKids k level mask kids rem acc
          = geKids k level mask kids (clearLowest rem)
              (acc.push (geChild k level mask kids (lowestSetIdx rem))) := by
        rw [geKids, dif_neg h0]
      have hlt : (clearLowest rem).toNat < n := by
        rw [← hrem]; exact toNat_clearLowest_lt rem hrem0
      obtain ⟨ihsize, ihpref, ihthird⟩ :=
        IH (clearLowest rem).toNat hlt (clearLowest rem) rfl
          (acc.push (geChild k level mask kids (lowestSetIdx rem)))
      have hpc : popCount (clearLowest rem) + 1 = popCount rem := popCount_clearLowest rem hrem0
      have haccsz : (acc.push (geChild k level mask kids (lowestSetIdx rem))).size = acc.size + 1 :=
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

/-- Reading a present slot of the rebuilt child array recovers that slot's `geChild`. -/
private theorem childAt_geKids (k : Nat) (level : Nat) (mask : UInt32) (kids : Array (PTree L))
    (c : UInt32) (hc : c < 32) (htb : testBit mask c = true) :
    childAt mask (geKids k level mask kids mask #[]) c = geChild k level mask kids c := by
  obtain ⟨_, _, hthird⟩ := geKids_spec k level mask kids mask.toNat mask rfl #[]
  have hc' := hthird c hc htb
  unfold childAt
  rw [show (#[] : Array (PTree L)).size = 0 from rfl, Nat.zero_add] at hc'
  rw [hc', Option.getD_some]

/-- `geChild` reads as the slot-interval split on `childAt`. -/
private theorem geChild_eq (k : Nat) (level : Nat) (mask : UInt32) (kids : Array (PTree L))
    (c : UInt32) :
    geChild k level mask kids c
      = if chunk k level < c then childAt mask kids c
        else if c == chunk k level then filterGEU k (childAt mask kids c)
        else .nil := by
  rw [geChild]
  by_cases hlt : chunk k level < c
  · rw [if_pos hlt, if_pos hlt]
    unfold childAt
    by_cases h : arrayIndex mask c < kids.size
    · rw [dif_pos h, Array.getElem?_eq_getElem h, Option.getD_some]
    · rw [dif_neg h, Array.getElem?_eq_none (Nat.le_of_not_lt h), Option.getD_none]
  · rw [if_neg hlt, if_neg hlt]
    by_cases heq : (c == chunk k level) = true
    · rw [if_pos heq, if_pos heq]
      unfold childAt
      by_cases h : arrayIndex mask c < kids.size
      · rw [dif_pos h, Array.getElem?_eq_getElem h, Option.getD_some]
      · rw [dif_neg h, Array.getElem?_eq_none (Nat.le_of_not_lt h), Option.getD_none, filterGEU]
    · rw [if_neg heq, if_neg heq]

/-- `filterLtU` preserves `WF`, and every surviving key shares its high bits with an original key.
`filter_WF_keys` with the slot-interval `hslot`. -/
private theorem filterLt_WF_keys (k : Nat) : (t : PTree L) → WF t →
    WF (filterLtU k t)
      ∧ ∀ j, contains j (filterLtU k t) = true → ∃ j', contains j' t = true ∧ j >>> 5 = j' >>> 5
  | .nil => fun _ => by
      rw [filterLtU]
      exact ⟨by rw [WF]; trivial,
             fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
  | .tip pfx leaf => fun hwf => by
      rw [filterLtU]
      by_cases h1 : k >>> 5 < pfx
      · rw [if_pos h1]
        exact ⟨by rw [WF]; trivial,
               fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
      · rw [if_neg h1]
        by_cases h2 : pfx < k >>> 5
        · rw [if_pos h2]
          exact ⟨hwf, fun j hj => ⟨j, hj, rfl⟩⟩
        · rw [if_neg h2]
          by_cases he : LeafOps.isEmpty
              (LeafOps.filter (fun s _ => decide (s < chunk k 0)) leaf) = true
          · rw [if_pos he]
            exact ⟨by rw [WF]; trivial,
                   fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
          · rw [if_neg he]
            refine ⟨by rw [WF]; simpa using he, ?_⟩
            intro j hj
            obtain ⟨j', hj'⟩ := exists_mem (.tip pfx leaf) hwf (by simp)
            exact ⟨j', hj', (hi_eq_of_contains_tip hj).trans (hi_eq_of_contains_tip hj').symm⟩
  | .bin pfx level mask kids => fun hwf => by
      rw [filterLtU]
      by_cases h1 : prefixAbove k level < pfx
      · rw [if_pos h1]
        exact ⟨by rw [WF]; trivial,
               fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
      · rw [if_neg h1]
        by_cases h2 : pfx < prefixAbove k level
        · rw [if_pos h2]
          exact ⟨hwf, fun j hj => ⟨j, hj, rfl⟩⟩
        · rw [if_neg h2, Array.emptyWithCapacity_eq]
          have hwf' := hwf
          rw [WF] at hwf'
          obtain ⟨hl, hsz, _, hwfk, _, hal⟩ := hwf'
          have hslot : ∀ c, c < 32 → testBit mask c = true →
              WF (ltChild k level mask kids c)
              ∧ ∀ j, contains j (ltChild k level mask kids c) = true →
                  ∃ j', contains j' (childAt mask kids c) = true ∧ j >>> 5 = j' >>> 5 := by
            intro c hc htc
            have hbc : arrayIndex mask c < kids.size := by
              rw [hsz]; exact arrayIndex_lt mask c htc
            have hcA : childAt mask kids c = kids[arrayIndex mask c]'hbc := by
              unfold childAt; rw [Array.getElem?_eq_getElem hbc, Option.getD_some]
            rw [ltChild_eq]
            by_cases hclt : c < chunk k level
            · rw [if_pos hclt, hcA]
              exact ⟨hwfk _ (Array.getElem_mem hbc), fun j hj => ⟨j, hj, rfl⟩⟩
            · rw [if_neg hclt]
              by_cases hceq : (c == chunk k level) = true
              · rw [if_pos hceq, hcA]
                exact filterLt_WF_keys k (kids[arrayIndex mask c]'hbc)
                  (hwfk _ (Array.getElem_mem hbc))
              · rw [if_neg hceq]
                exact ⟨by rw [WF]; trivial,
                       fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
          have hal' : ∀ c, c < 32 → testBit mask c = true →
              AlignedAt level c pfx (childAt mask (ltKids k level mask kids mask #[]) c) := by
            intro c hc htc
            rw [childAt_ltKids k level mask kids c hc htc]
            intro j hj
            obtain ⟨j', hj', h5⟩ := (hslot c hc htc).2 j hj
            obtain ⟨hch, hpf⟩ := hal c hc htc j' hj'
            exact ⟨(chunk_eq_of_hi level hl h5).trans hch,
                   (prefixAbove_eq_of_hi level h5).trans hpf⟩
          refine ⟨WF_finalize pfx level mask _ hl ?_ hal', ?_⟩
          · intro c hc htc
            rw [childAt_ltKids k level mask kids c hc htc]
            exact (hslot c hc htc).1
          · intro j hj
            rw [contains_finalize j pfx level mask _ hal'] at hj
            obtain ⟨htj, hcj⟩ := and_split hj
            rw [childAt_ltKids k level mask kids (chunk j level) (chunk_lt j level) htj] at hcj
            obtain ⟨j', hj', h5⟩ := (hslot (chunk j level) (chunk_lt j level) htj).2 j hcj
            refine ⟨j', ?_, h5⟩
            rw [contains_bin]
            obtain ⟨hch, _⟩ := hal (chunk j level) (chunk_lt j level) htj j' hj'
            rw [hch, htj, Bool.true_and]
            exact hj'
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hbc); omega

/-- `filterGEU` preserves `WF`, and every surviving key shares its high bits with an original
key — the mirror of `filterLt_WF_keys`. -/
private theorem filterGE_WF_keys (k : Nat) : (t : PTree L) → WF t →
    WF (filterGEU k t)
      ∧ ∀ j, contains j (filterGEU k t) = true → ∃ j', contains j' t = true ∧ j >>> 5 = j' >>> 5
  | .nil => fun _ => by
      rw [filterGEU]
      exact ⟨by rw [WF]; trivial,
             fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
  | .tip pfx leaf => fun hwf => by
      rw [filterGEU]
      by_cases h1 : k >>> 5 < pfx
      · rw [if_pos h1]
        exact ⟨hwf, fun j hj => ⟨j, hj, rfl⟩⟩
      · rw [if_neg h1]
        by_cases h2 : pfx < k >>> 5
        · rw [if_pos h2]
          exact ⟨by rw [WF]; trivial,
                 fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
        · rw [if_neg h2]
          by_cases he : LeafOps.isEmpty
              (LeafOps.filter (fun s _ => decide (chunk k 0 ≤ s)) leaf) = true
          · rw [if_pos he]
            exact ⟨by rw [WF]; trivial,
                   fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
          · rw [if_neg he]
            refine ⟨by rw [WF]; simpa using he, ?_⟩
            intro j hj
            obtain ⟨j', hj'⟩ := exists_mem (.tip pfx leaf) hwf (by simp)
            exact ⟨j', hj', (hi_eq_of_contains_tip hj).trans (hi_eq_of_contains_tip hj').symm⟩
  | .bin pfx level mask kids => fun hwf => by
      rw [filterGEU]
      by_cases h1 : prefixAbove k level < pfx
      · rw [if_pos h1]
        exact ⟨hwf, fun j hj => ⟨j, hj, rfl⟩⟩
      · rw [if_neg h1]
        by_cases h2 : pfx < prefixAbove k level
        · rw [if_pos h2]
          exact ⟨by rw [WF]; trivial,
                 fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
        · rw [if_neg h2, Array.emptyWithCapacity_eq]
          have hwf' := hwf
          rw [WF] at hwf'
          obtain ⟨hl, hsz, _, hwfk, _, hal⟩ := hwf'
          have hslot : ∀ c, c < 32 → testBit mask c = true →
              WF (geChild k level mask kids c)
              ∧ ∀ j, contains j (geChild k level mask kids c) = true →
                  ∃ j', contains j' (childAt mask kids c) = true ∧ j >>> 5 = j' >>> 5 := by
            intro c hc htc
            have hbc : arrayIndex mask c < kids.size := by
              rw [hsz]; exact arrayIndex_lt mask c htc
            have hcA : childAt mask kids c = kids[arrayIndex mask c]'hbc := by
              unfold childAt; rw [Array.getElem?_eq_getElem hbc, Option.getD_some]
            rw [geChild_eq]
            by_cases hclt : chunk k level < c
            · rw [if_pos hclt, hcA]
              exact ⟨hwfk _ (Array.getElem_mem hbc), fun j hj => ⟨j, hj, rfl⟩⟩
            · rw [if_neg hclt]
              by_cases hceq : (c == chunk k level) = true
              · rw [if_pos hceq, hcA]
                exact filterGE_WF_keys k (kids[arrayIndex mask c]'hbc)
                  (hwfk _ (Array.getElem_mem hbc))
              · rw [if_neg hceq]
                exact ⟨by rw [WF]; trivial,
                       fun j hj => by rw [contains_nil] at hj; exact absurd hj (by decide)⟩
          have hal' : ∀ c, c < 32 → testBit mask c = true →
              AlignedAt level c pfx (childAt mask (geKids k level mask kids mask #[]) c) := by
            intro c hc htc
            rw [childAt_geKids k level mask kids c hc htc]
            intro j hj
            obtain ⟨j', hj', h5⟩ := (hslot c hc htc).2 j hj
            obtain ⟨hch, hpf⟩ := hal c hc htc j' hj'
            exact ⟨(chunk_eq_of_hi level hl h5).trans hch,
                   (prefixAbove_eq_of_hi level h5).trans hpf⟩
          refine ⟨WF_finalize pfx level mask _ hl ?_ hal', ?_⟩
          · intro c hc htc
            rw [childAt_geKids k level mask kids c hc htc]
            exact (hslot c hc htc).1
          · intro j hj
            rw [contains_finalize j pfx level mask _ hal'] at hj
            obtain ⟨htj, hcj⟩ := and_split hj
            rw [childAt_geKids k level mask kids (chunk j level) (chunk_lt j level) htj] at hcj
            obtain ⟨j', hj', h5⟩ := (hslot (chunk j level) (chunk_lt j level) htj).2 j hcj
            refine ⟨j', ?_, h5⟩
            rw [contains_bin]
            obtain ⟨hch, _⟩ := hal (chunk j level) (chunk_lt j level) htj j' hj'
            rw [hch, htj, Bool.true_and]
            exact hj'
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hbc); omega

/-- `filterLt` preserves canonical shape. -/
theorem WF_filterLt (k : Nat) (t : PTree L) (hwf : WF t) : WF (filterLt k t) := by
  rw [filterLt]; exact (filterLt_WF_keys k t hwf).1

/-- `filterGE` preserves canonical shape. -/
theorem WF_filterGE (k : Nat) (t : PTree L) (hwf : WF t) : WF (filterGE k t) := by
  rw [filterGE]; exact (filterGE_WF_keys k t hwf).1

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
  have hclt : c.toNat < 32 := UInt32.lt_iff_toNat_lt.mp hc
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
private theorem get?_singleton (j k : Nat) (v : V) :
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
private theorem get?_join (j p l : Nat) (ca cb : UInt32) (a b : PTree L)
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
private theorem get?_join_eq (j ka kb : Nat) (a b : PTree L) (hne : ka ≠ kb)
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
private theorem get?_unionU (cf : V → V → V) (j : Nat) : ∀ (a b : PTree L), WF a → WF b →
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
    rw [unionU, if_pos heq, Array.emptyWithCapacity_eq, get?_bin, get?_bin, get?_bin]
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
private theorem get?_finalize (j : Nat) (p l : Nat) (mask : UInt32) (kids : Array (PTree L))
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
private theorem get?_meetU (cf : V → V → V) (j : Nat) : ∀ (a b : PTree L), WF a → WF b →
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
    rw [meetU, if_pos heq, if_pos hpfx, Array.emptyWithCapacity_eq, get?_finalize j p1 l1 (m1 &&& m2) _ halign]
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

/-- The `meet` value-step lies below its left input (when the combine does, `rel (cf x y) x`). -/
private theorem optRel_optVmeet_left (rel : V → V → Bool) (cf : V → V → V)
    (hmle : ∀ x y, rel (cf x y) x = true) (oa ob : Option V) :
    optRel rel (optVmeet cf oa ob) oa = true := by
  cases oa with
  | none => cases ob <;> rfl
  | some x => cases ob with
    | none => rfl
    | some y => exact hmle x y

/-- The `meet` value-step lies below its right input (when the combine does, `rel (cf x y) y`). -/
private theorem optRel_optVmeet_right (rel : V → V → Bool) (cf : V → V → V)
    (hmre : ∀ x y, rel (cf x y) y = true) (oa ob : Option V) :
    optRel rel (optVmeet cf oa ob) ob = true := by
  cases ob with
  | none => cases oa <;> rfl
  | some y => cases oa with
    | none => rfl
    | some x => exact hmre x y

/-- Any common lower bound `oc` lies below the `meet` value-step (the greatest-lower-bound step). -/
private theorem optRel_optVmeet_glb (rel : V → V → Bool) (cf : V → V → V)
    (hglb : ∀ z x y, rel z x = true → rel z y = true → rel z (cf x y) = true)
    (oa ob oc : Option V) (h1 : optRel rel oc oa = true) (h2 : optRel rel oc ob = true) :
    optRel rel oc (optVmeet cf oa ob) = true := by
  cases oc with
  | none => rfl
  | some z => cases oa with
    | none => simp [optRel] at h1
    | some x => cases ob with
      | none => simp [optRel] at h2
      | some y => simp only [optVmeet, optRel] at h1 h2 ⊢; exact hglb z x y h1 h2

/-- The left input lies below the `union` value-step (when the combine does, `rel x (cf x y)`). -/
private theorem optRel_optVjoin_left (rel : V → V → Bool) (cf : V → V → V)
    (hrefl : ∀ x, rel x x = true) (hjle : ∀ x y, rel x (cf x y) = true) (oa ob : Option V) :
    optRel rel oa (optVjoin cf oa ob) = true := by
  cases oa with
  | none => rfl
  | some x => cases ob with
    | none => exact hrefl x
    | some y => exact hjle x y

/-- The right input lies below the `union` value-step (when the combine does, `rel y (cf x y)`). -/
private theorem optRel_optVjoin_right (rel : V → V → Bool) (cf : V → V → V)
    (hrefl : ∀ x, rel x x = true) (hjre : ∀ x y, rel y (cf x y) = true) (oa ob : Option V) :
    optRel rel ob (optVjoin cf oa ob) = true := by
  cases ob with
  | none => rfl
  | some y => cases oa with
    | none => exact hrefl y
    | some x => exact hjre x y

/-- The `union` value-step lies below any common upper bound `oc` (the least-upper-bound step). -/
private theorem optRel_optVjoin_lub (rel : V → V → Bool) (cf : V → V → V)
    (hjlub : ∀ x y z, rel x z = true → rel y z = true → rel (cf x y) z = true)
    (oa ob oc : Option V) (h1 : optRel rel oa oc = true) (h2 : optRel rel ob oc = true) :
    optRel rel (optVjoin cf oa ob) oc = true := by
  cases oa with
  | none => cases ob with
    | none => rfl
    | some y => exact h2
  | some x => cases ob with
    | none => exact h1
    | some y => cases oc with
      | none => simp [optRel] at h1
      | some z => simp only [optVjoin, optRel] at h1 h2 ⊢; exact hjlub x y z h1 h2

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

private theorem optVjoin_assoc (cf : V → V → V) (hassoc : ∀ x y z, cf (cf x y) z = cf x (cf y z))
    (oa ob oc : Option V) :
    optVjoin cf (optVjoin cf oa ob) oc = optVjoin cf oa (optVjoin cf ob oc) := by
  cases oa <;> cases ob <;> cases oc <;> simp only [optVjoin] <;> first | rfl | rw [hassoc]

/-- `union` is associative when its combine is. -/
theorem union_assoc (cf : V → V → V) (hassoc : ∀ x y z, cf (cf x y) z = cf x (cf y z))
    (a b c : PTree L) (hwa : WF a) (hwb : WF b) (hwc : WF c) :
    union cf (union cf a b) c = union cf a (union cf b c) :=
  ext_get? _ _ (WF_union cf (union cf a b) c (WF_union cf a b hwa hwb) hwc)
    (WF_union cf a (union cf b c) hwa (WF_union cf b c hwb hwc)) (fun j => by
      rw [get?_union cf j (union cf a b) c (WF_union cf a b hwa hwb) hwc,
          get?_union cf j a (union cf b c) hwa (WF_union cf b c hwb hwc),
          get?_union cf j a b hwa hwb, get?_union cf j b c hwb hwc, optVjoin_assoc cf hassoc])

/-- `meet` is associative when its combine is. -/
theorem meet_assoc (cf : V → V → V) (hassoc : ∀ x y z, cf (cf x y) z = cf x (cf y z))
    (a b c : PTree L) (hwa : WF a) (hwb : WF b) (hwc : WF c) :
    meet cf (meet cf a b) c = meet cf a (meet cf b c) :=
  ext_get? _ _ (WF_meet cf (meet cf a b) c (WF_meet cf a b hwa hwb) hwc)
    (WF_meet cf a (meet cf b c) hwa (WF_meet cf b c hwb hwc)) (fun j => by
      rw [get?_meet cf j (meet cf a b) c (WF_meet cf a b hwa hwb) hwc,
          get?_meet cf j a (meet cf b c) hwa (WF_meet cf b c hwb hwc),
          get?_meet cf j a b hwa hwb, get?_meet cf j b c hwb hwc, optVmeet_assoc cf hassoc])

/-- `meet` distributes over `union` from the left (when the meet combine distributes over the join
combine pointwise). -/
theorem meet_union_distrib (cm cj : V → V → V)
    (hdist : ∀ x y z, cm x (cj y z) = cj (cm x y) (cm x z))
    (a b c : PTree L) (hwa : WF a) (hwb : WF b) (hwc : WF c) :
    meet cm a (union cj b c) = union cj (meet cm a b) (meet cm a c) :=
  ext_get? _ _ (WF_meet cm a (union cj b c) hwa (WF_union cj b c hwb hwc))
    (WF_union cj (meet cm a b) (meet cm a c) (WF_meet cm a b hwa hwb) (WF_meet cm a c hwa hwc))
    (fun j => by
      rw [get?_meet cm j a (union cj b c) hwa (WF_union cj b c hwb hwc),
          get?_union cj j b c hwb hwc,
          get?_union cj j (meet cm a b) (meet cm a c) (WF_meet cm a b hwa hwb) (WF_meet cm a c hwa hwc),
          get?_meet cm j a b hwa hwb, get?_meet cm j a c hwa hwc,
          optVmeet_optVjoin_distrib cm cj hdist])

/-- `union` distributes over `meet` from the left (given the full lattice algebra on the combines). -/
theorem union_meet_distrib (cj cm : V → V → V) (hidem : ∀ x, cm x x = x)
    (habs1 : ∀ x y, cm (cj x y) x = x) (habs2 : ∀ x y, cm x (cj x y) = x)
    (hdist : ∀ x y z, cj x (cm y z) = cm (cj x y) (cj x z))
    (a b c : PTree L) (hwa : WF a) (hwb : WF b) (hwc : WF c) :
    union cj a (meet cm b c) = meet cm (union cj a b) (union cj a c) :=
  ext_get? _ _ (WF_union cj a (meet cm b c) hwa (WF_meet cm b c hwb hwc))
    (WF_meet cm (union cj a b) (union cj a c) (WF_union cj a b hwa hwb) (WF_union cj a c hwa hwc))
    (fun j => by
      rw [get?_union cj j a (meet cm b c) hwa (WF_meet cm b c hwb hwc),
          get?_meet cm j b c hwb hwc,
          get?_meet cm j (union cj a b) (union cj a c) (WF_union cj a b hwa hwb) (WF_union cj a c hwa hwc),
          get?_union cj j a b hwa hwb, get?_union cj j a c hwa hwc,
          optVjoin_optVmeet_distrib cj cm hidem habs1 habs2 hdist])

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

/-- `meet` is a lower bound of its left input (greatest-lower-bound part 1). -/
theorem meet_subset_left (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (cf : V → V → V)
    (hmle : ∀ x y, rel (cf x y) x = true) (a b : PTree L) (hwa : WF a) (hwb : WF b) :
    subset rel (meet cf a b) a = true :=
  (subset_iff_eq rel hrefl (meet cf a b) a (WF_meet cf a b hwa hwb) hwa).mpr (fun k => by
    rw [get?_meet cf k a b hwa hwb]
    exact optRel_optVmeet_left rel cf hmle (get? k a) (get? k b))

/-- `meet` is a lower bound of its right input (greatest-lower-bound part 2). -/
theorem meet_subset_right (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (cf : V → V → V)
    (hmre : ∀ x y, rel (cf x y) y = true) (a b : PTree L) (hwa : WF a) (hwb : WF b) :
    subset rel (meet cf a b) b = true :=
  (subset_iff_eq rel hrefl (meet cf a b) b (WF_meet cf a b hwa hwb) hwb).mpr (fun k => by
    rw [get?_meet cf k a b hwa hwb]
    exact optRel_optVmeet_right rel cf hmre (get? k a) (get? k b))

/-- Any common lower bound of `a` and `b` is below their `meet` (greatest-lower-bound universal). -/
theorem subset_meet (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (cf : V → V → V)
    (hglb : ∀ z x y, rel z x = true → rel z y = true → rel z (cf x y) = true)
    (a b c : PTree L) (hwa : WF a) (hwb : WF b) (hwc : WF c)
    (hca : subset rel c a = true) (hcb : subset rel c b = true) :
    subset rel c (meet cf a b) = true :=
  (subset_iff_eq rel hrefl c (meet cf a b) hwc (WF_meet cf a b hwa hwb)).mpr (fun k => by
    rw [get?_meet cf k a b hwa hwb]
    exact optRel_optVmeet_glb rel cf hglb (get? k a) (get? k b) (get? k c)
      ((subset_iff_eq rel hrefl c a hwc hwa).mp hca k)
      ((subset_iff_eq rel hrefl c b hwc hwb).mp hcb k))

/-- `union` is an upper bound of its left input (least-upper-bound part 1). -/
theorem subset_union_left (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (cf : V → V → V)
    (hjle : ∀ x y, rel x (cf x y) = true) (a b : PTree L) (hwa : WF a) (hwb : WF b) :
    subset rel a (union cf a b) = true :=
  (subset_iff_eq rel hrefl a (union cf a b) hwa (WF_union cf a b hwa hwb)).mpr (fun k => by
    rw [get?_union cf k a b hwa hwb]
    exact optRel_optVjoin_left rel cf hrefl hjle (get? k a) (get? k b))

/-- `union` is an upper bound of its right input (least-upper-bound part 2). -/
theorem subset_union_right (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (cf : V → V → V)
    (hjre : ∀ x y, rel y (cf x y) = true) (a b : PTree L) (hwa : WF a) (hwb : WF b) :
    subset rel b (union cf a b) = true :=
  (subset_iff_eq rel hrefl b (union cf a b) hwb (WF_union cf a b hwa hwb)).mpr (fun k => by
    rw [get?_union cf k a b hwa hwb]
    exact optRel_optVjoin_right rel cf hrefl hjre (get? k a) (get? k b))

/-- Any common upper bound of `a` and `b` is above their `union` (least-upper-bound universal). -/
theorem union_subset (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (cf : V → V → V)
    (hjlub : ∀ x y z, rel x z = true → rel y z = true → rel (cf x y) z = true)
    (a b c : PTree L) (hwa : WF a) (hwb : WF b) (hwc : WF c)
    (hac : subset rel a c = true) (hbc : subset rel b c = true) :
    subset rel (union cf a b) c = true :=
  (subset_iff_eq rel hrefl (union cf a b) c (WF_union cf a b hwa hwb) hwc).mpr (fun k => by
    rw [get?_union cf k a b hwa hwb]
    exact optRel_optVjoin_lub rel cf hjlub (get? k a) (get? k b) (get? k c)
      ((subset_iff_eq rel hrefl a c hwa hwc).mp hac k)
      ((subset_iff_eq rel hrefl b c hwb hwc).mp hbc k))

/-! ### Structural equality (`beq`) is lawful

On any two tries (canonical or not) `beq` decides propositional equality — `beq_refl` and
`eq_of_beq` below. The `NatCollection` wrapper turns these into a `LawfulBEq` instance; because
every collection is kept canonical, structural equality there coincides with logical (set/map)
equality. The proofs are mutual structural inductions mirroring `beq`/`beqList`. -/

mutual
/-- `beq` is reflexive (given a reflexive leaf `BEq`). -/
theorem beq_refl [BEq L] [LawfulBEq L] : (t : PTree L) → beq t t = true
  | .nil        => rfl
  | .tip p l    => by simp only [beq, beq_self_eq_true, Bool.and_self]
  | .bin p v m k => by
      show ((p == p) && (v == v) && (m == m) && beqList k.toList k.toList) = true
      rw [beqList_refl k.toList]
      simp only [beq_self_eq_true, Bool.and_self]
/-- `beqList` is reflexive (the `beq_refl` companion). -/
private theorem beqList_refl [BEq L] [LawfulBEq L] : (l : List (PTree L)) → beqList l l = true
  | []     => rfl
  | c :: r => by
      show (beq c c && beqList r r) = true
      rw [beq_refl c, beqList_refl r, Bool.and_self]
end

mutual
/-- `beq` decides propositional equality. -/
theorem eq_of_beq [BEq L] [LawfulBEq L] : {a b : PTree L} → beq a b = true → a = b
  | .nil,             .nil,             _ => rfl
  | .tip p1 l1,       .tip p2 l2,       h => by
      simp only [beq, Bool.and_eq_true] at h
      rw [LawfulBEq.eq_of_beq h.1, LawfulBEq.eq_of_beq h.2]
  | .bin p1 v1 m1 k1, .bin p2 v2 m2 k2, h => by
      simp only [beq, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hp, hv⟩, hm⟩, hk⟩ := h
      have hp' : p1 = p2 := LawfulBEq.eq_of_beq hp
      have hv' : v1 = v2 := LawfulBEq.eq_of_beq hv
      have hm' : m1 = m2 := LawfulBEq.eq_of_beq hm
      have hk' : k1 = k2 := Array.toList_inj.mp (eqList_of_beqList hk)
      subst hp'; subst hv'; subst hm'; subst hk'; rfl
  | .nil,             .tip _ _,         h => by simp [beq] at h
  | .nil,             .bin _ _ _ _,     h => by simp [beq] at h
  | .tip _ _,         .nil,             h => by simp [beq] at h
  | .tip _ _,         .bin _ _ _ _,     h => by simp [beq] at h
  | .bin _ _ _ _,     .nil,             h => by simp [beq] at h
  | .bin _ _ _ _,     .tip _ _,         h => by simp [beq] at h
/-- `beqList` decides propositional equality (the `eq_of_beq` companion). -/
private theorem eqList_of_beqList [BEq L] [LawfulBEq L] :
    {l1 l2 : List (PTree L)} → beqList l1 l2 = true → l1 = l2
  | [],       [],       _ => rfl
  | c1 :: r1, c2 :: r2, h => by
      simp only [beqList, Bool.and_eq_true] at h
      rw [eq_of_beq h.1, eqList_of_beqList h.2]
  | [],       _ :: _,   h => by simp [beqList] at h
  | _ :: _,   [],       h => by simp [beqList] at h
end

/-! ### `map`: functorial leaf remap (the `NatMap` functor's structural core)

`map g` rewrites every leaf with `g : L → L'`, leaving the trie's shape — prefixes, levels, masks,
and which keys are present — untouched; only the leaf type changes (`L` to `L'`). The value
denotation changes pointwise (`get?_map`: when `g`'s leaf action is `f` under `LeafOps.get?`, then
`get? k (map g t) = (get? k t).map f`), and the canonical-shape invariant carries over whenever `g`
preserves leaf emptiness and leaf membership (`WF_map`). `NatMap.map` instantiates this with
`g := Node.map f`. The recursion mirrors `beq`/`beqList`: `mapList` recurses structurally over
`kids.toList`, so termination is the same proven pattern. -/

mutual
/-- Rewrite every leaf of a trie with `g`, preserving all structure. -/
def map {L' : Type u'} (g : L → L') : PTree L → PTree L'
  | .nil                     => .nil
  | .tip pfx leaf            => .tip pfx (g leaf)
  | .bin pfx level mask kids => .bin pfx level mask (mapList g kids.toList).toArray
/-- `map` over a child list (the `map` companion). -/
private def mapList {L' : Type u'} (g : L → L') : List (PTree L) → List (PTree L')
  | []        => []
  | c :: rest => map g c :: mapList g rest
end

/-- `mapList` is `List.map` of `map`. -/
private theorem mapList_eq_map {L' : Type u'} (g : L → L') :
    (l : List (PTree L)) → mapList g l = l.map (map g)
  | []        => rfl
  | c :: rest => by rw [mapList, mapList_eq_map g rest, List.map_cons]

/-- The defining `bin` equation, with the children as an honest `Array.map`. -/
theorem map_bin {L' : Type u'} (g : L → L') (pfx level : Nat) (mask : UInt32)
    (kids : Array (PTree L)) :
    map g (.bin pfx level mask kids) = .bin pfx level mask (kids.map (map g)) := by
  have harr : (kids.toList.map (map g)).toArray = kids.map (map g) := by
    apply Array.toList_inj.mp
    simp [Array.toList_map]
  rw [map, mapList_eq_map, harr]

/-- `map` sends `nil` to `nil` and nothing else to `nil`. -/
theorem map_nil_iff {L' : Type u'} (g : L → L') (t : PTree L) :
    map g t = (.nil : PTree L') ↔ t = .nil := by
  cases t <;> simp [map]

/-- `childAt` commutes with `map`: routing then mapping equals mapping then routing. -/
private theorem childAt_map {L' : Type u'} (g : L → L') (mask : UInt32) (kids : Array (PTree L))
    (c : UInt32) :
    childAt mask (kids.map (map g)) c = map g (childAt mask kids c) := by
  unfold childAt
  rw [Array.getElem?_map]
  cases kids[arrayIndex mask c]? with
  | none   => simp [map]
  | some x => simp

/-- `map` preserves leaf membership when `g`'s leaf action does. Manual structural recursion (the
recursive call lands on a genuine child `kids[i]`, so termination is `get?`'s own measure). -/
theorem contains_map {L' V' : Type u'} [LeafOps L' V'] (g : L → L')
    (hcontains : ∀ l i, (LeafOps.contains (g l) i : Bool) = LeafOps.contains l i) (k : Nat) :
    (t : PTree L) → contains k (map g t) = contains k t
  | .nil => by simp [map, contains_nil]
  | .tip pfx leaf => by rw [map, contains_tip, contains_tip, hcontains]
  | .bin pfx level mask kids => by
      rw [map_bin, contains_bin, contains_bin, childAt_map]
      by_cases hb : arrayIndex mask (chunk k level) < kids.size
      · have hca : childAt mask kids (chunk k level) = kids[arrayIndex mask (chunk k level)]'hb := by
          unfold childAt; rw [Array.getElem?_eq_getElem hb, Option.getD_some]
        rw [hca, contains_map g hcontains k (kids[arrayIndex mask (chunk k level)]'hb)]
      · have hca : childAt mask kids (chunk k level) = (.nil : PTree L) := by
          unfold childAt; rw [Array.getElem?_eq_none (Nat.le_of_not_lt hb), Option.getD_none]
        rw [hca]; simp [map, contains_nil]
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- **`get?` of a `map`**: looking up a key applies `f` to whatever was there, where `f` is `g`'s
leaf action under `LeafOps.get?`. The functorial value-denotation seam. Manual structural
recursion (the recursive call lands on a genuine child). -/
theorem get?_map {L' V' : Type u'} [LeafOps L' V'] (g : L → L') (f : V → V')
    (hget : ∀ l i, (LeafOps.get? (g l) i : Option V') = (LeafOps.get? l i).map f) (k : Nat) :
    (t : PTree L) → get? k (map g t) = (get? k t).map f
  | .nil => by simp [map, get?_nil]
  | .tip pfx leaf => by
      rw [map, get?_tip, get?_tip]
      by_cases hk : (k >>> 5 == pfx) = true
      · rw [if_pos hk, if_pos hk]; exact hget leaf (chunk k 0)
      · rw [if_neg hk, if_neg hk]; rfl
  | .bin pfx level mask kids => by
      rw [map_bin, get?_bin, get?_bin, childAt_map]
      by_cases htb : testBit mask (chunk k level) = true
      · rw [if_pos htb, if_pos htb]
        by_cases hb : arrayIndex mask (chunk k level) < kids.size
        · have hca : childAt mask kids (chunk k level) = kids[arrayIndex mask (chunk k level)]'hb := by
            unfold childAt; rw [Array.getElem?_eq_getElem hb, Option.getD_some]
          rw [hca, get?_map g f hget k (kids[arrayIndex mask (chunk k level)]'hb)]
        · have hca : childAt mask kids (chunk k level) = (.nil : PTree L) := by
            unfold childAt; rw [Array.getElem?_eq_none (Nat.le_of_not_lt hb), Option.getD_none]
          rw [hca, map]; simp [get?_nil]
      · rw [if_neg htb, if_neg htb]; rfl
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- `map` preserves well-formedness when `g` preserves leaf emptiness and leaf membership. Manual
structural recursion (children recursed via genuine membership). -/
theorem WF_map {L' V' : Type u'} [LeafOps L' V'] (g : L → L')
    (hempty : ∀ l, (LeafOps.isEmpty (g l) : Bool) = LeafOps.isEmpty l)
    (hcontains : ∀ l i, (LeafOps.contains (g l) i : Bool) = LeafOps.contains l i) :
    (t : PTree L) → WF t → WF (map g t)
  | .nil => fun _ => by rw [map, WF]; trivial
  | .tip pfx leaf => fun h => by rw [WF] at h; rw [map, WF, hempty]; exact h
  | .bin pfx level mask kids => fun hwf => by
      rw [WF] at hwf
      obtain ⟨hlv, hsz, hpc, hkwf, hknn, halign⟩ := hwf
      rw [map_bin, WF]
      refine ⟨hlv, ?_, hpc, ?_, ?_, ?_⟩
      · rw [Array.size_map]; exact hsz
      · intro c hc
        rw [Array.mem_map] at hc
        obtain ⟨c0, hc0, rfl⟩ := hc
        exact WF_map g hempty hcontains c0 (hkwf c0 hc0)
      · intro c hc
        rw [Array.mem_map] at hc
        obtain ⟨c0, hc0, rfl⟩ := hc
        exact fun heq => hknn c0 hc0 ((map_nil_iff g c0).mp heq)
      · intro c hclt htb
        rw [childAt_map]
        intro j hj
        rw [contains_map g hcontains j (childAt mask kids c)] at hj
        exact halign c hclt htb j hj
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem hc0; omega

/-- Pointwise-on-members congruence for an accumulating sum-fold (the `size_map` companion:
core's fold congruences need whole-function equality, but `size_map`'s induction hypothesis
only covers genuine children). -/
private theorem foldl_add_congr {α : Type u'} (f₁ f₂ : α → Nat) :
    (l : List α) → (∀ c ∈ l, f₁ c = f₂ c) → (acc : Nat) →
    l.foldl (fun acc c => acc + f₁ c) acc = l.foldl (fun acc c => acc + f₂ c) acc
  | [], _, _ => rfl
  | c :: rest, h, acc => by
      rw [List.foldl_cons, List.foldl_cons, h c (List.mem_cons_self ..),
          foldl_add_congr f₁ f₂ rest (fun d hd => h d (List.mem_cons_of_mem c hd)) (acc + f₂ c)]

/-- `map` preserves `size` when `g`'s leaf action preserves leaf size: the trie shape is unchanged,
so the key count is the same sum of leaf sizes. Manual structural recursion; the children's
induction hypotheses thread through the size fold via `foldl_add_congr`. -/
theorem size_map {L' V' : Type u'} [LeafOps L' V'] (g : L → L')
    (hsize : ∀ l, LeafOps.size (g l) = LeafOps.size l) :
    (t : PTree L) → size (map g t) = size t
  | .nil => by simp only [map, size]
  | .tip pfx leaf => by simp only [map, size]; exact hsize leaf
  | .bin pfx level mask kids => by
      rw [map_bin]
      simp only [size]
      rw [Array.foldl_attach (f := fun acc (c : PTree L') => acc + c.size),
          Array.foldl_attach (f := fun acc (c : PTree L) => acc + c.size),
          Array.foldl_map, ← Array.foldl_toList, ← Array.foldl_toList]
      exact foldl_add_congr _ _ kids.toList (fun c hc => size_map g hsize c) 0
termination_by t => sizeOf t
decreasing_by
  simp_wf
  have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp hc)
  omega

mutual
/-- `map` respects pointwise equality of the leaf function. -/
theorem map_congr {L' : Type u'} (g₁ g₂ : L → L') (h : ∀ l, g₁ l = g₂ l) :
    (t : PTree L) → map g₁ t = map g₂ t
  | .nil                     => rfl
  | .tip pfx leaf            => by rw [map, map, h]
  | .bin pfx level mask kids => by rw [map, map, mapList_congr g₁ g₂ h kids.toList]
/-- `mapList` respects pointwise equality of the leaf function (the `map_congr` companion). -/
private theorem mapList_congr {L' : Type u'} (g₁ g₂ : L → L') (h : ∀ l, g₁ l = g₂ l) :
    (l : List (PTree L)) → mapList g₁ l = mapList g₂ l
  | []        => rfl
  | c :: rest => by rw [mapList, mapList, map_congr g₁ g₂ h c, mapList_congr g₁ g₂ h rest]
end

mutual
/-- Mapping a pointwise-identity leaf function is the identity (the functor identity law's core). -/
theorem map_eq_id (g : L → L) (h : ∀ l, g l = l) : (t : PTree L) → map g t = t
  | .nil                     => rfl
  | .tip pfx leaf            => by rw [map, h]
  | .bin pfx level mask kids => by rw [map, mapList_eq_id g h kids.toList]
/-- `mapList` of a pointwise-identity leaf function is the identity (the `map_eq_id` companion). -/
private theorem mapList_eq_id (g : L → L) (h : ∀ l, g l = l) : (l : List (PTree L)) → mapList g l = l
  | []        => rfl
  | c :: rest => by rw [mapList, map_eq_id g h c, mapList_eq_id g h rest]
end

mutual
/-- Mapping a composition is the composition of maps (the functor composition law's core). -/
theorem map_comp {L' : Type u'} {L'' : Type u''} (g₁ : L → L') (g₂ : L' → L'') :
    (t : PTree L) → map (fun l => g₂ (g₁ l)) t = map g₂ (map g₁ t)
  | .nil                     => rfl
  | .tip pfx leaf            => by rw [map, map, map]
  | .bin pfx level mask kids => by rw [map, map, map, mapList_comp g₁ g₂ kids.toList]
/-- `mapList` of a composition is the composition of `mapList`s (the `map_comp` companion). -/
private theorem mapList_comp {L' : Type u'} {L'' : Type u''} (g₁ : L → L') (g₂ : L' → L'') :
    (l : List (PTree L)) → mapList (fun l => g₂ (g₁ l)) l = mapList g₂ (mapList g₁ l)
  | []        => rfl
  | c :: rest => by rw [mapList, mapList, mapList, map_comp g₁ g₂ c, mapList_comp g₁ g₂ rest]
end

/-! ### Ordered queries: `minEntry?`/`maxEntry?` denotations

`minEntry?` returns a real entry — `get?` reads its value back at its key — and that key is a
lower bound on every present key (`maxEntry?` mirrors, as an upper bound). The walks pick slots by
bit-scans over the leaf occupancy bitmap (`LeafOps.slotsMask`) and the branch mask, so the proofs
ride on the bitmap-accuracy law (`LeafOps.testBit_slotsMask`) plus big-endian ordering: keys that
agree on the prefix above a level are ordered by their chunks at that level. -/

/-- A chunk's numeric value is the corresponding 5-bit field of the key. -/
private theorem chunk_toNat (n l : Nat) : (chunk n l).toNat = (n >>> (5 * l)) % 32 := by
  unfold chunk
  rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact UInt32.toNat_ofNat_of_lt' (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

/-- A strict high-bits order is a strict key order (right shift is monotone). -/
private theorem lt_of_shiftRight_lt {k j n : Nat} (h : k >>> n < j >>> n) : k < j := by
  refine Nat.not_le.mp fun hge => ?_
  have hle : j >>> n ≤ k >>> n := by
    rw [Nat.shiftRight_eq_div_pow j n, Nat.shiftRight_eq_div_pow k n]
    exact Nat.div_le_div_right hge
  omega

/-- Big-endian ordering: keys agreeing on the prefix above `l` are ordered by their level-`l`
chunks. The ordering core of the `minEntry?`/`maxEntry?` bound proofs. -/
private theorem lt_of_chunk_lt {k j : Nat} (l : Nat)
    (hp : prefixAbove k l = prefixAbove j l) (hc : chunk k l < chunk j l) : k < j := by
  have hc' : (k >>> (5 * l)) % 32 < (j >>> (5 * l)) % 32 := by
    have h := UInt32.lt_iff_toNat_lt.mp hc
    rwa [chunk_toNat k l, chunk_toNat j l] at h
  have hp' : (k >>> (5 * l)) / 32 = (j >>> (5 * l)) / 32 := by
    have h : (k >>> (5 * l)) >>> 5 = (j >>> (5 * l)) >>> 5 := by
      rw [← Nat.shiftRight_add, ← Nat.shiftRight_add, show 5 * l + 5 = 5 * (l + 1) from by omega]
      exact hp
    rw [Nat.shiftRight_eq_div_pow (k >>> (5 * l)) 5, Nat.shiftRight_eq_div_pow (j >>> (5 * l)) 5,
        show (2 : Nat) ^ 5 = 32 from rfl] at h
    exact h
  exact lt_of_shiftRight_lt (n := 5 * l) (by omega)

/-- The converse at the bottom level: ordered keys sharing their high bits order their bottom
chunks. -/
private theorem chunk0_lt_of_lt {k j : Nat} (h5 : k >>> 5 = j >>> 5) (hkj : k < j) :
    chunk k 0 < chunk j 0 := by
  apply UInt32.lt_iff_toNat_lt.mpr
  rw [chunk_toNat k 0, chunk_toNat j 0, Nat.mul_zero, Nat.shiftRight_zero, Nat.shiftRight_zero]
  rw [shiftRight5_eq, shiftRight5_eq] at h5
  omega

/-- The non-strict converse at any level: ordered keys with equal prefixes above `l` have
non-decreasing level-`l` chunks (the lower levels may still differ either way). -/
private theorem chunk_le_of_le {k j : Nat} (l : Nat)
    (hp : prefixAbove k l = prefixAbove j l) (hkj : k ≤ j) : chunk k l ≤ chunk j l := by
  rcases Nat.lt_or_ge (chunk j l).toNat (chunk k l).toNat with hlt | hge
  · exact absurd (lt_of_chunk_lt l hp.symm (UInt32.lt_iff_toNat_lt.mpr hlt)) (by omega)
  · exact UInt32.le_iff_toNat_le.mpr hge

/-- The key a `tip` ordered query reconstructs (`(pfx <<< 5) ||| s.toNat`, slot `s < 32`) has
bottom chunk exactly `s` — the low-bits companion of `shiftLeft_lor_shiftRight`. -/
private theorem chunk_shiftLeft_lor_zero (p : Nat) (s : UInt32) (hs : s < 32) :
    chunk ((p <<< 5) ||| s.toNat) 0 = s := by
  have key : chunk ((p <<< 5) ||| s.toNat) 0 = chunk s.toNat 0 := by
    unfold chunk
    congr 1
    simp only [Nat.mul_zero, Nat.shiftRight_zero]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hi : i < 5
    · rw [decide_eq_false (by omega : ¬ 5 ≤ i)]
      simp
    · rw [show Nat.testBit 31 i = false from by
            rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.testBit_two_pow_sub_one]
            exact decide_eq_false hi,
          Bool.and_false, Bool.and_false]
  rw [key, chunk_toNat_zero s hs]

/-- A non-empty leaf's occupancy bitmap is non-zero: its representative slot's bit is set. -/
private theorem slotsMask_ne_zero (leaf : L) (hb : LeafOps.isEmpty (V := V) leaf = false) :
    LeafOps.slotsMask (V := V) leaf ≠ 0 := by
  intro h0
  have hcs : LeafOps.contains leaf (LeafOps.someSlot (V := V) leaf) = true :=
    LeafOps.contains_someSlot leaf hb
  rw [← LeafOps.testBit_slotsMask leaf (LeafOps.someSlot (V := V) leaf)
        (LeafOps.someSlot_lt leaf hb),
      h0, testBit_zero] at hcs
  exact absurd hcs (by decide)

/-- The entry `minEntry?` returns is real: `get?` reads its value back at its key. Member
recursion down the first-child spine; at the `tip`, the reconstructed key routes back to the
scanned slot. -/
theorem get?_of_minEntry? : (t : PTree L) → WF t → ∀ (k : Nat) (v : V),
    minEntry? t = some (k, v) → get? k t = some v
  | .nil => fun _ k v h => by
      rw [minEntry?] at h
      exact absurd h (by simp)
  | .tip pfx leaf => fun hwf k v h => by
      rw [WF] at hwf
      rw [minEntry?] at h
      obtain ⟨v', hg, hkv⟩ := Option.map_eq_some_iff.mp h
      injection hkv with hk hv
      subst hk hv
      have hm : LeafOps.slotsMask leaf ≠ 0 := slotsMask_ne_zero leaf hwf
      have hs : lowestSetIdx (LeafOps.slotsMask leaf) < 32 := lowestSetIdx_lt _ hm
      rw [get?_tip,
          if_pos (beq_iff_eq.mpr (shiftLeft_lor_shiftRight pfx _ 5
            (UInt32.lt_iff_toNat_lt.mp hs))),
          chunk_shiftLeft_lor_zero pfx _ hs]
      exact hg
  | .bin pfx level mask kids => fun hwf k v h => by
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, hpc, hwfk, _, hal⟩ := hwf'
      have hm : mask ≠ 0 := by
        intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
      have hb : 0 < kids.size := by rw [hsz]; omega
      rw [minEntry?, dif_pos hb] at h
      have hwk : WF (kids[0]'hb) := hwfk _ (Array.getElem_mem hb)
      have ih := get?_of_minEntry? (kids[0]'hb) hwk k v h
      have hc0 : childAt mask kids (lowestSetIdx mask) = kids[0]'hb := by
        unfold childAt
        rw [arrayIndex_lowestSetIdx mask hm, Array.getElem?_eq_getElem hb, Option.getD_some]
      have hkmem : contains k (kids[0]'hb) = true := by
        rw [contains_eq_isSome, ih]; rfl
      have halk := hal (lowestSetIdx mask) (lowestSetIdx_lt mask hm) (testBit_lowestSetIdx mask hm)
      rw [hc0] at halk
      obtain ⟨hck, _⟩ := halk k hkmem
      rw [get?_bin, hck, if_pos (testBit_lowestSetIdx mask hm), hc0]
      exact ih
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- The entry `maxEntry?` returns is real: `get?` reads its value back at its key (the
`get?_of_minEntry?` mirror down the last-child spine). -/
theorem get?_of_maxEntry? : (t : PTree L) → WF t → ∀ (k : Nat) (v : V),
    maxEntry? t = some (k, v) → get? k t = some v
  | .nil => fun _ k v h => by
      rw [maxEntry?] at h
      exact absurd h (by simp)
  | .tip pfx leaf => fun hwf k v h => by
      rw [WF] at hwf
      rw [maxEntry?] at h
      obtain ⟨v', hg, hkv⟩ := Option.map_eq_some_iff.mp h
      injection hkv with hk hv
      subst hk hv
      have hm : LeafOps.slotsMask leaf ≠ 0 := slotsMask_ne_zero leaf hwf
      have hs : highestSetIdx (LeafOps.slotsMask leaf) < 32 := highestSetIdx_lt _ hm
      rw [get?_tip,
          if_pos (beq_iff_eq.mpr (shiftLeft_lor_shiftRight pfx _ 5
            (UInt32.lt_iff_toNat_lt.mp hs))),
          chunk_shiftLeft_lor_zero pfx _ hs]
      exact hg
  | .bin pfx level mask kids => fun hwf k v h => by
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, hpc, hwfk, _, hal⟩ := hwf'
      have hm : mask ≠ 0 := by
        intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
      have hb0 : 0 < kids.size := by rw [hsz]; omega
      have hb : kids.size - 1 < kids.size := by omega
      rw [maxEntry?, dif_pos hb] at h
      have hwk : WF (kids[kids.size - 1]'hb) := hwfk _ (Array.getElem_mem hb)
      have ih := get?_of_maxEntry? (kids[kids.size - 1]'hb) hwk k v h
      have hidx : arrayIndex mask (highestSetIdx mask) = kids.size - 1 := by
        rw [arrayIndex_highestSetIdx mask hm, hsz]
      have hc31 : childAt mask kids (highestSetIdx mask) = kids[kids.size - 1]'hb := by
        unfold childAt
        rw [hidx, Array.getElem?_eq_getElem hb, Option.getD_some]
      have hkmem : contains k (kids[kids.size - 1]'hb) = true := by
        rw [contains_eq_isSome, ih]; rfl
      have halk := hal (highestSetIdx mask) (highestSetIdx_lt mask hm)
        (testBit_highestSetIdx mask hm)
      rw [hc31] at halk
      obtain ⟨hck, _⟩ := halk k hkmem
      rw [get?_bin, hck, if_pos (testBit_highestSetIdx mask hm), hc31]
      exact ih
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- `minEntry?`'s key is a lower bound: no present key is below it. At the `tip`, the chosen slot
is the bitmap minimum (`lowestSetIdx_le_of_testBit`); at a `bin`, any key outside the first child
routes to a strictly higher slot, and big-endian ordering lifts slot order to key order. -/
theorem minEntry?_le : (t : PTree L) → WF t → ∀ (k : Nat) (v : V) (j : Nat),
    minEntry? t = some (k, v) → contains j t = true → k ≤ j
  | .nil => fun _ k v j h _ => by
      rw [minEntry?] at h
      exact absurd h (by simp)
  | .tip pfx leaf => fun hwf k v j h hj => by
      rw [WF] at hwf
      rw [minEntry?] at h
      obtain ⟨v', hg, hkv⟩ := Option.map_eq_some_iff.mp h
      injection hkv with hk hv
      subst hk
      rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hj
      obtain ⟨hj5, hjc⟩ := hj
      have hm : LeafOps.slotsMask leaf ≠ 0 := slotsMask_ne_zero leaf hwf
      have hs : lowestSetIdx (LeafOps.slotsMask leaf) < 32 := lowestSetIdx_lt _ hm
      have hkhi : ((pfx <<< 5) ||| (lowestSetIdx (LeafOps.slotsMask leaf)).toNat) >>> 5 = pfx :=
        shiftLeft_lor_shiftRight pfx _ 5 (UInt32.lt_iff_toNat_lt.mp hs)
      have hkc : chunk ((pfx <<< 5) ||| (lowestSetIdx (LeafOps.slotsMask leaf)).toNat) 0
          = lowestSetIdx (LeafOps.slotsMask leaf) := chunk_shiftLeft_lor_zero pfx _ hs
      have htbj : testBit (LeafOps.slotsMask leaf) (chunk j 0) = true := by
        rw [LeafOps.testBit_slotsMask leaf (chunk j 0) (chunk_lt j 0)]
        exact hjc
      have hle := lowestSetIdx_le_of_testBit (LeafOps.slotsMask leaf) (chunk j 0)
        (chunk_lt j 0) htbj
      by_cases heq : lowestSetIdx (LeafOps.slotsMask leaf) = chunk j 0
      · exact Nat.le_of_eq ((key_eq_iff _ j).mpr ⟨hkhi.trans hj5.symm, by rw [hkc, heq]⟩)
      · refine Nat.le_of_lt (lt_of_chunk_lt 0 ?_ ?_)
        · show _ >>> 5 = j >>> 5
          rw [hkhi, hj5]
        · rw [hkc]
          rcases UInt32.lt_or_lt_of_ne heq with hlt | hgt
          · exact hlt
          · exact absurd (UInt32.le_iff_toNat_le.mp hle)
              (by have := UInt32.lt_iff_toNat_lt.mp hgt; omega)
  | .bin pfx level mask kids => fun hwf k v j h hj => by
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, hpc, hwfk, _, hal⟩ := hwf'
      have hm : mask ≠ 0 := by
        intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
      have hb : 0 < kids.size := by rw [hsz]; omega
      rw [minEntry?, dif_pos hb] at h
      have hwk : WF (kids[0]'hb) := hwfk _ (Array.getElem_mem hb)
      have hc0 : childAt mask kids (lowestSetIdx mask) = kids[0]'hb := by
        unfold childAt
        rw [arrayIndex_lowestSetIdx mask hm, Array.getElem?_eq_getElem hb, Option.getD_some]
      rw [contains_bin, Bool.and_eq_true] at hj
      obtain ⟨htj, hjc⟩ := hj
      by_cases hcj : chunk j level = lowestSetIdx mask
      · rw [hcj, hc0] at hjc
        exact minEntry?_le (kids[0]'hb) hwk k v j h hjc
      · have hkmem : contains k (kids[0]'hb) = true := by
          rw [contains_eq_isSome, get?_of_minEntry? (kids[0]'hb) hwk k v h]; rfl
        have halk := hal (lowestSetIdx mask) (lowestSetIdx_lt mask hm)
          (testBit_lowestSetIdx mask hm)
        rw [hc0] at halk
        obtain ⟨hck, hpk⟩ := halk k hkmem
        obtain ⟨_, hpj⟩ := hal (chunk j level) (chunk_lt j level) htj j hjc
        have hle := lowestSetIdx_le_of_testBit mask (chunk j level) (chunk_lt j level) htj
        refine Nat.le_of_lt (lt_of_chunk_lt level (hpk.trans hpj.symm) ?_)
        rw [hck]
        rcases UInt32.lt_or_lt_of_ne (fun hh => hcj hh.symm) with hlt | hgt
        · exact hlt
        · exact absurd (UInt32.le_iff_toNat_le.mp hle)
            (by have := UInt32.lt_iff_toNat_lt.mp hgt; omega)
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- `maxEntry?`'s key is an upper bound: no present key is above it (the `minEntry?_le` mirror:
highest slot at the `tip`, last child at a `bin`). -/
theorem le_maxEntry? : (t : PTree L) → WF t → ∀ (k : Nat) (v : V) (j : Nat),
    maxEntry? t = some (k, v) → contains j t = true → j ≤ k
  | .nil => fun _ k v j h _ => by
      rw [maxEntry?] at h
      exact absurd h (by simp)
  | .tip pfx leaf => fun hwf k v j h hj => by
      rw [WF] at hwf
      rw [maxEntry?] at h
      obtain ⟨v', hg, hkv⟩ := Option.map_eq_some_iff.mp h
      injection hkv with hk hv
      subst hk
      rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hj
      obtain ⟨hj5, hjc⟩ := hj
      have hm : LeafOps.slotsMask leaf ≠ 0 := slotsMask_ne_zero leaf hwf
      have hs : highestSetIdx (LeafOps.slotsMask leaf) < 32 := highestSetIdx_lt _ hm
      have hkhi : ((pfx <<< 5) ||| (highestSetIdx (LeafOps.slotsMask leaf)).toNat) >>> 5 = pfx :=
        shiftLeft_lor_shiftRight pfx _ 5 (UInt32.lt_iff_toNat_lt.mp hs)
      have hkc : chunk ((pfx <<< 5) ||| (highestSetIdx (LeafOps.slotsMask leaf)).toNat) 0
          = highestSetIdx (LeafOps.slotsMask leaf) := chunk_shiftLeft_lor_zero pfx _ hs
      have htbj : testBit (LeafOps.slotsMask leaf) (chunk j 0) = true := by
        rw [LeafOps.testBit_slotsMask leaf (chunk j 0) (chunk_lt j 0)]
        exact hjc
      have hle := le_highestSetIdx_of_testBit (LeafOps.slotsMask leaf) (chunk j 0)
        (chunk_lt j 0) htbj
      by_cases heq : highestSetIdx (LeafOps.slotsMask leaf) = chunk j 0
      · exact Nat.le_of_eq ((key_eq_iff _ j).mpr ⟨hkhi.trans hj5.symm, by rw [hkc, heq]⟩).symm
      · refine Nat.le_of_lt (lt_of_chunk_lt 0 ?_ ?_)
        · show j >>> 5 = _ >>> 5
          rw [hkhi, hj5]
        · rw [hkc]
          rcases UInt32.lt_or_lt_of_ne heq with hlt | hgt
          · exact absurd (UInt32.le_iff_toNat_le.mp hle)
              (by have := UInt32.lt_iff_toNat_lt.mp hlt; omega)
          · exact hgt
  | .bin pfx level mask kids => fun hwf k v j h hj => by
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, hpc, hwfk, _, hal⟩ := hwf'
      have hm : mask ≠ 0 := by
        intro h0; rw [h0, show popCount 0 = 0 from rfl] at hpc; omega
      have hb0 : 0 < kids.size := by rw [hsz]; omega
      have hb : kids.size - 1 < kids.size := by omega
      rw [maxEntry?, dif_pos hb] at h
      have hwk : WF (kids[kids.size - 1]'hb) := hwfk _ (Array.getElem_mem hb)
      have hidx : arrayIndex mask (highestSetIdx mask) = kids.size - 1 := by
        rw [arrayIndex_highestSetIdx mask hm, hsz]
      have hc31 : childAt mask kids (highestSetIdx mask) = kids[kids.size - 1]'hb := by
        unfold childAt
        rw [hidx, Array.getElem?_eq_getElem hb, Option.getD_some]
      rw [contains_bin, Bool.and_eq_true] at hj
      obtain ⟨htj, hjc⟩ := hj
      by_cases hcj : chunk j level = highestSetIdx mask
      · rw [hcj, hc31] at hjc
        exact le_maxEntry? (kids[kids.size - 1]'hb) hwk k v j h hjc
      · have hkmem : contains k (kids[kids.size - 1]'hb) = true := by
          rw [contains_eq_isSome, get?_of_maxEntry? (kids[kids.size - 1]'hb) hwk k v h]; rfl
        have halk := hal (highestSetIdx mask) (highestSetIdx_lt mask hm)
          (testBit_highestSetIdx mask hm)
        rw [hc31] at halk
        obtain ⟨hck, hpk⟩ := halk k hkmem
        obtain ⟨_, hpj⟩ := hal (chunk j level) (chunk_lt j level) htj j hjc
        have hle := le_highestSetIdx_of_testBit mask (chunk j level) (chunk_lt j level) htj
        refine Nat.le_of_lt (lt_of_chunk_lt level (hpj.trans hpk.symm) ?_)
        rw [hck]
        rcases UInt32.lt_or_lt_of_ne hcj with hlt | hgt
        · exact hlt
        · exact absurd (UInt32.le_iff_toNat_le.mp hle)
            (by have := UInt32.lt_iff_toNat_lt.mp hgt; omega)
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-! ### Ordered queries: `entryGT?`/`entryLT?` denotations

The full successor spec: a `some (j, v)` answer is a real entry (`get?` reads it back), its key is
strictly beyond the query key, and it is the *nearest* such key; a `none` answer means nothing lies
beyond the query key. The fallback walks (`minEntryAbove`/`maxEntryBelow`) get their own spec
lemmas, which the main inductions consume at each `bin`. -/

/-- A non-empty well-formed trie has a least entry (`minEntry?` is total off `nil`). -/
theorem isSome_minEntry? : (t : PTree L) → WF t → t ≠ .nil → (minEntry? t).isSome = true
  | .nil => fun _ hne => absurd rfl hne
  | .tip pfx leaf => fun hwf _ => by
      rw [WF] at hwf
      have hm : LeafOps.slotsMask leaf ≠ 0 := slotsMask_ne_zero leaf hwf
      have htb : testBit (LeafOps.slotsMask leaf) (lowestSetIdx (LeafOps.slotsMask leaf)) = true :=
        testBit_lowestSetIdx _ hm
      rw [LeafOps.testBit_slotsMask leaf _ (lowestSetIdx_lt _ hm),
          LeafOps.contains_eq_isSome] at htb
      simp only [minEntry?]
      cases hg : LeafOps.get? leaf (lowestSetIdx (LeafOps.slotsMask leaf)) with
      | none => rw [hg] at htb; simp at htb
      | some v => rfl
  | .bin pfx level mask kids => fun hwf _ => by
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, hpc, hwfk, hnn, hal⟩ := hwf'
      have hb : 0 < kids.size := by rw [hsz]; omega
      rw [minEntry?, dif_pos hb]
      exact isSome_minEntry? _ (hwfk _ (Array.getElem_mem hb)) (hnn _ (Array.getElem_mem hb))
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- A non-empty well-formed trie has a greatest entry (`maxEntry?` is total off `nil`). -/
theorem isSome_maxEntry? : (t : PTree L) → WF t → t ≠ .nil → (maxEntry? t).isSome = true
  | .nil => fun _ hne => absurd rfl hne
  | .tip pfx leaf => fun hwf _ => by
      rw [WF] at hwf
      have hm : LeafOps.slotsMask leaf ≠ 0 := slotsMask_ne_zero leaf hwf
      have htb : testBit (LeafOps.slotsMask leaf) (highestSetIdx (LeafOps.slotsMask leaf)) = true :=
        testBit_highestSetIdx _ hm
      rw [LeafOps.testBit_slotsMask leaf _ (highestSetIdx_lt _ hm),
          LeafOps.contains_eq_isSome] at htb
      simp only [maxEntry?]
      cases hg : LeafOps.get? leaf (highestSetIdx (LeafOps.slotsMask leaf)) with
      | none => rw [hg] at htb; simp at htb
      | some v => rfl
  | .bin pfx level mask kids => fun hwf _ => by
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, hpc, hwfk, hnn, hal⟩ := hwf'
      have hb0 : 0 < kids.size := by rw [hsz]; omega
      have hb : kids.size - 1 < kids.size := by omega
      rw [maxEntry?, dif_pos hb]
      exact isSome_maxEntry? _ (hwfk _ (Array.getElem_mem hb)) (hnn _ (Array.getElem_mem hb))
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- The next-sibling fallback answers correctly: a `some (j, v)` from
`minEntryAbove mask kids c` is a real entry of the `bin`, routes strictly above slot `c`, and is
least among the `bin`'s keys routing strictly above `c`. -/
private theorem minEntryAbove_spec (pfx level : Nat) (mask : UInt32) (kids : Array (PTree L))
    (hwf : WF (.bin pfx level mask kids)) (c : UInt32) (hc : c < 32) (j : Nat) (v : V)
    (h : minEntryAbove mask kids c = some (j, v)) :
    get? j (.bin pfx level mask kids) = some v
    ∧ c < chunk j level
    ∧ ∀ j2, contains j2 (.bin pfx level mask kids) = true → c < chunk j2 level → j ≤ j2 := by
  have hwf' := hwf
  rw [WF] at hwf'
  obtain ⟨hl, hsz, hpc, hwfk, hnn, hal⟩ := hwf'
  simp only [minEntryAbove] at h
  by_cases hm0 : mask &&& upperMask c = 0
  · rw [if_pos (beq_iff_eq.mpr hm0)] at h
    exact absurd h (by simp)
  · rw [if_neg (fun hb => hm0 (beq_iff_eq.mp hb))] at h
    have hs32 : lowestSetIdx (mask &&& upperMask c) < 32 := lowestSetIdx_lt _ hm0
    have htbm : testBit (mask &&& upperMask c) (lowestSetIdx (mask &&& upperMask c)) = true :=
      testBit_lowestSetIdx _ hm0
    rw [testBit_and] at htbm
    obtain ⟨htbs, hups⟩ := and_split htbm
    have hcs : c < lowestSetIdx (mask &&& upperMask c) :=
      lt_of_testBit_upperMask c _ hc hs32 hups
    have hbs : arrayIndex mask (lowestSetIdx (mask &&& upperMask c)) < kids.size := by
      rw [hsz]; exact arrayIndex_lt mask _ htbs
    have hcA : childAt mask kids (lowestSetIdx (mask &&& upperMask c))
        = kids[arrayIndex mask (lowestSetIdx (mask &&& upperMask c))]'hbs := by
      unfold childAt; rw [Array.getElem?_eq_getElem hbs, Option.getD_some]
    have hwfc : WF (childAt mask kids (lowestSetIdx (mask &&& upperMask c))) := by
      rw [hcA]; exact hwfk _ (Array.getElem_mem hbs)
    have hget : get? j (childAt mask kids (lowestSetIdx (mask &&& upperMask c))) = some v :=
      get?_of_minEntry? _ hwfc j v h
    have hmem : contains j (childAt mask kids (lowestSetIdx (mask &&& upperMask c))) = true := by
      rw [contains_eq_isSome, hget]; rfl
    obtain ⟨hcj, hpj⟩ := hal (lowestSetIdx (mask &&& upperMask c)) hs32 htbs j hmem
    refine ⟨?_, ?_, ?_⟩
    · rw [get?_bin, hcj, if_pos htbs]
      exact hget
    · rw [hcj]; exact hcs
    · intro j2 hj2 hcj2
      rw [contains_bin, Bool.and_eq_true] at hj2
      obtain ⟨htj2, hj2c⟩ := hj2
      have htm2 : testBit (mask &&& upperMask c) (chunk j2 level) = true := by
        rw [testBit_and, htj2, testBit_upperMask_lt c _ (chunk_lt j2 level) hcj2]; rfl
      have hle2 : lowestSetIdx (mask &&& upperMask c) ≤ chunk j2 level :=
        lowestSetIdx_le_of_testBit _ _ (chunk_lt j2 level) htm2
      obtain ⟨_, hpj2⟩ := hal (chunk j2 level) (chunk_lt j2 level) htj2 j2 hj2c
      by_cases heq2 : chunk j2 level = lowestSetIdx (mask &&& upperMask c)
      · rw [heq2] at hj2c
        exact minEntry?_le _ hwfc j v j2 h hj2c
      · refine Nat.le_of_lt (lt_of_chunk_lt level (hpj.trans hpj2.symm) ?_)
        rw [hcj]
        rcases UInt32.lt_or_lt_of_ne (fun hh => heq2 hh.symm) with hlt | hgt
        · exact hlt
        · exact absurd (UInt32.le_iff_toNat_le.mp hle2)
            (by have := UInt32.lt_iff_toNat_lt.mp hgt; omega)

/-- A `none` fallback answer means no present slot lies strictly above `c` at all. -/
private theorem minEntryAbove_eq_none (pfx level : Nat) (mask : UInt32) (kids : Array (PTree L))
    (hwf : WF (.bin pfx level mask kids)) (c : UInt32)
    (h : minEntryAbove mask kids c = none) : mask &&& upperMask c = 0 := by
  have hwf' := hwf
  rw [WF] at hwf'
  obtain ⟨hl, hsz, hpc, hwfk, hnn, hal⟩ := hwf'
  simp only [minEntryAbove] at h
  by_cases hm0 : mask &&& upperMask c = 0
  · exact hm0
  · rw [if_neg (fun hb => hm0 (beq_iff_eq.mp hb))] at h
    have htbm : testBit (mask &&& upperMask c) (lowestSetIdx (mask &&& upperMask c)) = true :=
      testBit_lowestSetIdx _ hm0
    rw [testBit_and] at htbm
    obtain ⟨htbs, _⟩ := and_split htbm
    have hbs : arrayIndex mask (lowestSetIdx (mask &&& upperMask c)) < kids.size := by
      rw [hsz]; exact arrayIndex_lt mask _ htbs
    have hcA : childAt mask kids (lowestSetIdx (mask &&& upperMask c))
        = kids[arrayIndex mask (lowestSetIdx (mask &&& upperMask c))]'hbs := by
      unfold childAt; rw [Array.getElem?_eq_getElem hbs, Option.getD_some]
    have hsome : (minEntry? (childAt mask kids (lowestSetIdx (mask &&& upperMask c)))).isSome
        = true := by
      rw [hcA]
      exact isSome_minEntry? _ (hwfk _ (Array.getElem_mem hbs)) (hnn _ (Array.getElem_mem hbs))
    rw [h] at hsome
    simp at hsome

/-- The entry `entryGT?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_entryGT? : (t : PTree L) → WF t → ∀ (k j : Nat) (v : V),
    entryGT? k t = some (j, v) → get? j t = some v
  | .nil => fun _ k j v h => by
      rw [entryGT?] at h
      exact absurd h (by simp)
  | .tip pfx leaf => fun hwf k j v h => by
      simp only [entryGT?] at h
      rcases Nat.lt_trichotomy (k >>> 5) pfx with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        exact get?_of_minEntry? _ hwf j v h
      · rw [if_neg (by omega), if_neg (by omega)] at h
        by_cases hm0 : LeafOps.slotsMask leaf &&& upperMask (chunk k 0) = 0
        · rw [if_pos (beq_iff_eq.mpr hm0)] at h
          exact absurd h (by simp)
        · rw [if_neg (fun hb => hm0 (beq_iff_eq.mp hb))] at h
          obtain ⟨v', hg, hkv⟩ := Option.map_eq_some_iff.mp h
          injection hkv with hk hv
          subst hk hv
          have hs : lowestSetIdx (LeafOps.slotsMask leaf &&& upperMask (chunk k 0)) < 32 :=
            lowestSetIdx_lt _ hm0
          rw [get?_tip,
              if_pos (beq_iff_eq.mpr (shiftLeft_lor_shiftRight pfx _ 5
                (UInt32.lt_iff_toNat_lt.mp hs))),
              chunk_shiftLeft_lor_zero pfx _ hs]
          exact hg
      · rw [if_neg (by omega), if_pos hgt] at h
        exact absurd h (by simp)
  | .bin pfx level mask kids => fun hwf k j v h => by
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, hpc, hwfk, hnn, hal⟩ := hwf'
      simp only [entryGT?] at h
      rcases Nat.lt_trichotomy (prefixAbove k level) pfx with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        exact get?_of_minEntry? _ hwf j v h
      · rw [if_neg (by omega), if_neg (by omega)] at h
        by_cases htb : testBit mask (chunk k level) = true
        · rw [if_pos htb] at h
          have hb : arrayIndex mask (chunk k level) < kids.size := by
            rw [hsz]; exact arrayIndex_lt mask _ htb
          rw [dif_pos hb] at h
          cases ho : entryGT? k (kids[arrayIndex mask (chunk k level)]'hb) with
          | some e =>
            rw [ho] at h
            replace h : some e = some (j, v) := h
            injection h with he
            subst he
            have hwk : WF (kids[arrayIndex mask (chunk k level)]'hb) :=
              hwfk _ (Array.getElem_mem hb)
            have ih := get?_of_entryGT? _ hwk k j v ho
            have hcA : childAt mask kids (chunk k level)
                = kids[arrayIndex mask (chunk k level)]'hb := by
              unfold childAt; rw [Array.getElem?_eq_getElem hb, Option.getD_some]
            have hmem : contains j (kids[arrayIndex mask (chunk k level)]'hb) = true := by
              rw [contains_eq_isSome, ih]; rfl
            have halk := hal (chunk k level) (chunk_lt k level) htb
            rw [hcA] at halk
            obtain ⟨hcj, _⟩ := halk j hmem
            rw [get?_bin, hcj, if_pos htb, hcA]
            exact ih
          | none =>
            rw [ho] at h
            replace h : minEntryAbove mask kids (chunk k level) = some (j, v) := h
            exact (minEntryAbove_spec pfx level mask kids hwf (chunk k level)
              (chunk_lt k level) j v h).1
        · rw [if_neg htb] at h
          exact (minEntryAbove_spec pfx level mask kids hwf (chunk k level)
            (chunk_lt k level) j v h).1
      · rw [if_neg (by omega), if_pos hgt] at h
        exact absurd h (by simp)
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- `entryGT?`'s answer is strictly greater than the query key (it is a *successor*). -/
theorem entryGT?_gt : (t : PTree L) → WF t → ∀ (k j : Nat) (v : V),
    entryGT? k t = some (j, v) → k < j
  | .nil => fun _ k j v h => by
      rw [entryGT?] at h
      exact absurd h (by simp)
  | .tip pfx leaf => fun hwf k j v h => by
      simp only [entryGT?] at h
      rcases Nat.lt_trichotomy (k >>> 5) pfx with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        have hmem : contains j (.tip pfx leaf) = true := by
          rw [contains_eq_isSome, get?_of_minEntry? _ hwf j v h]; rfl
        have hj5 : j >>> 5 = pfx := hi_eq_of_contains_tip hmem
        exact lt_of_shiftRight_lt (n := 5) (by omega)
      · rw [if_neg (by omega), if_neg (by omega)] at h
        by_cases hm0 : LeafOps.slotsMask leaf &&& upperMask (chunk k 0) = 0
        · rw [if_pos (beq_iff_eq.mpr hm0)] at h
          exact absurd h (by simp)
        · rw [if_neg (fun hb => hm0 (beq_iff_eq.mp hb))] at h
          obtain ⟨v', hg, hkv⟩ := Option.map_eq_some_iff.mp h
          injection hkv with hk hv
          subst hk
          have hs : lowestSetIdx (LeafOps.slotsMask leaf &&& upperMask (chunk k 0)) < 32 :=
            lowestSetIdx_lt _ hm0
          have htbm := testBit_lowestSetIdx _ hm0
          rw [testBit_and] at htbm
          obtain ⟨_, hups⟩ := and_split htbm
          have hcs : chunk k 0 < lowestSetIdx (LeafOps.slotsMask leaf &&& upperMask (chunk k 0)) :=
            lt_of_testBit_upperMask _ _ (chunk_lt k 0) hs hups
          have hkhi : ((pfx <<< 5)
              ||| (lowestSetIdx (LeafOps.slotsMask leaf &&& upperMask (chunk k 0))).toNat) >>> 5
              = pfx := shiftLeft_lor_shiftRight pfx _ 5 (UInt32.lt_iff_toNat_lt.mp hs)
          refine lt_of_chunk_lt 0 ?_ ?_
          · show k >>> 5 = _ >>> 5
            rw [hkhi, hpe]
          · rw [chunk_shiftLeft_lor_zero pfx _ hs]
            exact hcs
      · rw [if_neg (by omega), if_pos hgt] at h
        exact absurd h (by simp)
  | .bin pfx level mask kids => fun hwf k j v h => by
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, hpc, hwfk, hnn, hal⟩ := hwf'
      simp only [entryGT?] at h
      rcases Nat.lt_trichotomy (prefixAbove k level) pfx with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        have hmem : contains j (.bin pfx level mask kids) = true := by
          rw [contains_eq_isSome, get?_of_minEntry? _ hwf j v h]; rfl
        rw [contains_bin, Bool.and_eq_true] at hmem
        obtain ⟨htj, hjc⟩ := hmem
        obtain ⟨_, hpj⟩ := hal (chunk j level) (chunk_lt j level) htj j hjc
        rw [← hpj] at hlt
        exact lt_of_shiftRight_lt hlt
      · rw [if_neg (by omega), if_neg (by omega)] at h
        have hfall : ∀ (h' : minEntryAbove mask kids (chunk k level) = some (j, v)), k < j := by
          intro h'
          obtain ⟨hget, hcgt, _⟩ := minEntryAbove_spec pfx level mask kids hwf (chunk k level)
            (chunk_lt k level) j v h'
          have hmem : contains j (.bin pfx level mask kids) = true := by
            rw [contains_eq_isSome, hget]; rfl
          rw [contains_bin, Bool.and_eq_true] at hmem
          obtain ⟨htj, hjc⟩ := hmem
          obtain ⟨_, hpj⟩ := hal (chunk j level) (chunk_lt j level) htj j hjc
          exact lt_of_chunk_lt level (hpe.trans hpj.symm) hcgt
        by_cases htb : testBit mask (chunk k level) = true
        · rw [if_pos htb] at h
          have hb : arrayIndex mask (chunk k level) < kids.size := by
            rw [hsz]; exact arrayIndex_lt mask _ htb
          rw [dif_pos hb] at h
          cases ho : entryGT? k (kids[arrayIndex mask (chunk k level)]'hb) with
          | some e =>
            rw [ho] at h
            replace h : some e = some (j, v) := h
            injection h with he
            subst he
            exact entryGT?_gt _ (hwfk _ (Array.getElem_mem hb)) k j v ho
          | none =>
            rw [ho] at h
            replace h : minEntryAbove mask kids (chunk k level) = some (j, v) := h
            exact hfall h
        · rw [if_neg htb] at h
          exact hfall h
      · rw [if_neg (by omega), if_pos hgt] at h
        exact absurd h (by simp)
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- A `none` from `entryGT?` is complete: nothing in the trie lies strictly above the query key. -/
theorem le_of_entryGT?_eq_none : (t : PTree L) → WF t → ∀ (k : Nat),
    entryGT? k t = none → ∀ (j : Nat), contains j t = true → j ≤ k
  | .nil => fun _ k _ j hj => by
      rw [contains_nil] at hj
      exact absurd hj (by decide)
  | .tip pfx leaf => fun hwf k h j hj => by
      have hwfc := hwf
      rw [WF] at hwfc
      simp only [entryGT?] at h
      rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hj
      obtain ⟨hj5, hjc⟩ := hj
      rcases Nat.lt_trichotomy (k >>> 5) pfx with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        have hsome := isSome_minEntry? (.tip pfx leaf) hwf (by simp)
        rw [h] at hsome
        simp at hsome
      · rw [if_neg (by omega), if_neg (by omega)] at h
        by_cases hm0 : LeafOps.slotsMask leaf &&& upperMask (chunk k 0) = 0
        · refine Nat.not_lt.mp fun hkj => ?_
          have hcc : chunk k 0 < chunk j 0 := chunk0_lt_of_lt (by omega) hkj
          have htj : testBit (LeafOps.slotsMask leaf) (chunk j 0) = true := by
            rw [LeafOps.testBit_slotsMask leaf _ (chunk_lt j 0)]
            exact hjc
          have htm : testBit (LeafOps.slotsMask leaf &&& upperMask (chunk k 0)) (chunk j 0)
              = true := by
            rw [testBit_and, htj, testBit_upperMask_lt _ _ (chunk_lt j 0) hcc]; rfl
          rw [hm0, testBit_zero] at htm
          exact absurd htm (by decide)
        · rw [if_neg (fun hb => hm0 (beq_iff_eq.mp hb))] at h
          have htbm := testBit_lowestSetIdx _ hm0
          rw [testBit_and] at htbm
          obtain ⟨htbs, _⟩ := and_split htbm
          rw [LeafOps.testBit_slotsMask leaf _ (lowestSetIdx_lt _ hm0),
              LeafOps.contains_eq_isSome] at htbs
          cases hg : LeafOps.get? leaf
              (lowestSetIdx (LeafOps.slotsMask leaf &&& upperMask (chunk k 0))) with
          | none => rw [hg] at htbs; simp at htbs
          | some v' => rw [hg] at h; exact absurd h (by simp)
      · exact Nat.le_of_lt (lt_of_shiftRight_lt (n := 5) (by omega))
  | .bin pfx level mask kids => fun hwf k h j hj => by
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, hpc, hwfk, hnn, hal⟩ := hwf'
      simp only [entryGT?] at h
      rw [contains_bin, Bool.and_eq_true] at hj
      obtain ⟨htj, hjc⟩ := hj
      obtain ⟨_, hpj⟩ := hal (chunk j level) (chunk_lt j level) htj j hjc
      rcases Nat.lt_trichotomy (prefixAbove k level) pfx with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        have hsome := isSome_minEntry? (.bin pfx level mask kids) hwf (by simp)
        rw [h] at hsome
        simp at hsome
      · rw [if_neg (by omega), if_neg (by omega)] at h
        have hcA : ∀ (hb : arrayIndex mask (chunk j level) < kids.size),
            childAt mask kids (chunk j level) = kids[arrayIndex mask (chunk j level)]'hb := by
          intro hb
          unfold childAt; rw [Array.getElem?_eq_getElem hb, Option.getD_some]
        have habove : ∀ (h' : minEntryAbove mask kids (chunk k level) = none),
            ¬ (chunk k level < chunk j level) := by
          intro h' hcc
          have hm0 := minEntryAbove_eq_none pfx level mask kids hwf (chunk k level) h'
          have htm : testBit (mask &&& upperMask (chunk k level)) (chunk j level) = true := by
            rw [testBit_and, htj, testBit_upperMask_lt _ _ (chunk_lt j level) hcc]; rfl
          rw [hm0, testBit_zero] at htm
          exact absurd htm (by decide)
        by_cases htb : testBit mask (chunk k level) = true
        · rw [if_pos htb] at h
          have hb : arrayIndex mask (chunk k level) < kids.size := by
            rw [hsz]; exact arrayIndex_lt mask _ htb
          rw [dif_pos hb] at h
          cases ho : entryGT? k (kids[arrayIndex mask (chunk k level)]'hb) with
          | some e =>
            rw [ho] at h
            replace h : some e = none := h
            exact absurd h (by simp)
          | none =>
            rw [ho] at h
            replace h : minEntryAbove mask kids (chunk k level) = none := h
            by_cases heqc : chunk j level = chunk k level
            · rw [heqc] at hjc htj
              have hb' : arrayIndex mask (chunk k level) < kids.size := hb
              rw [show childAt mask kids (chunk k level)
                    = kids[arrayIndex mask (chunk k level)]'hb from by
                  unfold childAt; rw [Array.getElem?_eq_getElem hb, Option.getD_some]] at hjc
              exact le_of_entryGT?_eq_none _ (hwfk _ (Array.getElem_mem hb)) k ho j hjc
            · refine Nat.not_lt.mp fun hkj => ?_
              have hcc : chunk k level ≤ chunk j level :=
                chunk_le_of_le level (hpe.trans hpj.symm) (Nat.le_of_lt hkj)
              have hccs : chunk k level < chunk j level := by
                rcases UInt32.lt_or_lt_of_ne (fun hh => heqc hh.symm) with hlt' | hgt'
                · exact hlt'
                · exact absurd (UInt32.le_iff_toNat_le.mp hcc)
                    (by have := UInt32.lt_iff_toNat_lt.mp hgt'; omega)
              exact habove h hccs
        · rw [if_neg htb] at h
          by_cases heqc : chunk j level = chunk k level
          · rw [heqc] at htj
            exact absurd htj htb
          · refine Nat.not_lt.mp fun hkj => ?_
            have hcc : chunk k level ≤ chunk j level :=
              chunk_le_of_le level (hpe.trans hpj.symm) (Nat.le_of_lt hkj)
            have hccs : chunk k level < chunk j level := by
              rcases UInt32.lt_or_lt_of_ne (fun hh => heqc hh.symm) with hlt' | hgt'
              · exact hlt'
              · exact absurd (UInt32.le_iff_toNat_le.mp hcc)
                  (by have := UInt32.lt_iff_toNat_lt.mp hgt'; omega)
            exact habove h hccs
      · rw [← hpj] at hgt
        exact Nat.le_of_lt (lt_of_shiftRight_lt hgt)
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- `entryGT?` returns the *least* key beyond the query key: any present `j > k` is at or above
the answer. With `entryGT?_gt` and `get?_of_entryGT?`, this pins the successor exactly. -/
theorem entryGT?_le : (t : PTree L) → WF t → ∀ (k j' : Nat) (v : V) (j : Nat),
    entryGT? k t = some (j', v) → contains j t = true → k < j → j' ≤ j
  | .nil => fun _ k j' v j h hj _ => by
      rw [contains_nil] at hj
      exact absurd hj (by decide)
  | .tip pfx leaf => fun hwf k j' v j h hj hkj => by
      simp only [entryGT?] at h
      have hjmem := hj
      rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hj
      obtain ⟨hj5, hjc⟩ := hj
      rcases Nat.lt_trichotomy (k >>> 5) pfx with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        exact minEntry?_le _ hwf j' v j h hjmem
      · rw [if_neg (by omega), if_neg (by omega)] at h
        by_cases hm0 : LeafOps.slotsMask leaf &&& upperMask (chunk k 0) = 0
        · rw [if_pos (beq_iff_eq.mpr hm0)] at h
          exact absurd h (by simp)
        · rw [if_neg (fun hb => hm0 (beq_iff_eq.mp hb))] at h
          obtain ⟨v', hg, hkv⟩ := Option.map_eq_some_iff.mp h
          injection hkv with hk hv
          subst hk
          have hs : lowestSetIdx (LeafOps.slotsMask leaf &&& upperMask (chunk k 0)) < 32 :=
            lowestSetIdx_lt _ hm0
          have hkhi : ((pfx <<< 5)
              ||| (lowestSetIdx (LeafOps.slotsMask leaf &&& upperMask (chunk k 0))).toNat) >>> 5
              = pfx := shiftLeft_lor_shiftRight pfx _ 5 (UInt32.lt_iff_toNat_lt.mp hs)
          have hkc : chunk ((pfx <<< 5)
              ||| (lowestSetIdx (LeafOps.slotsMask leaf &&& upperMask (chunk k 0))).toNat) 0
              = lowestSetIdx (LeafOps.slotsMask leaf &&& upperMask (chunk k 0)) :=
            chunk_shiftLeft_lor_zero pfx _ hs
          have hcc : chunk k 0 < chunk j 0 := chunk0_lt_of_lt (by omega) hkj
          have htm : testBit (LeafOps.slotsMask leaf &&& upperMask (chunk k 0)) (chunk j 0)
              = true := by
            rw [testBit_and, testBit_upperMask_lt _ _ (chunk_lt j 0) hcc,
                LeafOps.testBit_slotsMask leaf _ (chunk_lt j 0)]
            rw [hjc]; rfl
          have hle := lowestSetIdx_le_of_testBit _ _ (chunk_lt j 0) htm
          by_cases heq : lowestSetIdx (LeafOps.slotsMask leaf &&& upperMask (chunk k 0))
              = chunk j 0
          · exact Nat.le_of_eq ((key_eq_iff _ j).mpr ⟨hkhi.trans hj5.symm, by rw [hkc, heq]⟩)
          · refine Nat.le_of_lt (lt_of_chunk_lt 0 ?_ ?_)
            · show _ >>> 5 = j >>> 5
              rw [hkhi, hj5]
            · rw [hkc]
              rcases UInt32.lt_or_lt_of_ne heq with hlt' | hgt'
              · exact hlt'
              · exact absurd (UInt32.le_iff_toNat_le.mp hle)
                  (by have := UInt32.lt_iff_toNat_lt.mp hgt'; omega)
      · rw [if_neg (by omega), if_pos hgt] at h
        exact absurd h (by simp)
  | .bin pfx level mask kids => fun hwf k j' v j h hj hkj => by
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, hpc, hwfk, hnn, hal⟩ := hwf'
      simp only [entryGT?] at h
      have hjmem := hj
      rw [contains_bin, Bool.and_eq_true] at hj
      obtain ⟨htj, hjc⟩ := hj
      obtain ⟨_, hpj⟩ := hal (chunk j level) (chunk_lt j level) htj j hjc
      rcases Nat.lt_trichotomy (prefixAbove k level) pfx with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        exact minEntry?_le _ hwf j' v j h hjmem
      · rw [if_neg (by omega), if_neg (by omega)] at h
        have hccle : chunk k level ≤ chunk j level :=
          chunk_le_of_le level (hpe.trans hpj.symm) (Nat.le_of_lt hkj)
        have hfall : ∀ (h' : minEntryAbove mask kids (chunk k level) = some (j', v)),
            chunk k level < chunk j level → j' ≤ j := fun h' hccs =>
          (minEntryAbove_spec pfx level mask kids hwf (chunk k level)
            (chunk_lt k level) j' v h').2.2 j hjmem hccs
        have hstrict : chunk j level ≠ chunk k level → chunk k level < chunk j level := by
          intro hne
          rcases UInt32.lt_or_lt_of_ne (fun hh => hne hh.symm) with hlt' | hgt'
          · exact hlt'
          · exact absurd (UInt32.le_iff_toNat_le.mp hccle)
              (by have := UInt32.lt_iff_toNat_lt.mp hgt'; omega)
        by_cases htb : testBit mask (chunk k level) = true
        · rw [if_pos htb] at h
          have hb : arrayIndex mask (chunk k level) < kids.size := by
            rw [hsz]; exact arrayIndex_lt mask _ htb
          rw [dif_pos hb] at h
          have hcA : childAt mask kids (chunk k level)
              = kids[arrayIndex mask (chunk k level)]'hb := by
            unfold childAt; rw [Array.getElem?_eq_getElem hb, Option.getD_some]
          cases ho : entryGT? k (kids[arrayIndex mask (chunk k level)]'hb) with
          | some e =>
            rw [ho] at h
            replace h : some e = some (j', v) := h
            injection h with he
            subst he
            by_cases heqc : chunk j level = chunk k level
            · rw [heqc, hcA] at hjc
              exact entryGT?_le _ (hwfk _ (Array.getElem_mem hb)) k j' v j ho hjc hkj
            · have hccs := hstrict heqc
              have hget : get? j' (kids[arrayIndex mask (chunk k level)]'hb) = some v :=
                get?_of_entryGT? _ (hwfk _ (Array.getElem_mem hb)) k j' v ho
              have hmem' : contains j' (kids[arrayIndex mask (chunk k level)]'hb) = true := by
                rw [contains_eq_isSome, hget]; rfl
              have halk := hal (chunk k level) (chunk_lt k level) htb
              rw [hcA] at halk
              obtain ⟨hcj', hpj'⟩ := halk j' hmem'
              refine Nat.le_of_lt (lt_of_chunk_lt level (hpj'.trans hpj.symm) ?_)
              rw [hcj']
              exact hccs
          | none =>
            rw [ho] at h
            replace h : minEntryAbove mask kids (chunk k level) = some (j', v) := h
            by_cases heqc : chunk j level = chunk k level
            · rw [heqc, hcA] at hjc
              have hd := le_of_entryGT?_eq_none _ (hwfk _ (Array.getElem_mem hb)) k ho j hjc
              omega
            · exact hfall h (hstrict heqc)
        · rw [if_neg htb] at h
          by_cases heqc : chunk j level = chunk k level
          · rw [heqc] at htj
            exact absurd htj htb
          · exact hfall h (hstrict heqc)
      · rw [if_neg (by omega), if_pos hgt] at h
        exact absurd h (by simp)
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- The previous-sibling fallback answers correctly: a `some (j, v)` from
`maxEntryBelow mask kids c` is a real entry of the `bin`, routes strictly below slot `c`, and is
greatest among the `bin`'s keys routing strictly below `c` (the `minEntryAbove_spec` mirror). -/
private theorem maxEntryBelow_spec (pfx level : Nat) (mask : UInt32) (kids : Array (PTree L))
    (hwf : WF (.bin pfx level mask kids)) (c : UInt32) (hc : c < 32) (j : Nat) (v : V)
    (h : maxEntryBelow mask kids c = some (j, v)) :
    get? j (.bin pfx level mask kids) = some v
    ∧ chunk j level < c
    ∧ ∀ j2, contains j2 (.bin pfx level mask kids) = true → chunk j2 level < c → j2 ≤ j := by
  have hwf' := hwf
  rw [WF] at hwf'
  obtain ⟨hl, hsz, hpc, hwfk, hnn, hal⟩ := hwf'
  simp only [maxEntryBelow] at h
  by_cases hm0 : mask &&& lowerMask c = 0
  · rw [if_pos (beq_iff_eq.mpr hm0)] at h
    exact absurd h (by simp)
  · rw [if_neg (fun hb => hm0 (beq_iff_eq.mp hb))] at h
    have hs32 : highestSetIdx (mask &&& lowerMask c) < 32 := highestSetIdx_lt _ hm0
    have htbm : testBit (mask &&& lowerMask c) (highestSetIdx (mask &&& lowerMask c)) = true :=
      testBit_highestSetIdx _ hm0
    rw [testBit_and] at htbm
    obtain ⟨htbs, hlos⟩ := and_split htbm
    have hcs : highestSetIdx (mask &&& lowerMask c) < c :=
      lt_of_testBit_lowerMask c _ hc hs32 hlos
    have hbs : arrayIndex mask (highestSetIdx (mask &&& lowerMask c)) < kids.size := by
      rw [hsz]; exact arrayIndex_lt mask _ htbs
    have hcA : childAt mask kids (highestSetIdx (mask &&& lowerMask c))
        = kids[arrayIndex mask (highestSetIdx (mask &&& lowerMask c))]'hbs := by
      unfold childAt; rw [Array.getElem?_eq_getElem hbs, Option.getD_some]
    have hwfc : WF (childAt mask kids (highestSetIdx (mask &&& lowerMask c))) := by
      rw [hcA]; exact hwfk _ (Array.getElem_mem hbs)
    have hget : get? j (childAt mask kids (highestSetIdx (mask &&& lowerMask c))) = some v :=
      get?_of_maxEntry? _ hwfc j v h
    have hmem : contains j (childAt mask kids (highestSetIdx (mask &&& lowerMask c))) = true := by
      rw [contains_eq_isSome, hget]; rfl
    obtain ⟨hcj, hpj⟩ := hal (highestSetIdx (mask &&& lowerMask c)) hs32 htbs j hmem
    refine ⟨?_, ?_, ?_⟩
    · rw [get?_bin, hcj, if_pos htbs]
      exact hget
    · rw [hcj]; exact hcs
    · intro j2 hj2 hcj2
      rw [contains_bin, Bool.and_eq_true] at hj2
      obtain ⟨htj2, hj2c⟩ := hj2
      have htm2 : testBit (mask &&& lowerMask c) (chunk j2 level) = true := by
        rw [testBit_and, htj2, testBit_lowerMask_lt c _ hc hcj2]; rfl
      have hle2 : chunk j2 level ≤ highestSetIdx (mask &&& lowerMask c) :=
        le_highestSetIdx_of_testBit _ _ (chunk_lt j2 level) htm2
      obtain ⟨_, hpj2⟩ := hal (chunk j2 level) (chunk_lt j2 level) htj2 j2 hj2c
      by_cases heq2 : chunk j2 level = highestSetIdx (mask &&& lowerMask c)
      · rw [heq2] at hj2c
        exact le_maxEntry? _ hwfc j v j2 h hj2c
      · refine Nat.le_of_lt (lt_of_chunk_lt level (hpj2.trans hpj.symm) ?_)
        rw [hcj]
        rcases UInt32.lt_or_lt_of_ne heq2 with hlt | hgt
        · exact hlt
        · exact absurd (UInt32.le_iff_toNat_le.mp hle2)
            (by have := UInt32.lt_iff_toNat_lt.mp hgt; omega)

/-- A `none` fallback answer means no present slot lies strictly below `c` at all. -/
private theorem maxEntryBelow_eq_none (pfx level : Nat) (mask : UInt32) (kids : Array (PTree L))
    (hwf : WF (.bin pfx level mask kids)) (c : UInt32)
    (h : maxEntryBelow mask kids c = none) : mask &&& lowerMask c = 0 := by
  have hwf' := hwf
  rw [WF] at hwf'
  obtain ⟨hl, hsz, hpc, hwfk, hnn, hal⟩ := hwf'
  simp only [maxEntryBelow] at h
  by_cases hm0 : mask &&& lowerMask c = 0
  · exact hm0
  · rw [if_neg (fun hb => hm0 (beq_iff_eq.mp hb))] at h
    have htbm : testBit (mask &&& lowerMask c) (highestSetIdx (mask &&& lowerMask c)) = true :=
      testBit_highestSetIdx _ hm0
    rw [testBit_and] at htbm
    obtain ⟨htbs, _⟩ := and_split htbm
    have hbs : arrayIndex mask (highestSetIdx (mask &&& lowerMask c)) < kids.size := by
      rw [hsz]; exact arrayIndex_lt mask _ htbs
    have hcA : childAt mask kids (highestSetIdx (mask &&& lowerMask c))
        = kids[arrayIndex mask (highestSetIdx (mask &&& lowerMask c))]'hbs := by
      unfold childAt; rw [Array.getElem?_eq_getElem hbs, Option.getD_some]
    have hsome : (maxEntry? (childAt mask kids (highestSetIdx (mask &&& lowerMask c)))).isSome
        = true := by
      rw [hcA]
      exact isSome_maxEntry? _ (hwfk _ (Array.getElem_mem hbs)) (hnn _ (Array.getElem_mem hbs))
    rw [h] at hsome
    simp at hsome

/-- The entry `entryLT?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_entryLT? : (t : PTree L) → WF t → ∀ (k j : Nat) (v : V),
    entryLT? k t = some (j, v) → get? j t = some v
  | .nil => fun _ k j v h => by
      rw [entryLT?] at h
      exact absurd h (by simp)
  | .tip pfx leaf => fun hwf k j v h => by
      simp only [entryLT?] at h
      rcases Nat.lt_trichotomy pfx (k >>> 5) with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        exact get?_of_maxEntry? _ hwf j v h
      · rw [if_neg (by omega), if_neg (by omega)] at h
        by_cases hm0 : LeafOps.slotsMask leaf &&& lowerMask (chunk k 0) = 0
        · rw [if_pos (beq_iff_eq.mpr hm0)] at h
          exact absurd h (by simp)
        · rw [if_neg (fun hb => hm0 (beq_iff_eq.mp hb))] at h
          obtain ⟨v', hg, hkv⟩ := Option.map_eq_some_iff.mp h
          injection hkv with hk hv
          subst hk hv
          have hs : highestSetIdx (LeafOps.slotsMask leaf &&& lowerMask (chunk k 0)) < 32 :=
            highestSetIdx_lt _ hm0
          rw [get?_tip,
              if_pos (beq_iff_eq.mpr (shiftLeft_lor_shiftRight pfx _ 5
                (UInt32.lt_iff_toNat_lt.mp hs))),
              chunk_shiftLeft_lor_zero pfx _ hs]
          exact hg
      · rw [if_neg (by omega), if_pos hgt] at h
        exact absurd h (by simp)
  | .bin pfx level mask kids => fun hwf k j v h => by
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, hpc, hwfk, hnn, hal⟩ := hwf'
      simp only [entryLT?] at h
      rcases Nat.lt_trichotomy pfx (prefixAbove k level) with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        exact get?_of_maxEntry? _ hwf j v h
      · rw [if_neg (by omega), if_neg (by omega)] at h
        by_cases htb : testBit mask (chunk k level) = true
        · rw [if_pos htb] at h
          have hb : arrayIndex mask (chunk k level) < kids.size := by
            rw [hsz]; exact arrayIndex_lt mask _ htb
          rw [dif_pos hb] at h
          cases ho : entryLT? k (kids[arrayIndex mask (chunk k level)]'hb) with
          | some e =>
            rw [ho] at h
            replace h : some e = some (j, v) := h
            injection h with he
            subst he
            have hwk : WF (kids[arrayIndex mask (chunk k level)]'hb) :=
              hwfk _ (Array.getElem_mem hb)
            have ih := get?_of_entryLT? _ hwk k j v ho
            have hcA : childAt mask kids (chunk k level)
                = kids[arrayIndex mask (chunk k level)]'hb := by
              unfold childAt; rw [Array.getElem?_eq_getElem hb, Option.getD_some]
            have hmem : contains j (kids[arrayIndex mask (chunk k level)]'hb) = true := by
              rw [contains_eq_isSome, ih]; rfl
            have halk := hal (chunk k level) (chunk_lt k level) htb
            rw [hcA] at halk
            obtain ⟨hcj, _⟩ := halk j hmem
            rw [get?_bin, hcj, if_pos htb, hcA]
            exact ih
          | none =>
            rw [ho] at h
            replace h : maxEntryBelow mask kids (chunk k level) = some (j, v) := h
            exact (maxEntryBelow_spec pfx level mask kids hwf (chunk k level)
              (chunk_lt k level) j v h).1
        · rw [if_neg htb] at h
          exact (maxEntryBelow_spec pfx level mask kids hwf (chunk k level)
            (chunk_lt k level) j v h).1
      · rw [if_neg (by omega), if_pos hgt] at h
        exact absurd h (by simp)
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- `entryLT?`'s answer is strictly less than the query key (it is a *predecessor*). -/
theorem entryLT?_lt : (t : PTree L) → WF t → ∀ (k j : Nat) (v : V),
    entryLT? k t = some (j, v) → j < k
  | .nil => fun _ k j v h => by
      rw [entryLT?] at h
      exact absurd h (by simp)
  | .tip pfx leaf => fun hwf k j v h => by
      simp only [entryLT?] at h
      rcases Nat.lt_trichotomy pfx (k >>> 5) with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        have hmem : contains j (.tip pfx leaf) = true := by
          rw [contains_eq_isSome, get?_of_maxEntry? _ hwf j v h]; rfl
        have hj5 : j >>> 5 = pfx := hi_eq_of_contains_tip hmem
        exact lt_of_shiftRight_lt (n := 5) (by omega)
      · rw [if_neg (by omega), if_neg (by omega)] at h
        by_cases hm0 : LeafOps.slotsMask leaf &&& lowerMask (chunk k 0) = 0
        · rw [if_pos (beq_iff_eq.mpr hm0)] at h
          exact absurd h (by simp)
        · rw [if_neg (fun hb => hm0 (beq_iff_eq.mp hb))] at h
          obtain ⟨v', hg, hkv⟩ := Option.map_eq_some_iff.mp h
          injection hkv with hk hv
          subst hk
          have hs : highestSetIdx (LeafOps.slotsMask leaf &&& lowerMask (chunk k 0)) < 32 :=
            highestSetIdx_lt _ hm0
          have htbm := testBit_highestSetIdx _ hm0
          rw [testBit_and] at htbm
          obtain ⟨_, hlos⟩ := and_split htbm
          have hcs : highestSetIdx (LeafOps.slotsMask leaf &&& lowerMask (chunk k 0))
              < chunk k 0 := lt_of_testBit_lowerMask _ _ (chunk_lt k 0) hs hlos
          have hkhi : ((pfx <<< 5)
              ||| (highestSetIdx (LeafOps.slotsMask leaf &&& lowerMask (chunk k 0))).toNat) >>> 5
              = pfx := shiftLeft_lor_shiftRight pfx _ 5 (UInt32.lt_iff_toNat_lt.mp hs)
          refine lt_of_chunk_lt 0 ?_ ?_
          · show _ >>> 5 = k >>> 5
            rw [hkhi, hpe]
          · rw [chunk_shiftLeft_lor_zero pfx _ hs]
            exact hcs
      · rw [if_neg (by omega), if_pos hgt] at h
        exact absurd h (by simp)
  | .bin pfx level mask kids => fun hwf k j v h => by
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, hpc, hwfk, hnn, hal⟩ := hwf'
      simp only [entryLT?] at h
      rcases Nat.lt_trichotomy pfx (prefixAbove k level) with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        have hmem : contains j (.bin pfx level mask kids) = true := by
          rw [contains_eq_isSome, get?_of_maxEntry? _ hwf j v h]; rfl
        rw [contains_bin, Bool.and_eq_true] at hmem
        obtain ⟨htj, hjc⟩ := hmem
        obtain ⟨_, hpj⟩ := hal (chunk j level) (chunk_lt j level) htj j hjc
        rw [← hpj] at hlt
        exact lt_of_shiftRight_lt hlt
      · rw [if_neg (by omega), if_neg (by omega)] at h
        have hfall : ∀ (h' : maxEntryBelow mask kids (chunk k level) = some (j, v)), j < k := by
          intro h'
          obtain ⟨hget, hclt, _⟩ := maxEntryBelow_spec pfx level mask kids hwf (chunk k level)
            (chunk_lt k level) j v h'
          have hmem : contains j (.bin pfx level mask kids) = true := by
            rw [contains_eq_isSome, hget]; rfl
          rw [contains_bin, Bool.and_eq_true] at hmem
          obtain ⟨htj, hjc⟩ := hmem
          obtain ⟨_, hpj⟩ := hal (chunk j level) (chunk_lt j level) htj j hjc
          exact lt_of_chunk_lt level (hpj.trans hpe) hclt
        by_cases htb : testBit mask (chunk k level) = true
        · rw [if_pos htb] at h
          have hb : arrayIndex mask (chunk k level) < kids.size := by
            rw [hsz]; exact arrayIndex_lt mask _ htb
          rw [dif_pos hb] at h
          cases ho : entryLT? k (kids[arrayIndex mask (chunk k level)]'hb) with
          | some e =>
            rw [ho] at h
            replace h : some e = some (j, v) := h
            injection h with he
            subst he
            exact entryLT?_lt _ (hwfk _ (Array.getElem_mem hb)) k j v ho
          | none =>
            rw [ho] at h
            replace h : maxEntryBelow mask kids (chunk k level) = some (j, v) := h
            exact hfall h
        · rw [if_neg htb] at h
          exact hfall h
      · rw [if_neg (by omega), if_pos hgt] at h
        exact absurd h (by simp)
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- A `none` from `entryLT?` is complete: nothing in the trie lies strictly below the query key. -/
theorem ge_of_entryLT?_eq_none : (t : PTree L) → WF t → ∀ (k : Nat),
    entryLT? k t = none → ∀ (j : Nat), contains j t = true → k ≤ j
  | .nil => fun _ k _ j hj => by
      rw [contains_nil] at hj
      exact absurd hj (by decide)
  | .tip pfx leaf => fun hwf k h j hj => by
      simp only [entryLT?] at h
      rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hj
      obtain ⟨hj5, hjc⟩ := hj
      rcases Nat.lt_trichotomy pfx (k >>> 5) with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        have hsome := isSome_maxEntry? (.tip pfx leaf) hwf (by simp)
        rw [h] at hsome
        simp at hsome
      · rw [if_neg (by omega), if_neg (by omega)] at h
        by_cases hm0 : LeafOps.slotsMask leaf &&& lowerMask (chunk k 0) = 0
        · refine Nat.not_lt.mp fun hjk => ?_
          have hcc : chunk j 0 < chunk k 0 := chunk0_lt_of_lt (by omega) hjk
          have htj : testBit (LeafOps.slotsMask leaf) (chunk j 0) = true := by
            rw [LeafOps.testBit_slotsMask leaf _ (chunk_lt j 0)]
            exact hjc
          have htm : testBit (LeafOps.slotsMask leaf &&& lowerMask (chunk k 0)) (chunk j 0)
              = true := by
            rw [testBit_and, htj, testBit_lowerMask_lt _ _ (chunk_lt k 0) hcc]; rfl
          rw [hm0, testBit_zero] at htm
          exact absurd htm (by decide)
        · rw [if_neg (fun hb => hm0 (beq_iff_eq.mp hb))] at h
          have htbm := testBit_highestSetIdx _ hm0
          rw [testBit_and] at htbm
          obtain ⟨htbs, _⟩ := and_split htbm
          rw [LeafOps.testBit_slotsMask leaf _ (highestSetIdx_lt _ hm0),
              LeafOps.contains_eq_isSome] at htbs
          cases hg : LeafOps.get? leaf
              (highestSetIdx (LeafOps.slotsMask leaf &&& lowerMask (chunk k 0))) with
          | none => rw [hg] at htbs; simp at htbs
          | some v' => rw [hg] at h; exact absurd h (by simp)
      · exact Nat.le_of_lt (lt_of_shiftRight_lt (n := 5) (by omega))
  | .bin pfx level mask kids => fun hwf k h j hj => by
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, hpc, hwfk, hnn, hal⟩ := hwf'
      simp only [entryLT?] at h
      rw [contains_bin, Bool.and_eq_true] at hj
      obtain ⟨htj, hjc⟩ := hj
      obtain ⟨_, hpj⟩ := hal (chunk j level) (chunk_lt j level) htj j hjc
      rcases Nat.lt_trichotomy pfx (prefixAbove k level) with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        have hsome := isSome_maxEntry? (.bin pfx level mask kids) hwf (by simp)
        rw [h] at hsome
        simp at hsome
      · rw [if_neg (by omega), if_neg (by omega)] at h
        have hbelow : ∀ (h' : maxEntryBelow mask kids (chunk k level) = none),
            ¬ (chunk j level < chunk k level) := by
          intro h' hcc
          have hm0 := maxEntryBelow_eq_none pfx level mask kids hwf (chunk k level) h'
          have htm : testBit (mask &&& lowerMask (chunk k level)) (chunk j level) = true := by
            rw [testBit_and, htj, testBit_lowerMask_lt _ _ (chunk_lt k level) hcc]; rfl
          rw [hm0, testBit_zero] at htm
          exact absurd htm (by decide)
        by_cases htb : testBit mask (chunk k level) = true
        · rw [if_pos htb] at h
          have hb : arrayIndex mask (chunk k level) < kids.size := by
            rw [hsz]; exact arrayIndex_lt mask _ htb
          rw [dif_pos hb] at h
          cases ho : entryLT? k (kids[arrayIndex mask (chunk k level)]'hb) with
          | some e =>
            rw [ho] at h
            replace h : some e = none := h
            exact absurd h (by simp)
          | none =>
            rw [ho] at h
            replace h : maxEntryBelow mask kids (chunk k level) = none := h
            by_cases heqc : chunk j level = chunk k level
            · rw [heqc] at hjc htj
              rw [show childAt mask kids (chunk k level)
                    = kids[arrayIndex mask (chunk k level)]'hb from by
                  unfold childAt; rw [Array.getElem?_eq_getElem hb, Option.getD_some]] at hjc
              exact ge_of_entryLT?_eq_none _ (hwfk _ (Array.getElem_mem hb)) k ho j hjc
            · refine Nat.not_lt.mp fun hjk => ?_
              have hcc : chunk j level ≤ chunk k level :=
                chunk_le_of_le level (hpj.trans hpe) (Nat.le_of_lt hjk)
              have hccs : chunk j level < chunk k level := by
                rcases UInt32.lt_or_lt_of_ne heqc with hlt' | hgt'
                · exact hlt'
                · exact absurd (UInt32.le_iff_toNat_le.mp hcc)
                    (by have := UInt32.lt_iff_toNat_lt.mp hgt'; omega)
              exact hbelow h hccs
        · rw [if_neg htb] at h
          by_cases heqc : chunk j level = chunk k level
          · rw [heqc] at htj
            exact absurd htj htb
          · refine Nat.not_lt.mp fun hjk => ?_
            have hcc : chunk j level ≤ chunk k level :=
              chunk_le_of_le level (hpj.trans hpe) (Nat.le_of_lt hjk)
            have hccs : chunk j level < chunk k level := by
              rcases UInt32.lt_or_lt_of_ne heqc with hlt' | hgt'
              · exact hlt'
              · exact absurd (UInt32.le_iff_toNat_le.mp hcc)
                  (by have := UInt32.lt_iff_toNat_lt.mp hgt'; omega)
            exact hbelow h hccs
      · rw [← hpj] at hgt
        exact Nat.le_of_lt (lt_of_shiftRight_lt hgt)
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- `entryLT?` returns the *greatest* key below the query key: any present `j < k` is at or below
the answer. With `entryLT?_lt` and `get?_of_entryLT?`, this pins the predecessor exactly. -/
theorem le_entryLT? : (t : PTree L) → WF t → ∀ (k j' : Nat) (v : V) (j : Nat),
    entryLT? k t = some (j', v) → contains j t = true → j < k → j ≤ j'
  | .nil => fun _ k j' v j h hj _ => by
      rw [contains_nil] at hj
      exact absurd hj (by decide)
  | .tip pfx leaf => fun hwf k j' v j h hj hjk => by
      simp only [entryLT?] at h
      have hjmem := hj
      rw [contains_tip, Bool.and_eq_true, beq_iff_eq] at hj
      obtain ⟨hj5, hjc⟩ := hj
      rcases Nat.lt_trichotomy pfx (k >>> 5) with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        exact le_maxEntry? _ hwf j' v j h hjmem
      · rw [if_neg (by omega), if_neg (by omega)] at h
        by_cases hm0 : LeafOps.slotsMask leaf &&& lowerMask (chunk k 0) = 0
        · rw [if_pos (beq_iff_eq.mpr hm0)] at h
          exact absurd h (by simp)
        · rw [if_neg (fun hb => hm0 (beq_iff_eq.mp hb))] at h
          obtain ⟨v', hg, hkv⟩ := Option.map_eq_some_iff.mp h
          injection hkv with hk hv
          subst hk
          have hs : highestSetIdx (LeafOps.slotsMask leaf &&& lowerMask (chunk k 0)) < 32 :=
            highestSetIdx_lt _ hm0
          have hkhi : ((pfx <<< 5)
              ||| (highestSetIdx (LeafOps.slotsMask leaf &&& lowerMask (chunk k 0))).toNat) >>> 5
              = pfx := shiftLeft_lor_shiftRight pfx _ 5 (UInt32.lt_iff_toNat_lt.mp hs)
          have hkc : chunk ((pfx <<< 5)
              ||| (highestSetIdx (LeafOps.slotsMask leaf &&& lowerMask (chunk k 0))).toNat) 0
              = highestSetIdx (LeafOps.slotsMask leaf &&& lowerMask (chunk k 0)) :=
            chunk_shiftLeft_lor_zero pfx _ hs
          have hcc : chunk j 0 < chunk k 0 := chunk0_lt_of_lt (by omega) hjk
          have htm : testBit (LeafOps.slotsMask leaf &&& lowerMask (chunk k 0)) (chunk j 0)
              = true := by
            rw [testBit_and, testBit_lowerMask_lt _ _ (chunk_lt k 0) hcc,
                LeafOps.testBit_slotsMask leaf _ (chunk_lt j 0)]
            rw [hjc]; rfl
          have hle := le_highestSetIdx_of_testBit _ _ (chunk_lt j 0) htm
          by_cases heq : highestSetIdx (LeafOps.slotsMask leaf &&& lowerMask (chunk k 0))
              = chunk j 0
          · exact Nat.le_of_eq
              ((key_eq_iff _ j).mpr ⟨hkhi.trans hj5.symm, by rw [hkc, heq]⟩).symm
          · refine Nat.le_of_lt (lt_of_chunk_lt 0 ?_ ?_)
            · show j >>> 5 = _ >>> 5
              rw [hkhi, hj5]
            · rw [hkc]
              rcases UInt32.lt_or_lt_of_ne heq with hlt' | hgt'
              · exact absurd (UInt32.le_iff_toNat_le.mp hle)
                  (by have := UInt32.lt_iff_toNat_lt.mp hlt'; omega)
              · exact hgt'
      · rw [if_neg (by omega), if_pos hgt] at h
        exact absurd h (by simp)
  | .bin pfx level mask kids => fun hwf k j' v j h hj hjk => by
      have hwf' := hwf
      rw [WF] at hwf'
      obtain ⟨hl, hsz, hpc, hwfk, hnn, hal⟩ := hwf'
      simp only [entryLT?] at h
      have hjmem := hj
      rw [contains_bin, Bool.and_eq_true] at hj
      obtain ⟨htj, hjc⟩ := hj
      obtain ⟨_, hpj⟩ := hal (chunk j level) (chunk_lt j level) htj j hjc
      rcases Nat.lt_trichotomy pfx (prefixAbove k level) with hlt | hpe | hgt
      · rw [if_pos hlt] at h
        exact le_maxEntry? _ hwf j' v j h hjmem
      · rw [if_neg (by omega), if_neg (by omega)] at h
        have hccle : chunk j level ≤ chunk k level :=
          chunk_le_of_le level (hpj.trans hpe) (Nat.le_of_lt hjk)
        have hfall : ∀ (h' : maxEntryBelow mask kids (chunk k level) = some (j', v)),
            chunk j level < chunk k level → j ≤ j' := fun h' hccs =>
          (maxEntryBelow_spec pfx level mask kids hwf (chunk k level)
            (chunk_lt k level) j' v h').2.2 j hjmem hccs
        have hstrict : chunk j level ≠ chunk k level → chunk j level < chunk k level := by
          intro hne
          rcases UInt32.lt_or_lt_of_ne hne with hlt' | hgt'
          · exact hlt'
          · exact absurd (UInt32.le_iff_toNat_le.mp hccle)
              (by have := UInt32.lt_iff_toNat_lt.mp hgt'; omega)
        by_cases htb : testBit mask (chunk k level) = true
        · rw [if_pos htb] at h
          have hb : arrayIndex mask (chunk k level) < kids.size := by
            rw [hsz]; exact arrayIndex_lt mask _ htb
          rw [dif_pos hb] at h
          have hcA : childAt mask kids (chunk k level)
              = kids[arrayIndex mask (chunk k level)]'hb := by
            unfold childAt; rw [Array.getElem?_eq_getElem hb, Option.getD_some]
          cases ho : entryLT? k (kids[arrayIndex mask (chunk k level)]'hb) with
          | some e =>
            rw [ho] at h
            replace h : some e = some (j', v) := h
            injection h with he
            subst he
            by_cases heqc : chunk j level = chunk k level
            · rw [heqc, hcA] at hjc
              exact le_entryLT? _ (hwfk _ (Array.getElem_mem hb)) k j' v j ho hjc hjk
            · have hccs := hstrict heqc
              have hget : get? j' (kids[arrayIndex mask (chunk k level)]'hb) = some v :=
                get?_of_entryLT? _ (hwfk _ (Array.getElem_mem hb)) k j' v ho
              have hmem' : contains j' (kids[arrayIndex mask (chunk k level)]'hb) = true := by
                rw [contains_eq_isSome, hget]; rfl
              have halk := hal (chunk k level) (chunk_lt k level) htb
              rw [hcA] at halk
              obtain ⟨hcj', hpj'⟩ := halk j' hmem'
              refine Nat.le_of_lt (lt_of_chunk_lt level (hpj.trans hpj'.symm) ?_)
              rw [hcj']
              exact hccs
          | none =>
            rw [ho] at h
            replace h : maxEntryBelow mask kids (chunk k level) = some (j', v) := h
            by_cases heqc : chunk j level = chunk k level
            · rw [heqc, hcA] at hjc
              have hd := ge_of_entryLT?_eq_none _ (hwfk _ (Array.getElem_mem hb)) k ho j hjc
              omega
            · exact hfall h (hstrict heqc)
        · rw [if_neg htb] at h
          by_cases heqc : chunk j level = chunk k level
          · rw [heqc] at htj
            exact absurd htj htb
          · exact hfall h (hstrict heqc)
      · rw [if_neg (by omega), if_pos hgt] at h
        exact absurd h (by simp)
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-! ### `erase` denotation

`get?` after `erase`: the erased key reads `none`, every other key is unchanged. Member recursion
down the one routed path. The `bin` case reuses `erase_WF_keys`' splice bookkeeping (`hset` for
how the `kids.set` reads, the keys-provenance of the recursive result for transferring `AlignedAt`
across the splice) to discharge `get?_finalize`'s routing hypothesis. -/

private theorem get?_eraseU (k : Nat) : (t : PTree L) → WF t → ∀ j,
    get? j (eraseU k t) = if j = k then none else get? j t
  | .nil => fun _ j => by
      rw [eraseU, get?_nil]
      by_cases hjk : j = k
      · rw [if_pos hjk]
      · rw [if_neg hjk]
  | .tip pfx leaf => fun hwf j => by
      rw [eraseU]
      by_cases hp : (k >>> 5 == pfx) = true
      · rw [if_pos hp]
        replace hp : k >>> 5 = pfx := by simpa using hp
        by_cases he : LeafOps.isEmpty (LeafOps.erase leaf (chunk k 0)) = true
        · -- the erased leaf emptied: every slot of `leaf` other than `chunk k 0` was empty
          rw [if_pos he, get?_nil]
          by_cases hjk : j = k
          · rw [if_pos hjk]
          · rw [if_neg hjk, get?_tip]
            by_cases hjp : (j >>> 5 == pfx) = true
            · rw [if_pos hjp]
              replace hjp : j >>> 5 = pfx := by simpa using hjp
              have hcne : chunk j 0 ≠ chunk k 0 := by
                intro hc
                exact hjk (key_eq_iff j k |>.mpr ⟨hjp.trans hp.symm, hc⟩)
              have hread := LeafOps.get?_erase (V := V) leaf (chunk k 0) (chunk j 0)
                (chunk_lt _ _) (chunk_lt _ _)
              rw [if_neg hcne] at hread
              rw [← hread, LeafOps.eq_empty_of_isEmpty _ he, LeafOps.get?_empty]
            · rw [if_neg hjp]
        · -- the leaf survives: read it through the leaf law
          rw [if_neg he, get?_tip, get?_tip]
          by_cases hjp : (j >>> 5 == pfx) = true
          · rw [if_pos hjp, if_pos hjp]
            replace hjp : j >>> 5 = pfx := by simpa using hjp
            rw [LeafOps.get?_erase (V := V) leaf (chunk k 0) (chunk j 0)
                  (chunk_lt _ _) (chunk_lt _ _)]
            by_cases hcc : chunk j 0 = chunk k 0
            · rw [if_pos hcc, if_pos (key_eq_iff j k |>.mpr ⟨hjp.trans hp.symm, hcc⟩)]
            · rw [if_neg hcc, if_neg (fun hjk => hcc (by rw [hjk]))]
          · rw [if_neg hjp, if_neg hjp]
            by_cases hjk : j = k
            · rw [if_pos hjk]
            · rw [if_neg hjk]
      · -- prefix mismatch: erasing is a no-op, and `k` reads `none` off the tip anyway
        rw [if_neg hp]
        by_cases hjk : j = k
        · subst hjk
          rw [if_pos rfl, get?_tip, if_neg hp]
        · rw [if_neg hjk]
  | .bin pfx level mask kids => fun hwf j => by
      rw [eraseU]
      by_cases hroute : ((prefixAbove k level == pfx) && testBit mask (chunk k level)) = true
      · rw [if_pos hroute]
        have hwf' := hwf
        rw [WF] at hwf'
        obtain ⟨hl, hsz, _, hwfk, _, hal⟩ := hwf'
        obtain ⟨_, htb⟩ := and_split hroute
        have hb : arrayIndex mask (chunk k level) < kids.size := by
          rw [hsz]; exact arrayIndex_lt mask _ htb
        rw [dif_pos hb]
        obtain ⟨_, ihkeys⟩ :=
          erase_WF_keys k (kids[arrayIndex mask (chunk k level)]'hb)
            (hwfk _ (Array.getElem_mem hb))
        have hcA : childAt mask kids (chunk k level)
            = kids[arrayIndex mask (chunk k level)]'hb := by
          unfold childAt; rw [Array.getElem?_eq_getElem hb, Option.getD_some]
        have hset : ∀ c, c < 32 → testBit mask c = true →
            childAt mask (kids.set (arrayIndex mask (chunk k level))
                (eraseU k (kids[arrayIndex mask (chunk k level)]'hb)) hb) c
              = if c = chunk k level
                  then eraseU k (kids[arrayIndex mask (chunk k level)]'hb)
                  else childAt mask kids c := by
          intro c hc htc
          unfold childAt
          rw [Array.getElem?_set hb]
          by_cases hcc : c = chunk k level
          · subst hcc
            rw [if_pos rfl, if_pos rfl, Option.getD_some]
          · rw [if_neg hcc,
                if_neg (arrayIndex_inj mask (chunk k level) c (chunk_lt k level) hc htb htc
                  (fun hh => hcc hh.symm))]
        have hal' : ∀ c, c < 32 → testBit mask c = true →
            AlignedAt level c pfx (childAt mask (kids.set (arrayIndex mask (chunk k level))
                (eraseU k (kids[arrayIndex mask (chunk k level)]'hb)) hb) c) := by
          intro c hc htc
          rw [hset c hc htc]
          by_cases hcc : c = chunk k level
          · rw [if_pos hcc]
            intro j2 hj2
            obtain ⟨j', hj', h5⟩ := ihkeys j2 hj2
            have hj'A : contains j' (childAt mask kids c) = true := by
              rw [hcc, hcA]; exact hj'
            obtain ⟨hch, hpf⟩ := hal c hc htc j' hj'A
            exact ⟨(chunk_eq_of_hi level hl h5).trans hch,
                   (prefixAbove_eq_of_hi level h5).trans hpf⟩
          · rw [if_neg hcc]
            exact hal c hc htc
        rw [get?_finalize j pfx level mask _ hal', get?_bin]
        by_cases htj : testBit mask (chunk j level) = true
        · rw [if_pos htj, hset (chunk j level) (chunk_lt _ _) htj]
          by_cases hcc : chunk j level = chunk k level
          · rw [if_pos hcc,
                get?_eraseU k (kids[arrayIndex mask (chunk k level)]'hb)
                  (hwfk _ (Array.getElem_mem hb)) j]
            by_cases hjk : j = k
            · rw [if_pos hjk, if_pos hjk]
            · rw [if_neg hjk, if_neg hjk, if_pos htj, hcc, hcA]
          · have hjk : j ≠ k := fun he => hcc (by rw [he])
            rw [if_neg hcc, if_neg hjk, if_pos htj]
        · rw [if_neg htj]
          have hjk : j ≠ k := by
            intro he; rw [he] at htj; exact htj htb
          rw [if_neg hjk, if_neg htj]
      · -- off the routed path: erasing is a no-op, and `k` reads `none` off this branch anyway
        rw [if_neg hroute]
        by_cases hjk : j = k
        · subst hjk
          rw [if_pos rfl, get?_bin]
          by_cases htb : testBit mask (chunk j level) = true
          · rw [if_pos htb]
            have hpe : ¬(prefixAbove j level = pfx) := by
              intro hpe2
              exact hroute (by simp [hpe2, htb])
            have hwf' := hwf
            rw [WF] at hwf'
            obtain ⟨_, _, _, _, _, hal⟩ := hwf'
            have hcontains : contains j (childAt mask kids (chunk j level)) = false := by
              cases hc : contains j (childAt mask kids (chunk j level)) with
              | false => rfl
              | true =>
                obtain ⟨_, hpf⟩ := hal (chunk j level) (chunk_lt _ _) htb j hc
                exact absurd hpf hpe
            rw [contains_eq_isSome] at hcontains
            cases hg : get? j (childAt mask kids (chunk j level)) with
            | none => rfl
            | some v => rw [hg] at hcontains; simp at hcontains
          · rw [if_neg htb]
        · rw [if_neg hjk]
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hb); omega

/-- `get?` after `erase`: the erased key reads `none`, every other key is unchanged — the
denotational equation for `erase` (with `WF_erase`, it pins `erase` exactly). -/
theorem get?_erase (k : Nat) (t : PTree L) (hwf : WF t) (j : Nat) :
    get? j (erase k t) = if j = k then none else get? j t :=
  get?_eraseU k t hwf j

/-! ### Range-restriction denotation

`get?` after `filterLt`/`filterGE`: a key reads through exactly when it is on the kept side of
the bound. Member recursion down the bound's routed path; the rebuilt `bin` reads via
`get?_finalize` + `childAt_ltKids`/`ltChild_eq` (the fold seams), with `filterLt_WF_keys`'
keys-provenance transferring `AlignedAt` across the rebuilt children. The whole-subtree
prune/keep cases close by the routing invariant: a key on the wrong side of the bound is also
misaligned with the subtree, so it reads `none` off the original too. -/

/-- Shifting right is monotone (the contrapositive of `lt_of_shiftRight_lt`). -/
private theorem shiftRight_le_of_le {k j : Nat} (n : Nat) (h : k ≤ j) : k >>> n ≤ j >>> n :=
  Nat.not_lt.mp fun hlt => Nat.not_lt.mpr h (lt_of_shiftRight_lt hlt)

/-- Prefixes are monotone in the key. -/
private theorem prefixAbove_le_of_le {k j : Nat} (level : Nat) (h : k ≤ j) :
    prefixAbove k level ≤ prefixAbove j level :=
  shiftRight_le_of_le _ h

/-- A key that violates a subtree's routing alignment reads `none` off it. -/
private theorem get?_eq_none_of_misaligned (j : Nat) (level : Nat) (c : UInt32) (p : Nat)
    (t : PTree L) (halign : AlignedAt level c p t) (hne : prefixAbove j level ≠ p) :
    get? j t = none := by
  cases hg : get? j t with
  | none => rfl
  | some v =>
    have hc : contains j t = true := by
      rw [contains_eq_isSome, hg]; rfl
    exact absurd (halign j hc).2 hne

/-- A key whose prefix disagrees with a well-formed `bin` reads `none` off it: `get?` routes by
chunk alone, but the routing invariant pins every present key's prefix. -/
private theorem get?_bin_eq_none_of_prefix_ne (j pfx level : Nat) (mask : UInt32)
    (kids : Array (PTree L)) (hwf : WF (.bin pfx level mask kids))
    (hne : prefixAbove j level ≠ pfx) :
    get? j (.bin pfx level mask kids) = none := by
  rw [get?_bin]
  by_cases htb : testBit mask (chunk j level) = true
  · rw [if_pos htb]
    rw [WF] at hwf
    obtain ⟨_, _, _, _, _, hal⟩ := hwf
    exact get?_eq_none_of_misaligned j level (chunk j level) pfx _
      (hal (chunk j level) (chunk_lt _ _) htb) hne
  · rw [if_neg htb]

private theorem get?_filterLtU (k : Nat) : (t : PTree L) → WF t → ∀ j,
    get? j (filterLtU k t) = if j < k then get? j t else none
  | .nil => fun _ j => by
      rw [filterLtU, get?_nil]
      by_cases hjk : j < k
      · rw [if_pos hjk]
      · rw [if_neg hjk]
  | .tip pfx leaf => fun hwf j => by
      rw [filterLtU]
      by_cases h1 : k >>> 5 < pfx
      · -- whole tip above the bound: dropped; any j < k reads none off it anyway
        rw [if_pos h1, get?_nil]
        by_cases hjk : j < k
        · rw [if_pos hjk, get?_tip,
              if_neg (by
                intro hp
                replace hp : j >>> 5 = pfx := by simpa using hp
                have hle := shiftRight_le_of_le 5 (Nat.le_of_lt hjk)
                rw [hp] at hle
                exact Nat.not_le.mpr h1 hle)]
        · rw [if_neg hjk]
      · rw [if_neg h1]
        by_cases h2 : pfx < k >>> 5
        · -- whole tip below the bound: kept; any j ≥ k reads none off it anyway
          rw [if_pos h2]
          by_cases hjk : j < k
          · rw [if_pos hjk]
          · rw [if_neg hjk, get?_tip,
                if_neg (by
                  intro hp
                  replace hp : j >>> 5 = pfx := by simpa using hp
                  have hle := shiftRight_le_of_le 5 (Nat.not_lt.mp hjk)
                  rw [hp] at hle
                  exact Nat.not_le.mpr h2 hle)]
        · -- the bound's own leaf: keep the slots strictly below the bound's chunk
          have hpe : k >>> 5 = pfx := by omega
          rw [if_neg h2]
          by_cases he : LeafOps.isEmpty
              (LeafOps.filter (fun s _ => decide (s < chunk k 0)) leaf) = true
          · rw [if_pos he, get?_nil]
            have hread := LeafOps.get?_filter (V := V)
              (fun s _ => decide (s < chunk k 0)) leaf (chunk j 0) (chunk_lt _ _)
            rw [LeafOps.eq_empty_of_isEmpty _ he, LeafOps.get?_empty] at hread
            by_cases hjk : j < k
            · rw [if_pos hjk, get?_tip]
              by_cases hjp : (j >>> 5 == pfx) = true
              · rw [if_pos hjp]
                replace hjp : j >>> 5 = pfx := by simpa using hjp
                have hclt : chunk j 0 < chunk k 0 :=
                  chunk0_lt_of_lt (hjp.trans hpe.symm) hjk
                cases hg : LeafOps.get? (V := V) leaf (chunk j 0) with
                | none => rfl
                | some v =>
                  rw [hg] at hread
                  simp [hclt] at hread
              · rw [if_neg hjp]
            · rw [if_neg hjk]
          · rw [if_neg he, get?_tip, get?_tip]
            by_cases hjp : (j >>> 5 == pfx) = true
            · rw [if_pos hjp, if_pos hjp,
                  LeafOps.get?_filter (V := V)
                    (fun s _ => decide (s < chunk k 0)) leaf (chunk j 0) (chunk_lt _ _)]
              replace hjp : j >>> 5 = pfx := by simpa using hjp
              by_cases hclt : chunk j 0 < chunk k 0
              · have hjk : j < k :=
                  lt_of_chunk_lt 0
                    (show prefixAbove j 0 = prefixAbove k 0 from hjp.trans hpe.symm) hclt
                rw [if_pos hjk]
                cases hg : LeafOps.get? (V := V) leaf (chunk j 0) with
                | none => rfl
                | some v => simp [hclt]
              · have hjk : ¬(j < k) :=
                  fun hjk => hclt (chunk0_lt_of_lt (hjp.trans hpe.symm) hjk)
                rw [if_neg hjk]
                cases hg : LeafOps.get? (V := V) leaf (chunk j 0) with
                | none => rfl
                | some v => simp [hclt]
            · rw [if_neg hjp, if_neg hjp]
              by_cases hjk : j < k
              · rw [if_pos hjk]
              · rw [if_neg hjk]
  | .bin pfx level mask kids => fun hwf j => by
      rw [filterLtU]
      by_cases h1 : prefixAbove k level < pfx
      · -- whole branch above the bound: dropped; any j < k is misaligned with it anyway
        rw [if_pos h1, get?_nil]
        by_cases hjk : j < k
        · rw [if_pos hjk,
              get?_bin_eq_none_of_prefix_ne j pfx level mask kids hwf
                (fun hp => Nat.not_le.mpr h1
                  (hp ▸ prefixAbove_le_of_le level (Nat.le_of_lt hjk)))]
        · rw [if_neg hjk]
      · rw [if_neg h1]
        by_cases h2 : pfx < prefixAbove k level
        · -- whole branch below the bound: kept; any j ≥ k is misaligned with it anyway
          rw [if_pos h2]
          by_cases hjk : j < k
          · rw [if_pos hjk]
          · rw [if_neg hjk,
                get?_bin_eq_none_of_prefix_ne j pfx level mask kids hwf
                  (fun hp => Nat.not_le.mpr h2
                    (hp ▸ prefixAbove_le_of_le level (Nat.not_lt.mp hjk)))]
        · -- the bound's routed branch: rebuilt slot-interval-wise
          have hpe : prefixAbove k level = pfx := by omega
          rw [if_neg h2, Array.emptyWithCapacity_eq]
          have hwf' := hwf
          rw [WF] at hwf'
          obtain ⟨hl, hsz, _, hwfk, _, hal⟩ := hwf'
          have hslot : ∀ c, c < 32 → testBit mask c = true →
              WF (ltChild k level mask kids c)
              ∧ ∀ j2, contains j2 (ltChild k level mask kids c) = true →
                  ∃ j', contains j' (childAt mask kids c) = true ∧ j2 >>> 5 = j' >>> 5 := by
            intro c hc htc
            have hbc : arrayIndex mask c < kids.size := by
              rw [hsz]; exact arrayIndex_lt mask c htc
            have hcA : childAt mask kids c = kids[arrayIndex mask c]'hbc := by
              unfold childAt; rw [Array.getElem?_eq_getElem hbc, Option.getD_some]
            rw [ltChild_eq]
            by_cases hclt : c < chunk k level
            · rw [if_pos hclt, hcA]
              exact ⟨hwfk _ (Array.getElem_mem hbc), fun j2 hj2 => ⟨j2, hj2, rfl⟩⟩
            · rw [if_neg hclt]
              by_cases hceq : (c == chunk k level) = true
              · rw [if_pos hceq, hcA]
                exact filterLt_WF_keys k (kids[arrayIndex mask c]'hbc)
                  (hwfk _ (Array.getElem_mem hbc))
              · rw [if_neg hceq]
                exact ⟨by rw [WF]; trivial,
                       fun j2 hj2 => by rw [contains_nil] at hj2; exact absurd hj2 (by decide)⟩
          have hal' : ∀ c, c < 32 → testBit mask c = true →
              AlignedAt level c pfx (childAt mask (ltKids k level mask kids mask #[]) c) := by
            intro c hc htc
            rw [childAt_ltKids k level mask kids c hc htc]
            intro j2 hj2
            obtain ⟨j', hj', h5⟩ := (hslot c hc htc).2 j2 hj2
            obtain ⟨hch, hpf⟩ := hal c hc htc j' hj'
            exact ⟨(chunk_eq_of_hi level hl h5).trans hch,
                   (prefixAbove_eq_of_hi level h5).trans hpf⟩
          rw [get?_finalize j pfx level mask _ hal', get?_bin]
          by_cases hjp : prefixAbove j level = pfx
          · by_cases htj : testBit mask (chunk j level) = true
            · rw [if_pos htj, childAt_ltKids k level mask kids (chunk j level) (chunk_lt _ _) htj,
                  ltChild_eq]
              by_cases hclt : chunk j level < chunk k level
              · have hjk : j < k := lt_of_chunk_lt level (hjp.trans hpe.symm) hclt
                rw [if_pos hclt, if_pos hjk, if_pos htj]
              · rw [if_neg hclt]
                by_cases hceq : (chunk j level == chunk k level) = true
                · rw [if_pos hceq]
                  have hbc : arrayIndex mask (chunk j level) < kids.size := by
                    rw [hsz]; exact arrayIndex_lt mask _ htj
                  have hcA : childAt mask kids (chunk j level)
                      = kids[arrayIndex mask (chunk j level)]'hbc := by
                    unfold childAt; rw [Array.getElem?_eq_getElem hbc, Option.getD_some]
                  rw [hcA, get?_filterLtU k (kids[arrayIndex mask (chunk j level)]'hbc)
                        (hwfk _ (Array.getElem_mem hbc)) j]
                  by_cases hjk : j < k
                  · rw [if_pos hjk, if_pos hjk, if_pos htj]
                  · rw [if_neg hjk, if_neg hjk]
                · rw [if_neg hceq, get?_nil]
                  have hne : chunk j level ≠ chunk k level := by simpa using hceq
                  rcases UInt32.lt_or_lt_of_ne hne with h | h
                  · exact absurd h hclt
                  · have hkj : k < j := lt_of_chunk_lt level (hpe.trans hjp.symm) h
                    rw [if_neg (Nat.lt_asymm hkj)]
            · rw [if_neg htj]
              by_cases hjk : j < k
              · rw [if_pos hjk, if_neg htj]
              · rw [if_neg hjk]
          · -- j misaligned with this branch: it reads none off both the rebuilt and the original
            by_cases htj : testBit mask (chunk j level) = true
            · rw [if_pos htj,
                  get?_eq_none_of_misaligned j level (chunk j level) pfx _
                    (hal' (chunk j level) (chunk_lt _ _) htj) hjp]
              by_cases hjk : j < k
              · rw [if_pos hjk, if_pos htj,
                    get?_eq_none_of_misaligned j level (chunk j level) pfx _
                      (hal (chunk j level) (chunk_lt _ _) htj) hjp]
              · rw [if_neg hjk]
            · rw [if_neg htj]
              by_cases hjk : j < k
              · rw [if_pos hjk, if_neg htj]
              · rw [if_neg hjk]
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hbc); omega

private theorem get?_filterGEU (k : Nat) : (t : PTree L) → WF t → ∀ j,
    get? j (filterGEU k t) = if k ≤ j then get? j t else none
  | .nil => fun _ j => by
      rw [filterGEU, get?_nil]
      by_cases hjk : k ≤ j
      · rw [if_pos hjk]
      · rw [if_neg hjk]
  | .tip pfx leaf => fun hwf j => by
      rw [filterGEU]
      by_cases h1 : k >>> 5 < pfx
      · -- whole tip above the bound: kept; any j < k is misaligned with it anyway
        rw [if_pos h1]
        by_cases hjk : k ≤ j
        · rw [if_pos hjk]
        · rw [if_neg hjk, get?_tip,
              if_neg (by
                intro hp
                replace hp : j >>> 5 = pfx := by simpa using hp
                have hle := shiftRight_le_of_le 5 (Nat.le_of_lt (Nat.not_le.mp hjk))
                rw [hp] at hle
                exact Nat.not_le.mpr h1 hle)]
      · rw [if_neg h1]
        by_cases h2 : pfx < k >>> 5
        · -- whole tip below the bound: dropped; any j ≥ k is misaligned with it anyway
          rw [if_pos h2, get?_nil]
          by_cases hjk : k ≤ j
          · rw [if_pos hjk, get?_tip,
                if_neg (by
                  intro hp
                  replace hp : j >>> 5 = pfx := by simpa using hp
                  have hle := shiftRight_le_of_le 5 hjk
                  rw [hp] at hle
                  exact Nat.not_le.mpr h2 hle)]
          · rw [if_neg hjk]
        · -- the bound's own leaf: keep the slots at or above the bound's chunk
          have hpe : k >>> 5 = pfx := by omega
          rw [if_neg h2]
          by_cases he : LeafOps.isEmpty
              (LeafOps.filter (fun s _ => decide (chunk k 0 ≤ s)) leaf) = true
          · rw [if_pos he, get?_nil]
            have hread := LeafOps.get?_filter (V := V)
              (fun s _ => decide (chunk k 0 ≤ s)) leaf (chunk j 0) (chunk_lt _ _)
            rw [LeafOps.eq_empty_of_isEmpty _ he, LeafOps.get?_empty] at hread
            by_cases hjk : k ≤ j
            · rw [if_pos hjk, get?_tip]
              by_cases hjp : (j >>> 5 == pfx) = true
              · rw [if_pos hjp]
                replace hjp : j >>> 5 = pfx := by simpa using hjp
                have hcle : chunk k 0 ≤ chunk j 0 :=
                  chunk_le_of_le 0
                    (show prefixAbove k 0 = prefixAbove j 0 from hpe.trans hjp.symm) hjk
                cases hg : LeafOps.get? (V := V) leaf (chunk j 0) with
                | none => rfl
                | some v =>
                  rw [hg] at hread
                  simp [hcle] at hread
              · rw [if_neg hjp]
            · rw [if_neg hjk]
          · rw [if_neg he, get?_tip, get?_tip]
            by_cases hjp : (j >>> 5 == pfx) = true
            · rw [if_pos hjp, if_pos hjp,
                  LeafOps.get?_filter (V := V)
                    (fun s _ => decide (chunk k 0 ≤ s)) leaf (chunk j 0) (chunk_lt _ _)]
              replace hjp : j >>> 5 = pfx := by simpa using hjp
              by_cases hcle : chunk k 0 ≤ chunk j 0
              · have hjk : k ≤ j := by
                  by_cases h : k ≤ j
                  · exact h
                  · exfalso
                    have hlt := chunk0_lt_of_lt (hjp.trans hpe.symm) (Nat.not_le.mp h)
                    have h1' := UInt32.lt_iff_toNat_lt.mp hlt
                    have h2' := UInt32.le_iff_toNat_le.mp hcle
                    omega
                rw [if_pos hjk]
                cases hg : LeafOps.get? (V := V) leaf (chunk j 0) with
                | none => rfl
                | some v => simp [hcle]
              · have hjk : ¬(k ≤ j) :=
                  fun hk => hcle (chunk_le_of_le 0
                    (show prefixAbove k 0 = prefixAbove j 0 from hpe.trans hjp.symm) hk)
                rw [if_neg hjk]
                cases hg : LeafOps.get? (V := V) leaf (chunk j 0) with
                | none => rfl
                | some v => simp [hcle]
            · rw [if_neg hjp, if_neg hjp]
              by_cases hjk : k ≤ j
              · rw [if_pos hjk]
              · rw [if_neg hjk]
  | .bin pfx level mask kids => fun hwf j => by
      rw [filterGEU]
      by_cases h1 : prefixAbove k level < pfx
      · -- whole branch above the bound: kept; any j < k is misaligned with it anyway
        rw [if_pos h1]
        by_cases hjk : k ≤ j
        · rw [if_pos hjk]
        · rw [if_neg hjk,
              get?_bin_eq_none_of_prefix_ne j pfx level mask kids hwf
                (fun hp => Nat.not_le.mpr h1
                  (hp ▸ prefixAbove_le_of_le level (Nat.le_of_lt (Nat.not_le.mp hjk))))]
      · rw [if_neg h1]
        by_cases h2 : pfx < prefixAbove k level
        · -- whole branch below the bound: dropped; any j ≥ k is misaligned with it anyway
          rw [if_pos h2, get?_nil]
          by_cases hjk : k ≤ j
          · rw [if_pos hjk,
                get?_bin_eq_none_of_prefix_ne j pfx level mask kids hwf
                  (fun hp => Nat.not_le.mpr h2
                    (hp ▸ prefixAbove_le_of_le level hjk))]
          · rw [if_neg hjk]
        · -- the bound's routed branch: rebuilt slot-interval-wise
          have hpe : prefixAbove k level = pfx := by omega
          rw [if_neg h2, Array.emptyWithCapacity_eq]
          have hwf' := hwf
          rw [WF] at hwf'
          obtain ⟨hl, hsz, _, hwfk, _, hal⟩ := hwf'
          have hslot : ∀ c, c < 32 → testBit mask c = true →
              WF (geChild k level mask kids c)
              ∧ ∀ j2, contains j2 (geChild k level mask kids c) = true →
                  ∃ j', contains j' (childAt mask kids c) = true ∧ j2 >>> 5 = j' >>> 5 := by
            intro c hc htc
            have hbc : arrayIndex mask c < kids.size := by
              rw [hsz]; exact arrayIndex_lt mask c htc
            have hcA : childAt mask kids c = kids[arrayIndex mask c]'hbc := by
              unfold childAt; rw [Array.getElem?_eq_getElem hbc, Option.getD_some]
            rw [geChild_eq]
            by_cases hcgt : chunk k level < c
            · rw [if_pos hcgt, hcA]
              exact ⟨hwfk _ (Array.getElem_mem hbc), fun j2 hj2 => ⟨j2, hj2, rfl⟩⟩
            · rw [if_neg hcgt]
              by_cases hceq : (c == chunk k level) = true
              · rw [if_pos hceq, hcA]
                exact filterGE_WF_keys k (kids[arrayIndex mask c]'hbc)
                  (hwfk _ (Array.getElem_mem hbc))
              · rw [if_neg hceq]
                exact ⟨by rw [WF]; trivial,
                       fun j2 hj2 => by rw [contains_nil] at hj2; exact absurd hj2 (by decide)⟩
          have hal' : ∀ c, c < 32 → testBit mask c = true →
              AlignedAt level c pfx (childAt mask (geKids k level mask kids mask #[]) c) := by
            intro c hc htc
            rw [childAt_geKids k level mask kids c hc htc]
            intro j2 hj2
            obtain ⟨j', hj', h5⟩ := (hslot c hc htc).2 j2 hj2
            obtain ⟨hch, hpf⟩ := hal c hc htc j' hj'
            exact ⟨(chunk_eq_of_hi level hl h5).trans hch,
                   (prefixAbove_eq_of_hi level h5).trans hpf⟩
          rw [get?_finalize j pfx level mask _ hal', get?_bin]
          by_cases hjp : prefixAbove j level = pfx
          · by_cases htj : testBit mask (chunk j level) = true
            · rw [if_pos htj, childAt_geKids k level mask kids (chunk j level) (chunk_lt _ _) htj,
                  geChild_eq]
              by_cases hcgt : chunk k level < chunk j level
              · have hjk : k ≤ j :=
                  Nat.le_of_lt (lt_of_chunk_lt level (hpe.trans hjp.symm) hcgt)
                rw [if_pos hcgt, if_pos hjk, if_pos htj]
              · rw [if_neg hcgt]
                by_cases hceq : (chunk j level == chunk k level) = true
                · rw [if_pos hceq]
                  have hbc : arrayIndex mask (chunk j level) < kids.size := by
                    rw [hsz]; exact arrayIndex_lt mask _ htj
                  have hcA : childAt mask kids (chunk j level)
                      = kids[arrayIndex mask (chunk j level)]'hbc := by
                    unfold childAt; rw [Array.getElem?_eq_getElem hbc, Option.getD_some]
                  rw [hcA, get?_filterGEU k (kids[arrayIndex mask (chunk j level)]'hbc)
                        (hwfk _ (Array.getElem_mem hbc)) j]
                  by_cases hjk : k ≤ j
                  · rw [if_pos hjk, if_pos hjk, if_pos htj]
                  · rw [if_neg hjk, if_neg hjk]
                · rw [if_neg hceq, get?_nil]
                  have hne : chunk j level ≠ chunk k level := by simpa using hceq
                  rcases UInt32.lt_or_lt_of_ne hne with h | h
                  · have hjk : j < k := lt_of_chunk_lt level (hjp.trans hpe.symm) h
                    rw [if_neg (Nat.not_le.mpr hjk)]
                  · exact absurd h hcgt
            · rw [if_neg htj]
              by_cases hjk : k ≤ j
              · rw [if_pos hjk, if_neg htj]
              · rw [if_neg hjk]
          · by_cases htj : testBit mask (chunk j level) = true
            · rw [if_pos htj,
                  get?_eq_none_of_misaligned j level (chunk j level) pfx _
                    (hal' (chunk j level) (chunk_lt _ _) htj) hjp]
              by_cases hjk : k ≤ j
              · rw [if_pos hjk, if_pos htj,
                    get?_eq_none_of_misaligned j level (chunk j level) pfx _
                      (hal (chunk j level) (chunk_lt _ _) htj) hjp]
              · rw [if_neg hjk]
            · rw [if_neg htj]
              by_cases hjk : k ≤ j
              · rw [if_pos hjk, if_neg htj]
              · rw [if_neg hjk]
termination_by t => sizeOf t
decreasing_by simp_wf; have := Array.sizeOf_lt_of_mem (Array.getElem_mem hbc); omega

/-- `get?` after `filterLt`: a key reads through exactly when it is strictly below the bound. -/
theorem get?_filterLt (k : Nat) (t : PTree L) (hwf : WF t) (j : Nat) :
    get? j (filterLt k t) = if j < k then get? j t else none :=
  get?_filterLtU k t hwf j

/-- `get?` after `filterGE`: a key reads through exactly when it is at or above the bound. -/
theorem get?_filterGE (k : Nat) (t : PTree L) (hwf : WF t) (j : Nat) :
    get? j (filterGE k t) = if k ≤ j then get? j t else none :=
  get?_filterGEU k t hwf j

end PTree
end NatCol
