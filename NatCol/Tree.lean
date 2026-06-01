import NatCol.Node

/-!
# The height-indexed trie and its generic operations

`Tree leaf h` is a uniform 32-ary trie of height `h`: a tree of height 0 is a single
`leaf`, and a tree of height `h+1` is a `Node` of height-`h` subtrees. A key's 5-bit
chunk at level `j` selects the slot at the node of height `j`, so a tree of height `h`
stores exactly the keys `< 32^(h+1)`.

All operations are written once here, generically over the leaf via `LeafOps L V`, where
`V` is the value type a leaf maps slot indices to (`Unit` for sets, `α` for maps). The
instances live in `NatCol/Set.lean` and `NatCol/Map.lean`.

Height is an explicit argument so the recursions (several of which recurse *through*
`Array.foldl` / `Node.join` closures) terminate on it. Binary operations on two trees
of different heights are handled at the `NatCollection` level by lifting the shorter one
(`liftBy`/`cast`) to the common height.
-/

namespace NatCol

----------------------------------------------------------------------------------------------------
-- Implementation
----------------------------------------------------------------------------------------------------

/-- A uniform 32-ary trie of the given height. -/
abbrev Tree (leaf : Type u) : Nat → Type u
  | 0 => leaf
  | n + 1 => Node (Tree leaf n)

/-- Value-level intersection of two lookups: a key survives only if present on *both* sides.
The total-`combine` companion of `Node.optMeet`, used at the leaf/tree/collection levels where
the merge never prunes a present-on-both key. -/
def optVmeet {V : Type u} (c : V → V → V) : Option V → Option V → Option V
  | some x, some y => some (c x y)
  | _,      _      => none

/-- Value-level union of two lookups: a key survives if present on *either* side. Values present
on both are combined with `c`; a value present on one side is copied. The total-`combine` companion
of `Node.optJoin` (`combine x y = some (c x y)`), used at the leaf/tree/collection levels. -/
def optVjoin {V : Type u} (c : V → V → V) : Option V → Option V → Option V
  | some x, some y => some (c x y)
  | some x, none   => some x
  | none,   oy     => oy

/-- A leaf collection: maps 5-bit slot indices to values of type `V`. This is the single
seam that distinguishes sets (`UInt32` leaves, `V = Unit`) from maps (`Node α` leaves,
`V = α`); everything else is shared. -/
class LeafOps (L : Type u) (V : outParam (Type u)) where
  empty     : L
  isEmpty   : L → Bool
  size      : L → Nat
  get?      : L → UInt32 → Option V
  /-- Membership test at a slot, returning `Bool` directly so the lookup path avoids boxing an
  `Option` it only inspects for presence. Tied to `get?` by `contains_eq_isSome`. -/
  contains  : L → UInt32 → Bool
  insert    : L → UInt32 → V → L
  erase     : L → UInt32 → L
  modify    : L → UInt32 → (V → V) → L
  join      : (V → V → V) → L → L → L
  meet      : (V → V → V) → L → L → L
  restricts : (V → V → Bool) → L → L → Bool
  /-- Present `(slot, value)` pairs in ascending slot order. -/
  toArray   : L → Array (UInt32 × V)
  /-- Keep only the slots whose `(slot, value)` satisfies `p`. The leaf base case of
  `Tree.filter`; a fully-filtered leaf becomes empty, but that emptiness is governed at the node
  above (or the collection top), so this carries no canonical-shape obligation of its own. -/
  filter    : (UInt32 → V → Bool) → L → L
  /-- `contains` agrees with `get?`'s presence: the `Bool` fast path matches the denotational
  lookup. Lets the collection layer keep its `get?`-based membership lemmas after routing
  `contains` through the boxing-free path. -/
  contains_eq_isSome : ∀ (l : L) (i : UInt32), contains l i = (get? l i).isSome
  /-- Inserting a value yields a non-empty leaf, so freshly-built subtrees are never empty.
  Part of the canonical-shape invariant (`Tree.Full`). -/
  insert_ne_empty : ∀ (l : L) (i : UInt32) (v : V), isEmpty (insert l i v) = false
  /-- Modifying a value never changes whether a leaf is empty (it touches values, not
  presence), so `modify` preserves canonical shape. -/
  isEmpty_modify : ∀ (l : L) (i : UInt32) (g : V → V), isEmpty (modify l i g) = isEmpty l
  /-- The empty leaf reads as empty. Lets the collection layer prove `empty.isEmpty = true`,
  which the lattice identities (e.g. left identity of `join`) bottom out in. -/
  isEmpty_empty : isEmpty (empty : L) = true
  /-- An empty leaf *is* the empty leaf (the canonical converse of `isEmpty_empty`). Lets the
  collection layer recover `c = empty` from `c.isEmpty = true` at height 0, which the right
  identity of `join` (`join a empty = a`) bottoms out in. -/
  eq_empty_of_isEmpty : ∀ (l : L), isEmpty l = true → l = empty
  /-- `restricts` is reflexive on a leaf when `rel` is reflexive on values: a leaf's keys are
  trivially a subset of its own, and `rel` holds on every coinciding value. Lets the collection
  layer prove reflexivity of `restricts`. -/
  restricts_refl : ∀ (rel : V → V → Bool), (∀ x, rel x x = true) →
    ∀ (l : L), restricts rel l l = true
  /-- `join` commutes when the combine is flipped: merging `a` into `b` with `f` equals
  merging `b` into `a` with `f`'s arguments swapped. Lets the collection layer derive
  commutativity of `join`; `joinEq_comm` lifts it through the tree. -/
  join_comm : ∀ (f g : V → V → V), (∀ x y, f x y = g y x) →
    ∀ (a b : L), join f a b = join g b a
  /-- `meet` commutes when the combine is flipped (the `meet` analogue of `join_comm`). Lets the
  collection layer derive commutativity of `meet`; `meetEq_comm` lifts it through the tree. -/
  meet_comm : ∀ (f g : V → V → V), (∀ x y, f x y = g y x) →
    ∀ (a b : L), meet f a b = meet g b a
  /-- `join` is associative when the combine is associative. Lets the collection layer derive
  associativity of `join`; `joinEq_assoc` lifts it through the tree. -/
  join_assoc : ∀ (c : V → V → V), (∀ x y z, c (c x y) z = c x (c y z)) →
    ∀ (a b d : L), join c (join c a b) d = join c a (join c b d)
  /-- Joining (with any combine) onto a non-empty leaf stays non-empty. Backs
  `Tree.isEmpty_joinEq_eq_false`, which the canonical-shape side of `join` associativity needs. -/
  isEmpty_join : ∀ (c : V → V → V) (a b : L), isEmpty a = false → isEmpty (join c a b) = false
  /-- The empty leaf reads `none` everywhere. Backs the `get?`-based denotational semantics the
  `meet`-associativity proof is built against. -/
  get?_empty : ∀ (i : UInt32), get? (empty : L) i = none
  /-- `get?` reads a `meet` as the value-level intersection (`optVmeet`) of the two lookups: a
  slot survives only if present on both leaves. The leaf base case of `Tree.get?_meetEq`. Stated
  on in-range slots (`< 32`); leaf `get?` only ever reads `chunk`s, which are. -/
  get?_meet : ∀ (c : V → V → V) (a b : L) (i : UInt32), i < 32 →
    get? (meet c a b) i = optVmeet c (get? a i) (get? b i)
  /-- `get?` of an equal-height `join` is the value-level union of the two lookups. The leaf base
  case of `Tree.get?_joinEq`. -/
  get?_join : ∀ (c : V → V → V) (a b : L) (i : UInt32), i < 32 →
    get? (join c a b) i = optVjoin c (get? a i) (get? b i)
  /-- `get?` reads an `insert` pointwise: the inserted slot reads the new value, every other slot
  is unchanged. Stated on in-range slots (`< 32`); leaf `get?`/`insert` only ever touch `chunk`s,
  which are. The leaf base case of `Tree.get?_insert`. -/
  get?_insert : ∀ (l : L) (i j : UInt32) (v : V), i < 32 → j < 32 →
    get? (insert l i v) j = if j = i then some v else get? l j
  /-- A leaf is determined by its `get?` at in-range slots. The leaf base case of `Tree.ext`. -/
  get?_ext : ∀ (a b : L), (∀ i, i < 32 → get? a i = get? b i) → a = b
  /-- A non-empty leaf has a present slot (`< 32`). The leaf base case of `Tree.exists_get?`. -/
  exists_get?_of_ne_empty : ∀ (l : L), isEmpty l = false → ∃ i, i < 32 ∧ (get? l i).isSome
  /-- `restricts` reads denotationally: it holds exactly when, slot by slot, a present left value
  forces a related right value (`optRel`). The reflexivity hypothesis lets the *set* leaf — whose
  `restricts` discards `rel`, comparing only the bitsets — still satisfy this (its sole value is
  `()`, so reflexivity makes `rel` vacuous on shared slots). The leaf base case of
  `Tree.restrictsEq_iff`, which drives `restricts` transitivity. -/
  get?_restricts : ∀ (rel : V → V → Bool), (∀ x, rel x x = true) → ∀ (a b : L),
    (restricts rel a b = true ↔ ∀ i, i < 32 → optRel rel (get? a i) (get? b i) = true)

namespace Tree

variable {L : Type u} {V : Type u} [LeafOps L V]

/-- The empty tree of a given height. -/
def empty : (h : Nat) → Tree L h
  | 0 => LeafOps.empty
  | _ + 1 => Node.empty

/-- Is the tree empty? (For canonical trees only the leaf or the top node can be empty.) -/
@[specialize] def isEmpty : (h : Nat) → Tree L h → Bool
  | 0, l => LeafOps.isEmpty l
  | _ + 1, n => Node.isEmpty n

/-- Number of keys present. -/
@[specialize] def size : (h : Nat) → Tree L h → Nat
  | 0, l => LeafOps.size l
  | h + 1, n => n.elements.foldl (fun acc c => acc + size h c) 0
termination_by h => h

/-- Look up the value at key `k`. -/
@[specialize] def get? (k : Nat) : (h : Nat) → Tree L h → Option V
  | 0, l => LeafOps.get? l (chunk k 0)
  | h + 1, n =>
    match Node.get? n (chunk k (h + 1)) with
    | some child => get? k h child
    | none => none
termination_by h => h

/-- Is key `k` present? The `Bool` companion of `get?`: it descends with a `testBit` + total
`Node.get` at each level rather than `Node.get?`, so no `Option` is boxed on the path. Tied to
`get?` by `contains_eq_isSome`. -/
@[specialize] def contains (k : Nat) : (h : Nat) → Tree L h → Bool
  | 0, l => LeafOps.contains l (chunk k 0)
  | h + 1, n =>
    if hp : testBit n.positionsMask (chunk k (h + 1)) = true then
      contains k h (n.get (chunk k (h + 1)) hp)
    else false
termination_by h => h

/-- A tree of the given height holding the single key `k` ↦ `v`. -/
@[specialize] def singleton (k : Nat) (v : V) : (h : Nat) → Tree L h
  | 0 => LeafOps.insert LeafOps.empty (chunk k 0) v
  | h + 1 => Node.singleton (chunk k (h + 1)) (singleton k v h)
termination_by h => h

/-- Insert / overwrite key `k` ↦ `v`. Assumes `h` is large enough to hold `k`
(the `NatCollection` layer grows the height first when needed). -/
@[specialize] def insert (k : Nat) (v : V) : (h : Nat) → Tree L h → Tree L h
  | 0, l => LeafOps.insert l (chunk k 0) v
  | h + 1, n => n.alter (chunk k (h + 1)) fun
      | some child => some (insert k v h child)
      | none => some (singleton k v h)
termination_by h => h

/-- Closure-free `insert`, equal to it (`insertImpl_eq_insert`) but cheaper to run: the node case
matches the present-bit once and updates in place via `Node.setChild`/`insertChild`, avoiding the
`Node.alter` `Option → Option` callback (which boxes the old child only to discard it). This is the
version the collection layer runs; `insert` stays the proof-facing specification. -/
@[specialize] def insertImpl (k : Nat) (v : V) : (h : Nat) → Tree L h → Tree L h
  | 0, l => LeafOps.insert l (chunk k 0) v
  | h + 1, n =>
    if hp : testBit n.positionsMask (chunk k (h + 1)) = true then
      n.setChild (chunk k (h + 1)) (insertImpl k v h (n.get (chunk k (h + 1)) hp))
    else
      n.insertChild (chunk k (h + 1)) (by simpa using hp) (singleton k v h)
termination_by h => h

/-- Erase key `k`, pruning subtrees that become empty (keeps the tree canonical below
the top level). -/
@[specialize] def erase (k : Nat) : (h : Nat) → Tree L h → Tree L h
  | 0, l => LeafOps.erase l (chunk k 0)
  | h + 1, n => n.alter (chunk k (h + 1)) fun
      | some child =>
        let c := erase k h child
        if isEmpty h c then none else some c
      | none => none
termination_by h => h

/-- Apply `f` to the value at key `k`, if present. -/
@[specialize] def modify (k : Nat) (f : V → V) : (h : Nat) → Tree L h → Tree L h
  | 0, l => LeafOps.modify l (chunk k 0) f
  | h + 1, n => n.alter (chunk k (h + 1)) fun
      | some child => some (modify k f h child)
      | none => none
termination_by h => h

/-- Lift a tree up by `d` levels (wrapping it under slot 0). Cast-free: the result type
`Tree L (h + d)` lines up definitionally because `h + (d+1)` reduces to `(h + d) + 1`. -/
@[specialize] def liftBy : (d : Nat) → {h : Nat} → Tree L h → Tree L (h + d)
  | 0, _, t => t
  | _ + 1, _, t => Node.singleton 0 (liftBy _ t)

/-- Transport a tree along a proof of equal heights (compiles to the identity). -/
def cast {ha hb : Nat} (h : ha = hb) (t : Tree L ha) : Tree L hb := h ▸ t

/-- Union of two equal-height trees. Children present on only one side are reused by
`Node.join` without recursion; shared children are merged recursively, combining leaf
values with `c`.

The recursive merge is guarded by `if isEmpty … then none`, exactly like `meetEq`. For
canonical (non-empty) children this guard never fires — a union is never empty — so it does
not change behavior, but it makes "no empty subtree" (`Tree.Full`) hold by construction:
every surviving merged child is provably non-empty. -/
@[specialize] def joinEq (c : V → V → V) : (h : Nat) → Tree L h → Tree L h → Tree L h
  | 0, a, b => LeafOps.join c a b
  | h + 1, a, b => Node.join (fun x y =>
      let t := joinEq c h x y
      if isEmpty h t then none else some t) a b
termination_by h => h

/-- Intersection of two equal-height trees. Children present on only one side are dropped
by `Node.meet`; shared subtrees are intersected recursively and pruned if they become
empty. -/
@[specialize] def meetEq (c : V → V → V) : (h : Nat) → Tree L h → Tree L h → Tree L h
  | 0, a, b => LeafOps.meet c a b
  | h + 1, a, b => Node.meet (fun x y =>
      let t := meetEq c h x y
      if isEmpty h t then none else some t) a b
termination_by h => h

/-- `a` restricts `b` (equal heights): `a`'s keys are a subset of `b`'s and `rel` holds
on every coinciding value. -/
@[specialize] def restrictsEq (rel : V → V → Bool) : (h : Nat) → Tree L h → Tree L h → Bool
  | 0, a, b => LeafOps.restricts rel a b
  | h + 1, a, b => Node.restricts (fun x y => restrictsEq rel h x y) a b
termination_by h => h

/-! ### Operating a shorter tree against a taller one without lifting

A canonical tree of height `h + d` holds the keys it shares with a height-`h` tree only on its
**slot-0 spine** (`d` levels of slot-0 children); everything off that spine lies outside the
shorter tree's key range. So a binary operation between a shorter tree `s : Tree L h` and a
taller `t : Tree L (h + d)` only needs to touch `t`'s spine — no lift of `s` to the taller
height. These are the spine analogues of the equal-height kernels above. -/

/-- Union of a shorter `s` (height `h`) with a taller `t` (height `h + d`): descend `t`'s slot-0
spine to height `h`, `joinEq` there, and plug the result back in; off-spine children of `t` are
reused untouched. The `combine` order is `c (s-value) (t-value)`. The `if isEmpty` guard makes
"no empty subtree" hold by construction, exactly as in `joinEq`. -/
@[specialize] def joinSpine (c : V → V → V) (h : Nat) : (d : Nat) → Tree L h → Tree L (h + d) → Tree L (h + d)
  | 0, s, t => joinEq c h s t
  | d + 1, s, t => t.alter 0 fun
      | some child =>
          let r := joinSpine c h d s child
          if isEmpty (h + d) r then none else some r
      | none => some (liftBy d s)
termination_by d => d

/-- Intersection of a shorter `s` (height `h`) with a taller `t` (height `h + d`): only keys on
`t`'s slot-0 spine can be shared, so descend to height `h` and `meetEq` there, discarding all
off-spine structure of `t`. The result lives at the *smaller* height `h`. -/
@[specialize] def meetSpine (c : V → V → V) (h : Nat) : (d : Nat) → Tree L h → Tree L (h + d) → Tree L h
  | 0, s, t => meetEq c h s t
  | d + 1, s, t =>
      match Node.get? t 0 with
      | some child => meetSpine c h d s child
      | none => Tree.empty h
termination_by d => d

/-- `a` (height `h`) restricts a taller `b` (height `h + d`): `a`'s keys can only match on `b`'s
slot-0 spine, so descend to height `h` and `restrictsEq` there; `b`'s off-spine children are
irrelevant. If the spine runs out (`none`), `b` has no key in `a`'s range, so `a ⊆ b` iff `a` is
empty. -/
@[specialize] def restrictsSpine (rel : V → V → Bool) (h : Nat) : (d : Nat) → Tree L h → Tree L (h + d) → Bool
  | 0, a, b => restrictsEq rel h a b
  | d + 1, a, b =>
      match Node.get? b 0 with
      | some child => restrictsSpine rel h d a child
      | none => Tree.isEmpty h a
termination_by d => d

/-- Structural equality at a fixed height. For canonical trees this coincides with
logical equality. -/
def beq [BEq L] : (h : Nat) → Tree L h → Tree L h → Bool
  | 0, a, b => a == b
  | h + 1, a, b => a.positionsMask == b.positionsMask && a.elements.isEqv b.elements (beq h)
termination_by h => h

/-- Collect `(key, value)` pairs into `acc`, ascending by key. `pfx` carries the key bits
fixed by higher levels. -/
@[specialize] def toArrayAux (pfx : Nat) : (h : Nat) → Tree L h → Array (Nat × V) → Array (Nat × V)
  | 0, l, acc => (LeafOps.toArray l).foldl (fun acc (i, v) => acc.push (pfx ||| i.toNat, v)) acc
  | h + 1, n, acc =>
    n.fold (fun acc i child => toArrayAux (pfx ||| (i.toNat <<< (5 * (h + 1)))) h child acc) acc
termination_by h => h

/-- All `(key, value)` pairs, ascending by key. -/
def toArray (h : Nat) (t : Tree L h) : Array (Nat × V) := toArrayAux 0 h t #[]

/-- Fold `f` over present `(key, value)` pairs in ascending key order, threading the accumulator.
`pfx` carries the key bits fixed by higher levels (mirrors `toArrayAux`, but applies `f` directly
rather than pushing onto an array — so it folds the trie in place, with no intermediate array). -/
@[specialize] def foldAux {β : Type w} (f : β → Nat → V → β) (pfx : Nat) : (h : Nat) → Tree L h → β → β
  | 0, l, acc => (LeafOps.toArray l).foldl (fun acc (i, v) => f acc (pfx ||| i.toNat) v) acc
  | h + 1, n, acc =>
    n.fold (fun acc i child => foldAux f (pfx ||| (i.toNat <<< (5 * (h + 1)))) h child acc) acc
termination_by h => h

/-- Fold `f` over all present `(key, value)` pairs, ascending by key, starting from `init`. -/
def fold {β : Type w} (f : β → Nat → V → β) (init : β) (h : Nat) (t : Tree L h) : β :=
  foldAux f 0 h t init

/-- Monadic fold over present `(key, value)` pairs in ascending key order, threading the
accumulator through `m`. The monadic companion of `foldAux`: the leaf level folds via
`Array.foldlM`, each node level via `Node.foldM`. -/
private def foldMAux {β : Type w} {m : Type w → Type w'} [Monad m] (f : β → Nat → V → m β) (pfx : Nat) :
    (h : Nat) → Tree L h → β → m β
  | 0, l, acc => (LeafOps.toArray l).foldlM (fun acc (i, v) => f acc (pfx ||| i.toNat) v) acc
  | h + 1, n, acc =>
    n.foldM (fun acc i child => foldMAux f (pfx ||| (i.toNat <<< (5 * (h + 1)))) h child acc) acc
termination_by h => h

/-- Monadic fold over all present `(key, value)` pairs, ascending by key, starting from `init`. -/
def foldM {β : Type w} {m : Type w → Type w'} [Monad m] (f : β → Nat → V → m β) (init : β)
    (h : Nat) (t : Tree L h) : m β :=
  foldMAux f 0 h t init

/-- Whether every present `(key, value)` pair satisfies `p`, short-circuiting at the first that
fails. Mirrors `foldAux` but threads a `Bool` with early exit: a leaf scans its present pairs with
`Array.all`; a node scans its slots with `Node.all`, stopping as soon as a child subtree fails — so
an entire subtree can be skipped without being descended. -/
@[specialize] def allAux (p : Nat → V → Bool) (pfx : Nat) : (h : Nat) → Tree L h → Bool
  | 0, l => (LeafOps.toArray l).all (fun (i, v) => p (pfx ||| i.toNat) v)
  | h + 1, n =>
    n.all (fun i child => allAux p (pfx ||| (i.toNat <<< (5 * (h + 1)))) h child)
termination_by h => h

/-- Whether every present `(key, value)` pair satisfies `p`, short-circuiting at the first failure. -/
def all (p : Nat → V → Bool) (h : Nat) (t : Tree L h) : Bool := allAux p 0 h t

/-- Whether some present `(key, value)` pair satisfies `p`, short-circuiting at the first that
holds. The `any` companion of `allAux`: a leaf scans with `Array.any`, a node with `Node.any`. -/
@[specialize] def anyAux (p : Nat → V → Bool) (pfx : Nat) : (h : Nat) → Tree L h → Bool
  | 0, l => (LeafOps.toArray l).any (fun (i, v) => p (pfx ||| i.toNat) v)
  | h + 1, n =>
    n.any (fun i child => anyAux p (pfx ||| (i.toNat <<< (5 * (h + 1)))) h child)
termination_by h => h

/-- Whether some present `(key, value)` pair satisfies `p`, short-circuiting at the first success. -/
def any (p : Nat → V → Bool) (h : Nat) (t : Tree L h) : Bool := anyAux p 0 h t

/-- Monadic `all`: whether every present `(key, value)` pair satisfies the monadic predicate `p`,
threading effects through `m` in ascending key order and short-circuiting at the first failure (a
whole subtree past it is then neither descended nor run). Mirrors `allAux` but threads `m`: a leaf
scans with `Array.allM`, a node with `Node.allM`. -/
private def allMAux {m : Type → Type w} [Monad m] (p : Nat → V → m Bool) (pfx : Nat) :
    (h : Nat) → Tree L h → m Bool
  | 0, l => (LeafOps.toArray l).allM (fun (i, v) => p (pfx ||| i.toNat) v)
  | h + 1, n =>
    n.allM (fun i child => allMAux p (pfx ||| (i.toNat <<< (5 * (h + 1)))) h child)
termination_by h => h

/-- Monadic `all` over all present `(key, value)` pairs, short-circuiting at the first failure. -/
def allM {m : Type → Type w} [Monad m] (p : Nat → V → m Bool) (h : Nat) (t : Tree L h) : m Bool :=
  allMAux p 0 h t

/-- Monadic `any`: whether some present `(key, value)` pair satisfies the monadic predicate `p`,
short-circuiting at the first that holds. The `any` companion of `allMAux`: a leaf scans with
`Array.anyM`, a node with `Node.anyM`. -/
private def anyMAux {m : Type → Type w} [Monad m] (p : Nat → V → m Bool) (pfx : Nat) :
    (h : Nat) → Tree L h → m Bool
  | 0, l => (LeafOps.toArray l).anyM (fun (i, v) => p (pfx ||| i.toNat) v)
  | h + 1, n =>
    n.anyM (fun i child => anyMAux p (pfx ||| (i.toNat <<< (5 * (h + 1)))) h child)
termination_by h => h

/-- Monadic `any` over all present `(key, value)` pairs, short-circuiting at the first success. -/
def anyM {m : Type → Type w} [Monad m] (p : Nat → V → m Bool) (h : Nat) (t : Tree L h) : m Bool :=
  anyMAux p 0 h t

/-- Keep only the present `(key, value)` pairs satisfying `p`, pruning subtrees that filter down
to empty (so the result stays canonical below the top level — exactly as `erase` does). `pfx`
carries the key bits fixed by higher levels, as in `foldAux`. A leaf filters via `LeafOps.filter`;
a node filters every child recursively (`Node.filterMap`) and drops any child that becomes empty. -/
private def filterAux (p : Nat → V → Bool) (pfx : Nat) : (h : Nat) → Tree L h → Tree L h
  | 0, l => LeafOps.filter (fun i v => p (pfx ||| i.toNat) v) l
  | h + 1, n =>
    n.filterMap (fun i child =>
      let c := filterAux p (pfx ||| (i.toNat <<< (5 * (h + 1)))) h child
      if isEmpty h c then none else some c)
termination_by h => h

/-- Keep only the present `(key, value)` pairs satisfying `p`. -/
def filter (p : Nat → V → Bool) (h : Nat) (t : Tree L h) : Tree L h := filterAux p 0 h t

/-! ### Canonical shape

`Full` is "no empty subtree": every present child, at every level, is non-empty. `TopProper`
is "no excessive height": the top node has a slot above slot 0 set (`2 ≤ positionsMask`), so
the height is minimal. Their conjunction `Canonical` is the invariant the `NatCollection`
layer carries as a proof field. Each lemma below shows one operation preserves or establishes
the relevant piece; the collection layer assembles them. -/

/-- No empty subtree: every present child, recursively, is non-empty. (Vacuous at a leaf —
a leaf's own emptiness is governed at the collection's top, not here.) -/
def Full : (h : Nat) → Tree L h → Prop
  | 0, _ => True
  | h + 1, n => ∀ c ∈ n.elements, Tree.isEmpty h c = false ∧ Full h c

/-- Height-minimal at the top: the top node has a slot ≥ 1 set, so the height cannot be
lowered. (Vacuous at a leaf.) -/
def TopProper : (h : Nat) → Tree L h → Prop
  | 0, _ => True
  | _ + 1, n => 2 ≤ n.positionsMask

/-- A canonical tree: no empty subtree and minimal height. -/
def Canonical (h : Nat) (t : Tree L h) : Prop := Full h t ∧ TopProper h t

end Tree

----------------------------------------------------------------------------------------------------
-- Theorems
----------------------------------------------------------------------------------------------------

/-- `optVmeet` is associative when the value combine is. -/
theorem optVmeet_assoc {V : Type u} (c : V → V → V) (hc : ∀ x y z, c (c x y) z = c x (c y z))
    (oa ob od : Option V) :
    optVmeet c (optVmeet c oa ob) od = optVmeet c oa (optVmeet c ob od) := by
  cases oa <;> cases ob <;> cases od <;> simp only [optVmeet]
  rw [hc]

/-- `optVmeet` with the combine's arguments flipped swaps the operands. -/
theorem optVmeet_flip {V : Type u} (c : V → V → V) (ox oy : Option V) :
    optVmeet (fun x y => c y x) oy ox = optVmeet c ox oy := by
  cases ox <;> cases oy <;> rfl

/-- A value present only on the left is copied through a `join`. -/
@[simp] theorem optVjoin_none_right {V : Type u} (c : V → V → V) (ox : Option V) :
    optVjoin c ox none = ox := by
  cases ox <;> rfl

/-- `optVjoin` with the combine's arguments flipped swaps the operands. -/
theorem optVjoin_flip {V : Type u} (c : V → V → V) (ox oy : Option V) :
    optVjoin (fun x y => c y x) oy ox = optVjoin c ox oy := by
  cases ox <;> cases oy <;> rfl

/-- `optVmeet` distributes over `optVjoin` from the left when the meet combine distributes over the
join combine pointwise (`hdist : cm x (cj y z) = cj (cm x y) (cm x z)`). One-sided keys are dropped
by `optVmeet` on both sides, so only the all-present case actually uses `hdist`. -/
theorem optVmeet_optVjoin_distrib {V : Type u} (cm cj : V → V → V)
    (hdist : ∀ x y z, cm x (cj y z) = cj (cm x y) (cm x z)) (oa ob oc : Option V) :
    optVmeet cm oa (optVjoin cj ob oc) = optVjoin cj (optVmeet cm oa ob) (optVmeet cm oa oc) := by
  cases oa <;> cases ob <;> cases oc <;> simp only [optVmeet, optVjoin] <;>
    first | rfl | rw [hdist]

/-- `optVjoin` distributes over `optVmeet` from the left, given the full lattice algebra on the
combines: the meet combine is idempotent (`hidem`) and absorbs the join combine (`habs1`/`habs2`),
and the join combine distributes over the meet combine (`hdist`). Unlike the dual law, *every*
mixed-presence case is non-trivial here, because `optVjoin` copies (rather than drops) one-sided
keys. -/
theorem optVjoin_optVmeet_distrib {V : Type u} (cj cm : V → V → V)
    (hidem : ∀ x, cm x x = x) (habs1 : ∀ x y, cm (cj x y) x = x) (habs2 : ∀ x y, cm x (cj x y) = x)
    (hdist : ∀ x y z, cj x (cm y z) = cm (cj x y) (cj x z)) (oa ob oc : Option V) :
    optVjoin cj oa (optVmeet cm ob oc) = optVmeet cm (optVjoin cj oa ob) (optVjoin cj oa oc) := by
  cases oa <;> cases ob <;> cases oc <;> simp only [optVmeet, optVjoin] <;>
    first | rfl | rw [hidem] | rw [habs1] | rw [habs2] | rw [hdist]

namespace Tree

variable {L : Type u} {V : Type u} [LeafOps L V]

/-- `beq` is reflexive at every height (given a reflexive leaf `BEq`). -/
theorem beq_refl [BEq L] [LawfulBEq L] : (h : Nat) → (t : Tree L h) → beq h t t = true := by
  intro h
  induction h with
  | zero => intro t; simp only [beq]; exact BEq.rfl
  | succ h ih =>
    intro t
    obtain ⟨m, e, _⟩ := t
    simp only [beq, Bool.and_eq_true]
    refine ⟨BEq.rfl, ?_⟩
    rw [Array.isEqv_iff_rel]
    exact ⟨rfl, fun i _ => ih e[i]⟩

/-- `beq` decides propositional equality: structurally-equal trees are equal. (This is the
heart of `LawfulBEq (NatCollection L)`; it holds for *any* tree, canonical or not.) -/
theorem eq_of_beq [BEq L] [LawfulBEq L] :
    (h : Nat) → {a b : Tree L h} → beq h a b = true → a = b := by
  intro h
  induction h with
  | zero => intro a b hb; simp only [beq] at hb; exact LawfulBEq.eq_of_beq hb
  | succ h ih =>
    intro a b hb
    obtain ⟨ma, ea, ha⟩ := a
    obtain ⟨mb, eb, hb'⟩ := b
    simp only [beq, Bool.and_eq_true] at hb
    obtain ⟨hm, he⟩ := hb
    rw [Array.isEqv_iff_rel] at he
    obtain ⟨hsize, hpt⟩ := he
    have hmeq : ma = mb := LawfulBEq.eq_of_beq hm
    have heeq : ea = eb := Array.ext hsize (fun i hi₁ _ => ih (hpt i hi₁))
    subst hmeq; subst heeq; rfl

/-- `restrictsEq` is reflexive when `rel` is reflexive on values: a tree's keys are a subset of
its own and `rel` holds on every coinciding value, at every height. Needs no canonical-shape
hypothesis — both operands are the same tree. Bottoms out in `LeafOps.restricts_refl` at a leaf
and `Node.restricts_self` at each node. -/
theorem restrictsEq_self (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) :
    (h : Nat) → (t : Tree L h) → restrictsEq rel h t t = true := by
  intro h
  induction h with
  | zero => intro l; simp only [restrictsEq]; exact LeafOps.restricts_refl rel hrefl l
  | succ h ih =>
    intro n
    simp only [restrictsEq]
    exact Node.restricts_self _ n (fun c _ => ih c)

/-- `joinEq` commutes when the combine is flipped, at every height: merging `a` into `b` with
`f` equals merging `b` into `a` with `f`'s arguments swapped. Bottoms out in `LeafOps.join_comm`
at a leaf and `Node.join_comm` at each node (the per-slot merge flips by the induction
hypothesis: the `if isEmpty` guard depends only on the recursively-merged child). -/
theorem joinEq_comm (f g : V → V → V) (hfg : ∀ x y, f x y = g y x) :
    (h : Nat) → (a b : Tree L h) → joinEq f h a b = joinEq g h b a := by
  intro h
  induction h with
  | zero => intro a b; simp only [joinEq]; exact LeafOps.join_comm f g hfg a b
  | succ h ih =>
    intro a b
    simp only [joinEq]
    refine Node.join_comm a b fun x y => ?_
    simp only [ih]

/-- `meetEq` commutes when the combine is flipped, at every height (the `meetEq` analogue of
`joinEq_comm`). Bottoms out in `LeafOps.meet_comm` at a leaf and `Node.meet_comm` at each node (the
per-slot merge flips by the induction hypothesis: the `if isEmpty` guard depends only on the
recursively-merged child). -/
theorem meetEq_comm (f g : V → V → V) (hfg : ∀ x y, f x y = g y x) :
    (h : Nat) → (a b : Tree L h) → meetEq f h a b = meetEq g h b a := by
  intro h
  induction h with
  | zero => intro a b; simp only [meetEq]; exact LeafOps.meet_comm f g hfg a b
  | succ h ih =>
    intro a b
    simp only [meetEq]
    refine Node.meet_comm a b fun x y => ?_
    simp only [ih]

/-- The empty tree has no subtrees, so it is `Full`. -/
theorem Full_empty : (h : Nat) → Full h (Tree.empty h : Tree L h)
  | 0 => trivial
  | _ + 1 => by intro c hc; simp [Tree.empty, Node.empty] at hc

/-- A singleton tree is non-empty at every height. -/
private theorem isEmpty_singleton : (h : Nat) → (k : Nat) → (v : V) →
    Tree.isEmpty h (Tree.singleton k v h : Tree L h) = false
  | 0, _, _ => by simp only [Tree.isEmpty, Tree.singleton]; exact LeafOps.insert_ne_empty _ _ _
  | _ + 1, _, _ => by simp only [Tree.isEmpty, Tree.singleton]; exact Node.isEmpty_singleton _ _

/-- A singleton tree has no empty subtree. -/
theorem Full_singleton : (h : Nat) → (k : Nat) → (v : V) → Full h (Tree.singleton k v h : Tree L h)
  | 0, _, _ => trivial
  | h + 1, k, v => by
      intro c hc
      simp only [Tree.singleton, Node.singleton, Array.mem_singleton] at hc
      subst hc
      exact ⟨isEmpty_singleton h k v, Full_singleton h k v⟩

/-- An `insert` result is never empty (it adds a key). -/
private theorem isEmpty_insert : (h : Nat) → (k : Nat) → (v : V) → (t : Tree L h) →
    Tree.isEmpty h (Tree.insert k v h t) = false
  | 0, _, _, _ => by simp only [Tree.isEmpty, Tree.insert]; exact LeafOps.insert_ne_empty _ _ _
  | h + 1, k, v, n => by
      simp only [Tree.isEmpty, Tree.insert, Node.isEmpty]
      rw [Node.positionsMask_alter_of_isSome n (chunk k (h + 1)) _
            (by cases Node.get? n (chunk k (h + 1)) <;> rfl)]
      exact beq_eq_false_iff_ne.mpr (setBit_ne_zero _ _)

/-- `insert` preserves "no empty subtree". -/
theorem Full_insert : (h : Nat) → (k : Nat) → (v : V) → (t : Tree L h) →
    Full h t → Full h (Tree.insert k v h t)
  | 0, _, _, _, _ => trivial
  | h + 1, k, v, n, hn => by
      intro c hc
      simp only [Tree.insert] at hc
      rcases Node.mem_alter n (chunk k (h + 1)) _ c hc with hmem | ⟨a, hfa, hca⟩
      · exact hn c hmem
      · subst hca
        cases hget : Node.get? n (chunk k (h + 1)) with
        | some child =>
          rw [hget] at hfa; simp only [Option.some.injEq] at hfa; subst hfa
          have hchild : Full h child := (hn child (Node.mem_of_get? n _ child hget)).2
          exact ⟨isEmpty_insert h k v child, Full_insert h k v child hchild⟩
        | none =>
          rw [hget] at hfa; simp only [Option.some.injEq] at hfa; subst hfa
          exact ⟨isEmpty_singleton h k v, Full_singleton h k v⟩

/-- `erase` preserves "no empty subtree" (it prunes any child that becomes empty). -/
theorem Full_erase : (h : Nat) → (k : Nat) → (t : Tree L h) →
    Full h t → Full h (Tree.erase k h t)
  | 0, _, _, _ => trivial
  | h + 1, k, n, hn => by
      intro c hc
      simp only [Tree.erase] at hc
      rcases Node.mem_alter n (chunk k (h + 1)) _ c hc with hmem | ⟨a, hfa, hca⟩
      · exact hn c hmem
      · subst hca
        cases hget : Node.get? n (chunk k (h + 1)) with
        | some child =>
          rw [hget] at hfa; simp only at hfa
          have hchild : Full h child := (hn child (Node.mem_of_get? n _ child hget)).2
          split at hfa
          · simp at hfa
          · rename_i hne
            simp only [Option.some.injEq] at hfa; subst hfa
            exact ⟨by simpa using hne, Full_erase h k child hchild⟩
        | none =>
          rw [hget] at hfa; simp at hfa

/-- `joinEq` preserves "no empty subtree": every merged child is guarded non-empty. -/
private theorem Full_joinEq : (h : Nat) → (c : V → V → V) → (a b : Tree L h) →
    Full h a → Full h b → Full h (joinEq c h a b)
  | 0, _, _, _, _, _ => trivial
  | h + 1, c, a, b, ha, hb => by
      simp only [joinEq]
      refine Node.join_forall (fun x hx => ha x hx) (fun y hy => hb y hy) ?_
      intro x hx y hy v hv
      simp only at hv
      split at hv
      · simp at hv
      · rename_i hne
        simp only [Option.some.injEq] at hv; subst hv
        exact ⟨by simpa using hne, Full_joinEq h c x y (ha x hx).2 (hb y hy).2⟩

/-- Joining onto a non-empty `Full` tree stays non-empty: a present key of `a` survives the merge.
Bottoms out in `LeafOps.isEmpty_join`; at a node the surviving slot is exhibited via `get?_join`
(the `if isEmpty` guard there never fires, by the induction hypothesis). -/
theorem isEmpty_joinEq_eq_false (c : V → V → V) : (h : Nat) → (a b : Tree L h) →
    Tree.isEmpty h a = false → Full h a → Full h b → Tree.isEmpty h (joinEq c h a b) = false
  | 0, a, b, hne, _, _ => by simp only [Tree.isEmpty, joinEq]; exact LeafOps.isEmpty_join c a b hne
  | h + 1, a, b, hne, ha, hb => by
      obtain ⟨s, hs, hsome⟩ := Node.exists_get?_of_isEmpty_false a hne
      obtain ⟨child, hchild⟩ := Option.isSome_iff_exists.mp hsome
      have hcf := ha child (Node.mem_of_get? a s child hchild)
      refine Node.isEmpty_eq_false_of_get? _ s ?_
      simp only [joinEq]
      rw [Node.get?_join _ _ _ _ hs, hchild]
      cases hb2 : Node.get? b s with
      | none => simp [Node.optJoin]
      | some bchild =>
          have hbf := hb bchild (Node.mem_of_get? b s bchild hb2)
          simp only [Node.optJoin]
          rw [if_neg (by simp [isEmpty_joinEq_eq_false c h child bchild hcf.1 hcf.2 hbf.2])]
          simp

/-- `joinEq` is associative at every height when the leaf combine is associative. Bottoms out in
`LeafOps.join_assoc` at a leaf; the successor step is `Node.join_assoc` for the (pruning) per-slot
combine, whose value-level associativity at each slot is discharged by the induction hypothesis —
the `if isEmpty` guards never fire on the `Full` non-empty children (`isEmpty_joinEq_eq_false`). -/
theorem joinEq_assoc (c : V → V → V) (hc : ∀ x y z, c (c x y) z = c x (c y z)) :
    (h : Nat) → (a b d : Tree L h) → Full h a → Full h b → Full h d →
      joinEq c h (joinEq c h a b) d = joinEq c h a (joinEq c h b d)
  | 0, a, b, d, _, _, _ => by simp only [joinEq]; exact LeafOps.join_assoc c hc a b d
  | h + 1, a, b, d, ha, hb, hd => by
      simp only [joinEq]
      apply Node.join_assoc
      intro s hs
      -- the per-slot combine `gC x y = if isEmpty (joinEq x y) then none else some (joinEq x y)`,
      -- pinned to `some (joinEq x y)` on non-empty `Full` children
      have key : ∀ (x y : Tree L h), Tree.isEmpty h x = false → Full h x → Full h y →
          (if Tree.isEmpty h (joinEq c h x y) then none else some (joinEq c h x y))
            = some (joinEq c h x y) :=
        fun x y hxe hfx hfy => if_neg (by simp [isEmpty_joinEq_eq_false c h x y hxe hfx hfy])
      rcases hga : Node.get? a s with _ | x
      · rcases hgb : Node.get? b s with _ | y
        · rcases hgd : Node.get? d s with _ | z <;> simp [Node.optJoin]
        · have hyf := hb y (Node.mem_of_get? b s y hgb)
          rcases hgd : Node.get? d s with _ | z
          · simp [Node.optJoin]
          · have hzf := hd z (Node.mem_of_get? d s z hgd)
            simp only [Node.optJoin, key y z hyf.1 hyf.2 hzf.2, Node.optJoin]
      · have hxf := ha x (Node.mem_of_get? a s x hga)
        rcases hgb : Node.get? b s with _ | y
        · rcases hgd : Node.get? d s with _ | z <;> simp [Node.optJoin]
        · have hyf := hb y (Node.mem_of_get? b s y hgb)
          rcases hgd : Node.get? d s with _ | z
          · simp only [Node.optJoin, key x y hxf.1 hxf.2 hyf.2, Node.optJoin]
          · have hzf := hd z (Node.mem_of_get? d s z hgd)
            simp only [Node.optJoin, key x y hxf.1 hxf.2 hyf.2, key y z hyf.1 hyf.2 hzf.2]
            rw [key (joinEq c h x y) z (isEmpty_joinEq_eq_false c h x y hxf.1 hxf.2 hyf.2)
                  (Full_joinEq h c x y hxf.2 hyf.2) hzf.2,
                key x (joinEq c h y z) hxf.1 hxf.2 (Full_joinEq h c y z hyf.2 hzf.2),
                joinEq_assoc c hc h x y z hxf.2 hyf.2 hzf.2]

/-- `meetEq` preserves "no empty subtree": every surviving child is guarded non-empty. -/
private theorem Full_meetEq : (h : Nat) → (c : V → V → V) → (a b : Tree L h) →
    Full h a → Full h b → Full h (meetEq c h a b)
  | 0, _, _, _, _, _ => trivial
  | h + 1, c, a, b, ha, hb => by
      simp only [meetEq]
      refine Node.meet_forall ?_
      intro x hx y hy v hv
      simp only at hv
      split at hv
      · simp at hv
      · rename_i hne
        simp only [Option.some.injEq] at hv; subst hv
        exact ⟨by simpa using hne, Full_meetEq h c x y (ha x hx).2 (hb y hy).2⟩

/-- `filterAux` preserves "no empty subtree": each surviving child is the guarded-non-empty
filtered subtree (the `if isEmpty` guard prunes the rest), `Full` by induction; the leaf case is
vacuous. The `filterMap` analogue of `Full_erase`/`Full_meetEq`. `pfx` is irrelevant to shape, so
it is re-quantified at the tail and structural recursion proceeds on the height. -/
private theorem Full_filterAux (p : Nat → V → Bool) :
    (h : Nat) → (t : Tree L h) → Full h t → ∀ pfx, Full h (filterAux p pfx h t)
  | 0, _, _, _ => trivial
  | h + 1, n, hn, pfx => by
      simp only [filterAux]
      refine Node.filterMap_forall ?_
      intro i hi y hy
      simp only at hy
      split at hy
      · simp at hy
      · rename_i hne
        simp only [Option.some.injEq] at hy; subst hy
        have hchild : Full h (n.get i hi) := (hn (n.get i hi) (n.get_mem i hi)).2
        exact ⟨by simpa using hne, Full_filterAux p h (n.get i hi) hchild _⟩

/-- `filter` preserves "no empty subtree". -/
theorem Full_filter (p : Nat → V → Bool) (h : Nat) (t : Tree L h) (hf : Full h t) :
    Full h (filter p h t) := Full_filterAux p h t hf 0

/-- Lifting a non-empty tree keeps it non-empty. -/
theorem isEmpty_liftBy : (d : Nat) → {h : Nat} → (t : Tree L h) →
    Tree.isEmpty h t = false → Tree.isEmpty (h + d) (liftBy d t) = false
  | 0, _, _, ht => ht
  | d + 1, _, t, _ => Node.isEmpty_singleton 0 (liftBy d t)

/-- Lifting a non-empty `Full` tree keeps it `Full` (the new slot-0 children are non-empty
copies of the original). -/
theorem Full_liftBy : (d : Nat) → {h : Nat} → (t : Tree L h) →
    Full h t → Tree.isEmpty h t = false → Full (h + d) (liftBy d t)
  | 0, _, _, hf, _ => hf
  | d + 1, _, t, hf, hne => by
      intro c hc
      simp only [liftBy, Node.singleton, Array.mem_singleton] at hc
      subst hc
      exact ⟨isEmpty_liftBy d t hne, Full_liftBy d t hf hne⟩

/-- Transporting a tree along an equality of heights preserves `Full`. -/
theorem Full_cast {ha hb : Nat} (heq : ha = hb) (t : Tree L ha) (hf : Full ha t) :
    Full hb (Tree.cast heq t) := by subst heq; exact hf

/-- Transporting a tree along an equality of heights preserves `TopProper`. -/
theorem TopProper_cast {ha hb : Nat} (heq : ha = hb) (t : Tree L ha) (htp : TopProper ha t) :
    TopProper hb (Tree.cast heq t) := by subst heq; exact htp

/-- Transporting a tree along an equality of heights preserves emptiness. -/
theorem isEmpty_cast {ha hb : Nat} (heq : ha = hb) (t : Tree L ha) :
    Tree.isEmpty hb (Tree.cast heq t) = Tree.isEmpty ha t := by subst heq; rfl

/-- `joinSpine` preserves "no empty subtree": the spine's merged child is guarded non-empty
(`some` branch) or is a lifted copy of the non-empty `s` (`none` branch); off-spine children
come straight from the `Full` taller tree. Requires `s` non-empty (its lift must stay `Full`). -/
theorem Full_joinSpine (c : V → V → V) (h : Nat) : (d : Nat) → (s : Tree L h) → (t : Tree L (h + d)) →
    Tree.isEmpty h s = false → Full h s → Full (h + d) t → Full (h + d) (joinSpine c h d s t)
  | 0, s, t, _, hs, ht => by simp only [joinSpine, Nat.add_zero]; exact Full_joinEq h c s t hs ht
  | d + 1, s, t, hsne, hs, ht => by
      simp only [joinSpine]
      intro x hx
      rcases Node.mem_alter t 0 _ x hx with hmem | ⟨a, hfa, hxa⟩
      · exact ht x hmem
      · subst hxa
        cases hget : Node.get? t 0 with
        | some child =>
            rw [hget] at hfa
            simp only at hfa
            split at hfa
            · simp at hfa
            · rename_i hne
              simp only [Option.some.injEq] at hfa; subst hfa
              have hchild : Full (h + d) child := (ht child (Node.mem_of_get? t 0 child hget)).2
              exact ⟨by simpa using hne, Full_joinSpine c h d s child hsne hs hchild⟩
        | none =>
            rw [hget] at hfa
            simp only [Option.some.injEq] at hfa; subst hfa
            exact ⟨isEmpty_liftBy d s hsne, Full_liftBy d s hs hsne⟩

/-- `meetSpine` preserves "no empty subtree": each step recurses into a `Full` spine child or
returns the empty tree (`Full_empty`); the base case is `meetEq`. -/
theorem Full_meetSpine (c : V → V → V) (h : Nat) : (d : Nat) → (s : Tree L h) → (t : Tree L (h + d)) →
    Full h s → Full (h + d) t → Full h (meetSpine c h d s t)
  | 0, s, t, hs, ht => by simp only [meetSpine]; exact Full_meetEq h c s t hs ht
  | d + 1, s, t, hs, ht => by
      simp only [meetSpine]
      split
      · rename_i child hget
        have hchild : Full (h + d) child := (ht child (Node.mem_of_get? t 0 child hget)).2
        exact Full_meetSpine c h d s child hs hchild
      · exact Full_empty h

/-- `modify` never empties a leaf, so it preserves emptiness at every height. -/
private theorem isEmpty_modify : (h : Nat) → (k : Nat) → (f : V → V) → (t : Tree L h) →
    Tree.isEmpty h (Tree.modify k f h t) = Tree.isEmpty h t
  | 0, _, _, _ => by simp only [Tree.isEmpty, Tree.modify]; exact LeafOps.isEmpty_modify _ _ _
  | h + 1, k, f, n => by
      simp only [Tree.isEmpty, Tree.modify]
      exact Node.isEmpty_alter_invariant n (chunk k (h + 1)) _ (by intro o; cases o <;> rfl)

/-- `modify` preserves "no empty subtree" (it changes values, not structure). -/
theorem Full_modify : (h : Nat) → (k : Nat) → (f : V → V) → (t : Tree L h) →
    Full h t → Full h (Tree.modify k f h t)
  | 0, _, _, _, _ => trivial
  | h + 1, k, f, n, hn => by
      intro c hc
      simp only [Tree.modify] at hc
      rcases Node.mem_alter n (chunk k (h + 1)) _ c hc with hmem | ⟨a, hfa, hca⟩
      · exact hn c hmem
      · subst hca
        cases hget : Node.get? n (chunk k (h + 1)) with
        | some child =>
          rw [hget] at hfa; simp only [Option.some.injEq] at hfa; subst hfa
          have hchild := hn child (Node.mem_of_get? n _ child hget)
          refine ⟨?_, Full_modify h k f child hchild.2⟩
          rw [isEmpty_modify h k f child]; exact hchild.1
        | none =>
          rw [hget] at hfa; simp at hfa

/-! ### `get?` characterization of `meet` and tree extensionality

The `meet`-associativity proof is denotational: it reads `meet` off `get?` and uses that two
canonical trees agreeing on every `get?` are equal. `get?_meetEq`/`get?_meetSpine` characterize
the equal-height and spine merges as `optVmeet`; `Tree.ext` recovers a tree from its `get?` by
probing keys whose top chunk selects a given slot (`chunk_probe_*`). -/

/-- `Tree.get?` unfolded one level (the defining equation at a successor height). -/
theorem get?_succ (k h : Nat) (n : Tree L (h + 1)) :
    Tree.get? k (h + 1) n
      = match Node.get? n (chunk k (h + 1)) with
        | some child => Tree.get? k h child
        | none => none := by
  simp only [Tree.get?]

/-- `Tree.get?` through a present top slot descends into that child. -/
private theorem get?_succ_some (k h : Nat) (n : Tree L (h + 1)) (child : Tree L h)
    (hc : Node.get? n (chunk k (h + 1)) = some child) : Tree.get? k (h + 1) n = Tree.get? k h child := by
  rw [get?_succ, hc]

/-- `Tree.get?` through an absent top slot is `none`. -/
private theorem get?_succ_none (k h : Nat) (n : Tree L (h + 1))
    (hc : Node.get? n (chunk k (h + 1)) = none) : Tree.get? k (h + 1) n = none := by
  rw [get?_succ, hc]

/-- The `Bool` lookup `contains` agrees with `get?`'s presence at every height. Lets the
collection layer route membership through the boxing-free path while keeping all its
`get?`-based lemmas. -/
theorem contains_eq_isSome (k : Nat) : (h : Nat) → (t : Tree L h) →
    Tree.contains k h t = (Tree.get? k h t).isSome
  | 0, l => by
    simp only [Tree.contains, Tree.get?]; exact LeafOps.contains_eq_isSome l (chunk k 0)
  | h + 1, n => by
    rw [get?_succ]
    simp only [Tree.contains]
    by_cases hp : testBit n.positionsMask (chunk k (h + 1)) = true
    · rw [dif_pos hp, show Node.get? n (chunk k (h + 1)) = some (n.get (chunk k (h + 1)) hp) from
        dif_pos hp]
      exact contains_eq_isSome k h (n.get (chunk k (h + 1)) hp)
    · rw [dif_neg hp, show Node.get? n (chunk k (h + 1)) = none from dif_neg hp]
      rfl

/-- `Tree.get?` commutes with a height cast. -/
@[simp] theorem get?_cast {ha hb : Nat} (p : ha = hb) (k : Nat) (t : Tree L ha) :
    Tree.get? k hb (Tree.cast p t) = Tree.get? k ha t := by subst p; rfl

/-- The empty tree reads `none` everywhere. -/
theorem get?_empty (k : Nat) : (h : Nat) → Tree.get? k h (Tree.empty h : Tree L h) = none
  | 0 => by simp only [Tree.get?, Tree.empty]; exact LeafOps.get?_empty _
  | _ + 1 => by simp only [Tree.empty, get?_succ, Node.get?_empty]

/-- A tree that is empty reads `none` everywhere (even off the top slot). -/
theorem get?_eq_none_of_isEmpty (k : Nat) : (h : Nat) → (t : Tree L h) →
    Tree.isEmpty h t = true → Tree.get? k h t = none
  | 0, l, hl => by
      simp only [Tree.get?]
      rw [LeafOps.eq_empty_of_isEmpty l hl, LeafOps.get?_empty]
  | h + 1, n, hn => by
      simp only [Tree.isEmpty] at hn
      simp only [get?_succ, Node.get?_eq_none_of_isEmpty n hn]

/-- `Tree.get?` depends on a key only through its chunks `0..h`, so keys agreeing there look up
the same value. -/
private theorem get?_congr (k₁ k₂ : Nat) : (h : Nat) → (t : Tree L h) →
    (∀ j, j ≤ h → chunk k₁ j = chunk k₂ j) → Tree.get? k₁ h t = Tree.get? k₂ h t
  | 0, l, hch => by simp only [Tree.get?, hch 0 (Nat.le_refl 0)]
  | h + 1, n, hch => by
      rw [get?_succ, get?_succ, hch (h + 1) (Nat.le_refl _)]
      cases Node.get? n (chunk k₂ (h + 1)) with
      | none => rfl
      | some c => exact get?_congr k₁ k₂ h c (fun j hj => hch j (Nat.le_succ_of_le hj))

/-- `get?` of an equal-height `meetEq` is the value-level intersection of the two lookups. -/
private theorem get?_meetEq (c : V → V → V) (k : Nat) : (h : Nat) → (a b : Tree L h) →
    Tree.get? k h (meetEq c h a b) = optVmeet c (Tree.get? k h a) (Tree.get? k h b)
  | 0, a, b => by
      simp only [meetEq, Tree.get?]
      exact LeafOps.get?_meet c a b (chunk k 0) (chunk_lt k 0)
  | h + 1, a, b => by
      simp only [meetEq]
      rw [get?_succ, get?_succ, get?_succ, Node.get?_meet _ a b (chunk k (h + 1)) (chunk_lt _ _)]
      cases hga : Node.get? a (chunk k (h + 1)) with
      | none => simp only [Node.optMeet, optVmeet]
      | some ca =>
        cases hgb : Node.get? b (chunk k (h + 1)) with
        | none => simp only [Node.optMeet]; cases Tree.get? k h ca <;> rfl
        | some cb =>
          show (match (if Tree.isEmpty h (meetEq c h ca cb) then none else some (meetEq c h ca cb)) with
                  | some cc => Tree.get? k h cc | none => none)
              = optVmeet c (Tree.get? k h ca) (Tree.get? k h cb)
          rw [← get?_meetEq c k h ca cb]
          by_cases hemp : Tree.isEmpty h (meetEq c h ca cb) = true
          · rw [if_pos hemp, get?_eq_none_of_isEmpty k h _ hemp]
          · rw [if_neg hemp]

/-- `get?` of an equal-height `joinEq` is the value-level union of the two lookups. -/
private theorem get?_joinEq (c : V → V → V) (k : Nat) : (h : Nat) → (a b : Tree L h) →
    Tree.get? k h (joinEq c h a b) = optVjoin c (Tree.get? k h a) (Tree.get? k h b)
  | 0, a, b => by
      simp only [joinEq, Tree.get?]
      exact LeafOps.get?_join c a b (chunk k 0) (chunk_lt k 0)
  | h + 1, a, b => by
      simp only [joinEq]
      rw [get?_succ, get?_succ, get?_succ, Node.get?_join _ a b (chunk k (h + 1)) (chunk_lt _ _)]
      cases hga : Node.get? a (chunk k (h + 1)) with
      | none =>
        cases hgb : Node.get? b (chunk k (h + 1)) with
        | none => simp only [Node.optJoin, optVjoin]
        | some cb => simp only [Node.optJoin, optVjoin]
      | some ca =>
        cases hgb : Node.get? b (chunk k (h + 1)) with
        | none => simp only [Node.optJoin, optVjoin_none_right]
        | some cb =>
          show (match (if Tree.isEmpty h (joinEq c h ca cb) then none else some (joinEq c h ca cb)) with
                  | some cc => Tree.get? k h cc | none => none)
              = optVjoin c (Tree.get? k h ca) (Tree.get? k h cb)
          rw [← get?_joinEq c k h ca cb]
          by_cases hemp : Tree.isEmpty h (joinEq c h ca cb) = true
          · rw [if_pos hemp, get?_eq_none_of_isEmpty k h _ hemp]
          · rw [if_neg hemp]

/-- `get?` of a singleton tree: the queried key reads the stored value exactly when it agrees with
the stored key on every chunk `0..h` (so their lookup paths coincide), otherwise `none`. -/
theorem get?_singleton (k : Nat) (v : V) (j : Nat) : (h : Nat) →
    Tree.get? j h (Tree.singleton k v h : Tree L h)
      = if (∀ i, i ≤ h → chunk j i = chunk k i) then some v else none
  | 0 => by
      simp only [Tree.singleton, Tree.get?]
      rw [LeafOps.get?_insert (LeafOps.empty : L) (chunk k 0) (chunk j 0) v (chunk_lt _ _) (chunk_lt _ _),
          LeafOps.get?_empty]
      by_cases hc : chunk j 0 = chunk k 0
      · have hall : ∀ i, i ≤ 0 → chunk j i = chunk k i := fun i hi => by rw [Nat.le_zero.mp hi]; exact hc
        rw [if_pos hc, if_pos hall]
      · rw [if_neg hc, if_neg (fun hall => hc (hall 0 (Nat.le_refl 0)))]
  | h + 1 => by
      simp only [Tree.singleton]
      rw [get?_succ,
          Node.get?_singleton (chunk k (h+1)) (Tree.singleton k v h) (chunk j (h+1))
            (chunk_lt _ _) (chunk_lt _ _)]
      by_cases hcj : chunk j (h+1) = chunk k (h+1)
      · rw [if_pos hcj]
        show Tree.get? j h (Tree.singleton k v h) = _
        rw [get?_singleton k v j h]
        by_cases hall : ∀ i, i ≤ h → chunk j i = chunk k i
        · have hbig : ∀ i, i ≤ h+1 → chunk j i = chunk k i := by
            intro i hi
            rcases Nat.lt_or_eq_of_le hi with h' | h'
            · exact hall i (Nat.le_of_lt_succ h')
            · subst h'; exact hcj
          rw [if_pos hall, if_pos hbig]
        · have hneg : ¬ (∀ i, i ≤ h+1 → chunk j i = chunk k i) :=
            fun hbig => hall (fun i hi => hbig i (Nat.le_succ_of_le hi))
          rw [if_neg hall, if_neg hneg]
      · rw [if_neg hcj]
        show (none : Option V) = if (∀ i, i ≤ h+1 → chunk j i = chunk k i) then some v else none
        rw [if_neg (fun hbig => hcj (hbig (h+1) (Nat.le_refl _)))]

/-- `get?` of an `insert`: the queried key reads the inserted value exactly when it agrees with the
inserted key on every chunk `0..h` (its lookup path coincides), otherwise the tree is read
unchanged. -/
theorem get?_insert (k : Nat) (v : V) (j : Nat) : (h : Nat) → (t : Tree L h) →
    Tree.get? j h (Tree.insert k v h t)
      = if (∀ i, i ≤ h → chunk j i = chunk k i) then some v else Tree.get? j h t
  | 0, l => by
      simp only [Tree.insert, Tree.get?]
      rw [LeafOps.get?_insert l (chunk k 0) (chunk j 0) v (chunk_lt _ _) (chunk_lt _ _)]
      by_cases hc : chunk j 0 = chunk k 0
      · have hall : ∀ i, i ≤ 0 → chunk j i = chunk k i := fun i hi => by rw [Nat.le_zero.mp hi]; exact hc
        rw [if_pos hc, if_pos hall]
      · rw [if_neg hc, if_neg (fun hall => hc (hall 0 (Nat.le_refl 0)))]
  | h + 1, n => by
      cases hck : Node.get? n (chunk k (h+1)) with
      | some child =>
          have halt : Tree.insert k v (h+1) n
              = Node.insert n (chunk k (h+1)) (Tree.insert k v h child) := by
            simp only [Tree.insert]
            exact Node.alter_eq_insert n (chunk k (h+1)) _ (Tree.insert k v h child) (by rw [hck])
          rw [get?_succ, halt,
              Node.get?_insert n (chunk k (h+1)) (Tree.insert k v h child) (chunk j (h+1))
                (chunk_lt _ _) (chunk_lt _ _)]
          by_cases hcj : chunk j (h+1) = chunk k (h+1)
          · rw [if_pos hcj, get?_succ_some j h n child (by rw [hcj]; exact hck)]
            show Tree.get? j h (Tree.insert k v h child) = _
            rw [get?_insert k v j h child]
            by_cases hall : ∀ i, i ≤ h → chunk j i = chunk k i
            · have hbig : ∀ i, i ≤ h+1 → chunk j i = chunk k i := by
                intro i hi
                rcases Nat.lt_or_eq_of_le hi with h' | h'
                · exact hall i (Nat.le_of_lt_succ h')
                · subst h'; exact hcj
              rw [if_pos hall, if_pos hbig]
            · have hneg : ¬ (∀ i, i ≤ h+1 → chunk j i = chunk k i) :=
                fun hbig => hall (fun i hi => hbig i (Nat.le_succ_of_le hi))
              rw [if_neg hall, if_neg hneg]
          · rw [if_neg hcj, ← get?_succ j h n,
                if_neg (fun hbig => hcj (hbig (h+1) (Nat.le_refl _)))]
      | none =>
          have halt : Tree.insert k v (h+1) n
              = Node.insert n (chunk k (h+1)) (Tree.singleton k v h) := by
            simp only [Tree.insert]
            exact Node.alter_eq_insert n (chunk k (h+1)) _ (Tree.singleton k v h) (by rw [hck])
          rw [get?_succ, halt,
              Node.get?_insert n (chunk k (h+1)) (Tree.singleton k v h) (chunk j (h+1))
                (chunk_lt _ _) (chunk_lt _ _)]
          by_cases hcj : chunk j (h+1) = chunk k (h+1)
          · rw [if_pos hcj, get?_succ_none j h n (by rw [hcj]; exact hck)]
            show Tree.get? j h (Tree.singleton k v h) = _
            rw [get?_singleton k v j h]
            by_cases hall : ∀ i, i ≤ h → chunk j i = chunk k i
            · have hbig : ∀ i, i ≤ h+1 → chunk j i = chunk k i := by
                intro i hi
                rcases Nat.lt_or_eq_of_le hi with h' | h'
                · exact hall i (Nat.le_of_lt_succ h')
                · subst h'; exact hcj
              rw [if_pos hall, if_pos hbig]
            · have hneg : ¬ (∀ i, i ≤ h+1 → chunk j i = chunk k i) :=
                fun hbig => hall (fun i hi => hbig i (Nat.le_succ_of_le hi))
              rw [if_neg hall, if_neg hneg]
          · rw [if_neg hcj, ← get?_succ j h n,
                if_neg (fun hbig => hcj (hbig (h+1) (Nat.le_refl _)))]

/-- `insertImpl` computes the same tree as `insert` at every height: the leaf cases are identical,
and at a node the `setChild`/`insertChild` fast paths each coincide with the `Node.alter` the spec
performs (`Node.setChild_eq_insert`/`insertChild_eq_insert`, collapsed to `alter` via
`Node.alter_eq_insert`). Lets the collection layer run `insertImpl` while keeping every `insert`
characterization (`get?_insert`, `Full_insert`, `isEmpty_insert`) verbatim. -/
theorem insertImpl_eq_insert (k : Nat) (v : V) : (h : Nat) → (t : Tree L h) →
    Tree.insertImpl k v h t = Tree.insert k v h t
  | 0, _ => by simp only [Tree.insertImpl, Tree.insert]
  | h + 1, n => by
      simp only [Tree.insertImpl, Tree.insert]
      by_cases hp : testBit n.positionsMask (chunk k (h + 1)) = true
      · rw [dif_pos hp, insertImpl_eq_insert k v h (n.get (chunk k (h + 1)) hp),
            Node.setChild_eq_insert n (chunk k (h + 1)) _ hp]
        refine (Node.alter_eq_insert n (chunk k (h + 1)) _ _ ?_).symm
        rw [show Node.get? n (chunk k (h + 1)) = some (n.get (chunk k (h + 1)) hp) from by
              simp only [Node.get?, dif_pos hp]]
      · rw [dif_neg hp,
            Node.insertChild_eq_insert n (chunk k (h + 1)) (by simpa using hp) (Tree.singleton k v h)]
        refine (Node.alter_eq_insert n (chunk k (h + 1)) _ _ ?_).symm
        rw [show Node.get? n (chunk k (h + 1)) = none from by
              simp only [Node.get?, dif_neg hp]]

/-- `get?` of a lift: a key in range reads the original tree; a key needing more height than the
slot-0 spine provides reads `none`. -/
theorem get?_liftBy (h : Nat) (t : Tree L h) (k : Nat) : (d : Nat) → requiredHeight k ≤ h + d →
    Tree.get? k (h + d) (liftBy d t) = if requiredHeight k ≤ h then Tree.get? k h t else none
  | 0, _ => by simp only [liftBy, Nat.add_zero]; rw [if_pos (by omega)]
  | d + 1, hk => by
      show Tree.get? k (h + d + 1) (Node.singleton 0 (liftBy d t))
          = if requiredHeight k ≤ h then Tree.get? k h t else none
      rw [get?_succ, Node.get?_singleton 0 (liftBy d t) (chunk k (h + d + 1)) (by decide) (chunk_lt _ _)]
      by_cases hcase : requiredHeight k ≤ h + d
      · rw [if_pos (chunk_eq_zero_of_requiredHeight_lt hcase (by omega))]
        show Tree.get? k (h + d) (liftBy d t) = if requiredHeight k ≤ h then Tree.get? k h t else none
        rw [get?_liftBy h t k d hcase]
      · rw [if_neg (chunk_ne_zero_of_requiredHeight_eq (h := h + d) (by omega)),
            if_neg (show ¬ requiredHeight k ≤ h by omega)]

/-- `get?` of a spine merge: the shorter tree intersected against the keys of the taller tree on
its slot-0 spine (`get?_meetEq` after descending). For keys in range (`requiredHeight ≤ h`). -/
theorem get?_meetSpine (c : V → V → V) (h : Nat) (s : Tree L h) (k : Nat)
    (hk : requiredHeight k ≤ h) : (d : Nat) → (t : Tree L (h + d)) →
      Tree.get? k h (meetSpine c h d s t) = optVmeet c (Tree.get? k h s) (Tree.get? k (h + d) t)
  | 0, t => by simp only [meetSpine, Nat.add_zero]; rw [get?_meetEq c k h s t]
  | d + 1, t => by
      show Tree.get? k h (meetSpine c h (d + 1) s t)
          = optVmeet c (Tree.get? k h s) (Tree.get? k (h + d + 1) t)
      simp only [meetSpine]
      have hchunk : chunk k (h + d + 1) = 0 :=
        chunk_eq_zero_of_requiredHeight_lt (Nat.le_trans hk (Nat.le_add_right h d)) (by omega)
      cases ht0 : Node.get? t 0 with
      | none =>
        rw [get?_empty k h, get?_succ_none k (h + d) t (by rw [hchunk]; exact ht0)]
        cases Tree.get? k h s <;> rfl
      | some child =>
        rw [get?_meetSpine c h s k hk d child,
            get?_succ_some k (h + d) t child (by rw [hchunk]; exact ht0)]

/-- A non-empty `Full` tree has a present key (in range). The denotational analogue of
`isEmpty_eq_false`. -/
theorem exists_get? : (h : Nat) → (t : Tree L h) → Full h t → Tree.isEmpty h t = false →
    ∃ k, requiredHeight k ≤ h ∧ (Tree.get? k h t).isSome
  | 0, l, _, hne => by
      obtain ⟨i, hi, hsome⟩ := LeafOps.exists_get?_of_ne_empty l hne
      have hlt : i.toNat < 32 := by
        have := UInt32.lt_iff_toNat_lt.mp hi; rwa [show (32:UInt32).toNat = 32 from by decide] at this
      refine ⟨i.toNat, requiredHeight_le_of_lt_pow (by rw [Nat.pow_one]; exact hlt), ?_⟩
      simp only [Tree.get?, chunk_toNat_zero i hi]; exact hsome
  | h + 1, n, hf, hne => by
      obtain ⟨s, hs, hsome⟩ := Node.exists_get?_of_isEmpty_false n (by simpa [Tree.isEmpty] using hne)
      obtain ⟨child, hchild⟩ := Option.isSome_iff_exists.mp hsome
      have hmem := Node.mem_of_get? n s child hchild
      obtain ⟨k', hk', hk'some⟩ := exists_get? h child (hf child hmem).2 (hf child hmem).1
      have hpk := lt_pow_of_requiredHeight_le hk'
      refine ⟨k' + s.toNat * 32 ^ (h + 1), requiredHeight_probe_le s k' h hpk hs, ?_⟩
      have hns : Node.get? n (chunk (k' + s.toNat * 32 ^ (h + 1)) (h + 1)) = some child := by
        rw [chunk_probe_high s k' h hpk hs]; exact hchild
      rw [get?_succ_some _ h n child hns,
          get?_congr (k' + s.toNat * 32 ^ (h + 1)) k' h child (fun j hj => chunk_probe_low s k' h j hj)]
      exact hk'some

/-- A non-empty *height-minimal* (`TopProper`) tree has a present key whose `requiredHeight`
is exactly the tree's height: the minimal-height top node has a set slot above slot 0, and
descending it yields a key reaching the top level. Pins the height to the contents. -/
theorem exists_get?_topProper : (h : Nat) → (t : Tree L h) → Full h t → TopProper h t →
    Tree.isEmpty h t = false → ∃ k, requiredHeight k = h ∧ (Tree.get? k h t).isSome
  | 0, t, hf, _, hne => by
      obtain ⟨k, hk, hs⟩ := exists_get? 0 t hf hne
      exact ⟨k, by omega, hs⟩
  | h + 1, n, hf, htp, _ => by
      obtain ⟨s, hs1, hs32, hbit⟩ := exists_high_bit n.positionsMask htp
      have hsome : (Node.get? n s).isSome = true := by rw [← Node.testBit_eq_isSome_get?]; exact hbit
      obtain ⟨child, hchild⟩ := Option.isSome_iff_exists.mp hsome
      have hmem := Node.mem_of_get? n s child hchild
      obtain ⟨k', hk', hk'some⟩ := exists_get? h child (hf child hmem).2 (hf child hmem).1
      have hpk := lt_pow_of_requiredHeight_le hk'
      have hs1' : 1 ≤ s.toNat := by have := UInt32.le_iff_toNat_le.mp hs1; simpa using this
      have hge : ¬ (k' + s.toNat * 32 ^ (h + 1) < 32 ^ (h + 1)) := by
        have hmul : 1 * 32 ^ (h + 1) ≤ s.toNat * 32 ^ (h + 1) := Nat.mul_le_mul hs1' (Nat.le_refl _)
        rw [Nat.one_mul] at hmul; omega
      have hreq : requiredHeight (k' + s.toNat * 32 ^ (h + 1)) = h + 1 := by
        have hub := requiredHeight_probe_le s k' h hpk hs32
        have hlb : ¬ requiredHeight (k' + s.toNat * 32 ^ (h + 1)) ≤ h :=
          fun hle => hge (lt_pow_of_requiredHeight_le hle)
        omega
      refine ⟨k' + s.toNat * 32 ^ (h + 1), hreq, ?_⟩
      rw [get?_succ_some (k' + s.toNat * 32 ^ (h + 1)) h n child
            (by rw [chunk_probe_high s k' h hpk hs32]; exact hchild),
          get?_congr (k' + s.toNat * 32 ^ (h + 1)) k' h child (fun j hj => chunk_probe_low s k' h j hj)]
      exact hk'some

/-- **Tree extensionality**: two `Full` trees of the same height agreeing on every in-range
`get?` are equal. Masks agree by presence (`exists_get?` rules out one-sided slots); children
agree by the induction hypothesis, fed per-slot child `get?`s via probe keys. -/
theorem ext : (h : Nat) → {a b : Tree L h} → Full h a → Full h b →
    (∀ k, requiredHeight k ≤ h → Tree.get? k h a = Tree.get? k h b) → a = b
  | 0, a, b, _, _, hget => by
      apply LeafOps.get?_ext
      intro i hi
      have hlt : i.toNat < 32 := by
        have := UInt32.lt_iff_toNat_lt.mp hi; rwa [show (32:UInt32).toNat = 32 from by decide] at this
      have := hget i.toNat (requiredHeight_le_of_lt_pow (by rw [Nat.pow_one]; exact hlt))
      simpa only [Tree.get?, chunk_toNat_zero i hi] using this
  | h + 1, a, b, hfa, hfb, hget => by
      apply Node.ext
      intro s hs
      have hchild : ∀ (ca cb : Tree L h), Node.get? a s = some ca → Node.get? b s = some cb → ca = cb := by
        intro ca cb hca hcb
        refine ext h (hfa ca (Node.mem_of_get? a s ca hca)).2 (hfb cb (Node.mem_of_get? b s cb hcb)).2 ?_
        intro k' hk'
        have hpk := lt_pow_of_requiredHeight_le hk'
        have hK := hget (k' + s.toNat * 32 ^ (h + 1)) (requiredHeight_probe_le s k' h hpk hs)
        have hca' : Node.get? a (chunk (k' + s.toNat * 32 ^ (h + 1)) (h + 1)) = some ca := by
          rw [chunk_probe_high s k' h hpk hs]; exact hca
        have hcb' : Node.get? b (chunk (k' + s.toNat * 32 ^ (h + 1)) (h + 1)) = some cb := by
          rw [chunk_probe_high s k' h hpk hs]; exact hcb
        rw [get?_succ_some _ h a ca hca', get?_succ_some _ h b cb hcb',
            get?_congr (k' + s.toNat * 32 ^ (h + 1)) k' h ca (fun j hj => chunk_probe_low s k' h j hj),
            get?_congr (k' + s.toNat * 32 ^ (h + 1)) k' h cb (fun j hj => chunk_probe_low s k' h j hj)] at hK
        exact hK
      cases hca : Node.get? a s with
      | none =>
        cases hcb : Node.get? b s with
        | none => rfl
        | some cb =>
          exfalso
          have hmem := Node.mem_of_get? b s cb hcb
          obtain ⟨k', hk', hk'some⟩ := exists_get? h cb (hfb cb hmem).2 (hfb cb hmem).1
          have hpk := lt_pow_of_requiredHeight_le hk'
          have hK := hget (k' + s.toNat * 32 ^ (h + 1)) (requiredHeight_probe_le s k' h hpk hs)
          have hca' : Node.get? a (chunk (k' + s.toNat * 32 ^ (h + 1)) (h + 1)) = none := by
            rw [chunk_probe_high s k' h hpk hs]; exact hca
          have hcb' : Node.get? b (chunk (k' + s.toNat * 32 ^ (h + 1)) (h + 1)) = some cb := by
            rw [chunk_probe_high s k' h hpk hs]; exact hcb
          rw [get?_succ_none _ h a hca', get?_succ_some _ h b cb hcb',
              get?_congr (k' + s.toNat * 32 ^ (h + 1)) k' h cb (fun j hj => chunk_probe_low s k' h j hj)] at hK
          rw [← hK] at hk'some; simp at hk'some
      | some ca =>
        cases hcb : Node.get? b s with
        | none =>
          exfalso
          have hmem := Node.mem_of_get? a s ca hca
          obtain ⟨k', hk', hk'some⟩ := exists_get? h ca (hfa ca hmem).2 (hfa ca hmem).1
          have hpk := lt_pow_of_requiredHeight_le hk'
          have hK := hget (k' + s.toNat * 32 ^ (h + 1)) (requiredHeight_probe_le s k' h hpk hs)
          have hca' : Node.get? a (chunk (k' + s.toNat * 32 ^ (h + 1)) (h + 1)) = some ca := by
            rw [chunk_probe_high s k' h hpk hs]; exact hca
          have hcb' : Node.get? b (chunk (k' + s.toNat * 32 ^ (h + 1)) (h + 1)) = none := by
            rw [chunk_probe_high s k' h hpk hs]; exact hcb
          rw [get?_succ_some _ h a ca hca', get?_succ_none _ h b hcb',
              get?_congr (k' + s.toNat * 32 ^ (h + 1)) k' h ca (fun j hj => chunk_probe_low s k' h j hj)] at hK
          rw [hK] at hk'some; simp at hk'some
        | some cb => exact congrArg some (hchild ca cb hca hcb)

/-! ### `get?` characterization of `restricts`

`restrictsEq_iff`/`restrictsSpine_iff` read the equal-height and spine `restricts` denotationally:
`a` restricts `b` exactly when `optRel rel` relates their `get?` readings at every in-range key.
Together with `Tree.ext`'s probe-key machinery these are the tree-level engine of `restricts`
transitivity at the collection layer (`optRel`-transitivity does the rest). The reflexivity
hypothesis is threaded down to the set leaf, whose `restricts` ignores `rel`. -/

/-- **`restrictsEq` characterization** (equal height, `Full` operands). The leaf base is the
`get?_restricts` field; the successor uses `Node.restricts_iff`, matching node slots to keys by
probing the top chunk (as in `Tree.ext`) and recursing on slot children. The forward direction
reduces a key to its low `h+1` digits (`chunk_mod_pow`) before applying the child hypothesis. -/
theorem restrictsEq_iff (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) :
    (h : Nat) → (a b : Tree L h) → Full h a → Full h b →
      (restrictsEq rel h a b = true ↔
        ∀ k, requiredHeight k ≤ h → optRel rel (Tree.get? k h a) (Tree.get? k h b) = true)
  | 0, a, b, _, _ => by
      simp only [restrictsEq]
      rw [LeafOps.get?_restricts rel hrefl a b]
      constructor
      · intro hslot k _
        simp only [Tree.get?]
        exact hslot (chunk k 0) (chunk_lt k 0)
      · intro hkey i hi
        have hlt : i.toNat < 32 := by
          have := UInt32.lt_iff_toNat_lt.mp hi; rwa [show (32 : UInt32).toNat = 32 from by decide] at this
        have hk := hkey i.toNat (requiredHeight_le_of_lt_pow (by rw [Nat.pow_one]; exact hlt))
        simpa only [Tree.get?, chunk_toNat_zero i hi] using hk
  | h + 1, a, b, hfa, hfb => by
      simp only [restrictsEq]
      rw [Node.restricts_iff (fun x y => restrictsEq rel h x y) a b]
      constructor
      · -- per-slot relations ⇒ per-key
        intro hslot k _
        cases hca : Node.get? a (chunk k (h + 1)) with
        | none => rw [get?_succ_none _ h a hca]; rfl
        | some ca =>
          have hsl := hslot (chunk k (h + 1)) (chunk_lt _ _)
          rw [hca] at hsl
          cases hcb : Node.get? b (chunk k (h + 1)) with
          | none => rw [hcb] at hsl; simp [optRel] at hsl
          | some cb =>
            rw [hcb] at hsl
            simp only [optRel] at hsl
            have hma := Node.mem_of_get? a _ ca hca
            have hmb := Node.mem_of_get? b _ cb hcb
            rw [get?_succ_some _ h a ca hca, get?_succ_some _ h b cb hcb]
            have hrlt : k % 32 ^ (h + 1) < 32 ^ (h + 1) := Nat.mod_lt _ (Nat.pow_pos (by decide))
            rw [get?_congr k (k % 32 ^ (h + 1)) h ca (fun j hj => (chunk_mod_pow k h j hj).symm),
                get?_congr k (k % 32 ^ (h + 1)) h cb (fun j hj => (chunk_mod_pow k h j hj).symm)]
            exact (restrictsEq_iff rel hrefl h ca cb (hfa ca hma).2 (hfb cb hmb).2).mp hsl
              (k % 32 ^ (h + 1)) (requiredHeight_le_of_lt_pow hrlt)
      · -- per-key ⇒ per-slot relations
        intro hkey s hs
        cases hca : Node.get? a s with
        | none => rfl
        | some ca =>
          have hma := Node.mem_of_get? a s ca hca
          have hca_ne : Tree.isEmpty h ca = false := (hfa ca hma).1
          have hca_full : Full h ca := (hfa ca hma).2
          cases hcb : Node.get? b s with
          | none =>
            exfalso
            obtain ⟨k', hk', hk'some⟩ := exists_get? h ca hca_full hca_ne
            have hpk := lt_pow_of_requiredHeight_le hk'
            have hK := hkey (k' + s.toNat * 32 ^ (h + 1)) (requiredHeight_probe_le s k' h hpk hs)
            have hca' : Node.get? a (chunk (k' + s.toNat * 32 ^ (h + 1)) (h + 1)) = some ca := by
              rw [chunk_probe_high s k' h hpk hs]; exact hca
            have hcb' : Node.get? b (chunk (k' + s.toNat * 32 ^ (h + 1)) (h + 1)) = none := by
              rw [chunk_probe_high s k' h hpk hs]; exact hcb
            rw [get?_succ_some _ h a ca hca', get?_succ_none _ h b hcb',
                get?_congr (k' + s.toNat * 32 ^ (h + 1)) k' h ca (fun j hj => chunk_probe_low s k' h j hj)] at hK
            obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk'some
            rw [hv] at hK; simp [optRel] at hK
          | some cb =>
            have hmb := Node.mem_of_get? b s cb hcb
            show restrictsEq rel h ca cb = true
            rw [restrictsEq_iff rel hrefl h ca cb hca_full (hfb cb hmb).2]
            intro k' hk'
            have hpk := lt_pow_of_requiredHeight_le hk'
            have hK := hkey (k' + s.toNat * 32 ^ (h + 1)) (requiredHeight_probe_le s k' h hpk hs)
            have hca' : Node.get? a (chunk (k' + s.toNat * 32 ^ (h + 1)) (h + 1)) = some ca := by
              rw [chunk_probe_high s k' h hpk hs]; exact hca
            have hcb' : Node.get? b (chunk (k' + s.toNat * 32 ^ (h + 1)) (h + 1)) = some cb := by
              rw [chunk_probe_high s k' h hpk hs]; exact hcb
            rw [get?_succ_some _ h a ca hca', get?_succ_some _ h b cb hcb',
                get?_congr (k' + s.toNat * 32 ^ (h + 1)) k' h ca (fun j hj => chunk_probe_low s k' h j hj),
                get?_congr (k' + s.toNat * 32 ^ (h + 1)) k' h cb (fun j hj => chunk_probe_low s k' h j hj)] at hK
            exact hK

/-- **`restrictsSpine` characterization**: a shorter `Full` tree restricts the slot-0 spine of a
taller `Full` one exactly when `optRel rel` relates their `get?` readings at every key in the
shorter's range. In-range keys have zero top chunks, so the taller `get?` follows the spine; the
base is `restrictsEq_iff`, and a broken spine (`none`) means the shorter tree is empty — which
`get?` detects via `exists_get?`. -/
theorem restrictsSpine_iff (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (h : Nat) (a : Tree L h) (hfa : Full h a) :
    (d : Nat) → (t : Tree L (h + d)) → Full (h + d) t →
      (restrictsSpine rel h d a t = true ↔
        ∀ k, requiredHeight k ≤ h → optRel rel (Tree.get? k h a) (Tree.get? k (h + d) t) = true)
  | 0, t, hft => by
      simp only [restrictsSpine, Nat.add_zero]
      exact restrictsEq_iff rel hrefl h a t hfa hft
  | d + 1, t, hft => by
      simp only [restrictsSpine]
      cases ht0 : Node.get? t 0 with
      | some child =>
        have hmem := Node.mem_of_get? t 0 child ht0
        have hchild_full : Full (h + d) child := (hft child hmem).2
        rw [restrictsSpine_iff rel hrefl h a hfa d child hchild_full]
        constructor
        · intro hh k hk
          have hchunk : chunk k (h + d + 1) = 0 :=
            chunk_eq_zero_of_requiredHeight_lt (Nat.le_trans hk (Nat.le_add_right h d)) (by omega)
          show optRel rel (get? k h a) (get? k (h + d + 1) t) = true
          rw [get?_succ_some k (h + d) t child (by rw [hchunk]; exact ht0)]
          exact hh k hk
        · intro hh k hk
          have hchunk : chunk k (h + d + 1) = 0 :=
            chunk_eq_zero_of_requiredHeight_lt (Nat.le_trans hk (Nat.le_add_right h d)) (by omega)
          have hb := hh k hk
          show optRel rel (get? k h a) (get? k (h + d) child) = true
          rw [← get?_succ_some k (h + d) t child (by rw [hchunk]; exact ht0)]
          exact hb
      | none =>
        constructor
        · intro hempty k hk
          have hchunk : chunk k (h + d + 1) = 0 :=
            chunk_eq_zero_of_requiredHeight_lt (Nat.le_trans hk (Nat.le_add_right h d)) (by omega)
          show optRel rel (get? k h a) (get? k (h + d + 1) t) = true
          rw [get?_succ_none k (h + d) t (by rw [hchunk]; exact ht0),
              get?_eq_none_of_isEmpty k h a hempty]
          rfl
        · intro hh
          cases hia : Tree.isEmpty h a with
          | true => rfl
          | false =>
            exfalso
            obtain ⟨k₀, hk₀, hk₀some⟩ := exists_get? h a hfa hia
            have hchunk : chunk k₀ (h + d + 1) = 0 :=
              chunk_eq_zero_of_requiredHeight_lt (Nat.le_trans hk₀ (Nat.le_add_right h d)) (by omega)
            have hb : optRel rel (get? k₀ h a) (get? k₀ (h + d + 1) t) = true := hh k₀ hk₀
            rw [get?_succ_none k₀ (h + d) t (by rw [hchunk]; exact ht0)] at hb
            obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk₀some
            rw [hv] at hb; simp [optRel] at hb

/-! ### Bridge lemmas relating `joinSpine`/`liftBy` to the equal-height `joinEq`

These reduce `NatCollection.join` (spine-based, mixed heights) to a single `joinEq` at the common
height, so that `joinEq_assoc` discharges associativity. `joinSpine_eq_joinEq_liftBy` rewrites the
spine descent as `joinEq` against the lifted shorter tree; `liftBy_joinEq` pushes a further lift
through a `joinEq`; `liftBy_liftBy` composes two lifts. All operate on canonical (`Full`,
non-empty) trees, where the `if isEmpty` guards never fire (`isEmpty_joinEq_eq_false`). -/

/-- `Tree.cast` along reflexivity is the identity. -/
@[simp] theorem cast_rfl (t : Tree L h) : Tree.cast (rfl : h = h) t = t := rfl

/-- Two successive casts compose. -/
@[simp] theorem cast_cast {ha hb hc : Nat} (p : ha = hb) (q : hb = hc) (t : Tree L ha) :
    Tree.cast q (Tree.cast p t) = Tree.cast (p.trans q) t := by subst p; subst q; rfl

/-- Lifting commutes with a height cast. -/
theorem liftBy_cast (d : Nat) {ha hb : Nat} (p : ha = hb) (t : Tree L ha) :
    liftBy d (Tree.cast p t) = Tree.cast (congrArg (· + d) p) (liftBy d t) := by subst p; rfl

/-- A slot-0 singleton commutes with a height cast on its child. -/
private theorem singleton0_cast {ha hb : Nat} (p : ha = hb) (t : Tree L ha) :
    (Node.singleton 0 (Tree.cast p t) : Tree L (hb + 1))
      = Tree.cast (congrArg (· + 1) p) (Node.singleton 0 t) := by subst p; rfl

/-- `joinEq` commutes with a height cast on both operands. -/
theorem joinEq_cast (c : V → V → V) {hh H : Nat} (p : hh = H) (x y : Tree L hh) :
    Tree.cast p (joinEq c hh x y) = joinEq c H (Tree.cast p x) (Tree.cast p y) := by subst p; rfl

/-- Lifting by equal amounts gives the same tree (up to the induced height cast). -/
theorem liftBy_congr_d {d d' : Nat} (hdd : d = d') {h : Nat} (t : Tree L h) :
    liftBy d t = Tree.cast (by rw [hdd]) (liftBy d' t) := by subst hdd; rfl

/-- `Tree.cast` is injective: it has the reverse cast as a two-sided inverse. -/
theorem cast_inj {ha hb : Nat} (p : ha = hb) (x y : Tree L ha)
    (h : Tree.cast p x = Tree.cast p y) : x = y := by
  subst p; simpa using h

/-- `liftBy d` is injective: each level wraps the tree under a slot-0 singleton, which the
slot-0 lookup recovers. -/
theorem liftBy_inj (d : Nat) {h : Nat} (x y : Tree L h)
    (heq : liftBy d x = liftBy d y) : x = y := by
  induction d with
  | zero => exact heq
  | succ d ih =>
    apply ih
    have heq' : Node.singleton (0 : UInt32) (liftBy d x) = Node.singleton 0 (liftBy d y) := heq
    have hget : (Node.singleton (0 : UInt32) (liftBy d x)).get? 0
        = (Node.singleton 0 (liftBy d y)).get? 0 := congrArg (fun n => Node.get? n 0) heq'
    rw [Node.get?_singleton 0 (liftBy d x) 0 (by decide) (by decide),
        Node.get?_singleton 0 (liftBy d y) 0 (by decide) (by decide), if_pos rfl] at hget
    exact Option.some.inj hget

/-- Two successive lifts compose into one (up to the height-associativity cast). -/
private theorem liftBy_liftBy (d₁ d₂ : Nat) {h : Nat} (t : Tree L h) :
    liftBy d₂ (liftBy d₁ t) = Tree.cast (Nat.add_assoc h d₁ d₂).symm (liftBy (d₁ + d₂) t) := by
  induction d₂ with
  | zero => rfl
  | succ d₂ ih =>
    have e1 : liftBy (d₂ + 1) (liftBy d₁ t) = Node.singleton 0 (liftBy d₂ (liftBy d₁ t)) := rfl
    rw [e1, ih, singleton0_cast]
    rfl

/-- A lift distributes over `joinEq` on canonical non-empty operands: the slot-0 spine the lift
introduces is merged slot-by-slot, and the guard never prunes. -/
private theorem liftBy_joinEq (c : V → V → V) (h : Nat) (x y : Tree L h)
    (hx : Tree.isEmpty h x = false) (hy : Tree.isEmpty h y = false)
    (hfx : Full h x) (hfy : Full h y) (d : Nat) :
    liftBy d (joinEq c h x y) = joinEq c (h + d) (liftBy d x) (liftBy d y) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hXne : Tree.isEmpty (h + d) (liftBy d x) = false := isEmpty_liftBy d x hx
    have hYne : Tree.isEmpty (h + d) (liftBy d y) = false := isEmpty_liftBy d y hy
    have hXf : Full (h + d) (liftBy d x) := Full_liftBy d x hfx hx
    have hYf : Full (h + d) (liftBy d y) := Full_liftBy d y hfy hy
    have hWne : Tree.isEmpty (h + d) (joinEq c (h + d) (liftBy d x) (liftBy d y)) = false :=
      isEmpty_joinEq_eq_false c (h + d) (liftBy d x) (liftBy d y) hXne hXf hYf
    show Node.singleton 0 (liftBy d (joinEq c h x y))
        = joinEq c (h + d + 1) (Node.singleton 0 (liftBy d x)) (Node.singleton 0 (liftBy d y))
    rw [ih]
    simp only [joinEq]
    apply Node.ext
    intro sl hsl
    rw [Node.get?_join _ _ _ _ hsl,
        Node.get?_singleton 0 (liftBy d x) sl (by decide) hsl,
        Node.get?_singleton 0 (liftBy d y) sl (by decide) hsl,
        Node.get?_singleton 0 (joinEq c (h + d) (liftBy d x) (liftBy d y)) sl (by decide) hsl]
    by_cases hs0 : sl = 0
    · subst hs0
      simp [Node.optJoin, hWne]
    · simp [hs0, Node.optJoin]

/-- The spine descent equals an equal-height `joinEq` against the lifted shorter tree. By induction
on the height gap `d`: each spine step alters slot 0, which (the guard never firing on canonical
non-empty children) coincides with `joinEq` of the slot-0 singleton holding the lifted `s`. -/
theorem joinSpine_eq_joinEq_liftBy (c : V → V → V) (h : Nat) (s : Tree L h)
    (hs : Tree.isEmpty h s = false) (hfs : Full h s) :
    (d : Nat) → (t : Tree L (h + d)) → Full (h + d) t →
      joinSpine c h d s t = joinEq c (h + d) (liftBy d s) t
  | 0, t, _ => by simp only [joinSpine, liftBy]; rfl
  | d + 1, t, hft => by
      have hSne : Tree.isEmpty (h + d) (liftBy d s) = false := isEmpty_liftBy d s hs
      have hSf : Full (h + d) (liftBy d s) := Full_liftBy d s hfs hs
      -- the slot-0 callback (in `have` form, matching `joinSpine`'s compiled definition) always
      -- yields `some` here: the guard never fires on canonical non-empty children
      have hF : (fun (o : Option (Tree L (h + d))) =>
            match o with
            | some child =>
                have r := joinSpine c h d s child
                if Tree.isEmpty (h + d) r then none else some r
            | none => some (liftBy d s)) (Node.get? t 0)
          = some (match Node.get? t 0 with
              | some child => joinEq c (h + d) (liftBy d s) child
              | none => liftBy d s) := by
        cases ht0 : Node.get? t 0 with
        | none => rfl
        | some child =>
            have hcf : Full (h + d) child := (hft child (Node.mem_of_get? t 0 child ht0)).2
            have hr : joinSpine c h d s child = joinEq c (h + d) (liftBy d s) child :=
              joinSpine_eq_joinEq_liftBy c h s hs hfs d child hcf
            show (if Tree.isEmpty (h + d) (joinSpine c h d s child) then none
                    else some (joinSpine c h d s child))
                = some (joinEq c (h + d) (liftBy d s) child)
            rw [hr, if_neg (by simp [isEmpty_joinEq_eq_false c (h + d) (liftBy d s) child hSne hSf hcf])]
      rw [joinSpine, Node.alter_eq_insert t 0 _ _ hF]
      show Node.insert t 0 _ = joinEq c (h + d + 1) (Node.singleton 0 (liftBy d s)) t
      simp only [joinEq]
      apply Node.ext
      intro sl hsl
      rw [Node.get?_insert _ _ _ _ (by decide) hsl, Node.get?_join _ _ _ _ hsl,
          Node.get?_singleton 0 (liftBy d s) sl (by decide) hsl]
      by_cases hs0 : sl = 0
      · subst hs0
        cases ht0 : Node.get? t 0 with
        | none => simp [Node.optJoin]
        | some child =>
            have hcf : Full (h + d) child := (hft child (Node.mem_of_get? t 0 child ht0)).2
            simp [Node.optJoin,
              isEmpty_joinEq_eq_false c (h + d) (liftBy d s) child hSne hSf hcf]
      · rw [if_neg hs0, if_neg hs0]
        cases Node.get? t sl <;> rfl

/-- The mask of a `joinEq` (at height `≥ 1`) on canonical operands is exactly the union of the
operand masks: no slot is pruned, since merging two non-empty `Full` children is never empty. -/
private theorem mask_joinEq (c : V → V → V) (h : Nat) (a b : Tree L (h + 1))
    (hfa : Full (h + 1) a) (hfb : Full (h + 1) b) :
    (joinEq c (h + 1) a b).positionsMask = a.positionsMask ||| b.positionsMask := by
  simp only [joinEq]
  apply eq_of_testBit_eq
  intro j hj
  rw [testBit_or, Node.testBit_eq_isSome_get? _ j, Node.get?_join _ _ _ _ hj,
      Node.testBit_eq_isSome_get? a j, Node.testBit_eq_isSome_get? b j]
  cases hga : Node.get? a j with
  | none => cases Node.get? b j <;> simp [Node.optJoin]
  | some ca =>
      have hcaf := hfa ca (Node.mem_of_get? a j ca hga)
      cases hgb : Node.get? b j with
      | none => simp [Node.optJoin]
      | some cb =>
          have hcbf := hfb cb (Node.mem_of_get? b j cb hgb)
          simp [Node.optJoin, isEmpty_joinEq_eq_false c h ca cb hcaf.1 hcaf.2 hcbf.2]

/-- Lifting a spine-descent merge by `D` more levels: it becomes an equal-height `joinEq` of both
operands lifted to the common top height. Combines the spine bridge with `liftBy_joinEq` and
`liftBy_liftBy`, packaging the spine-side lift composition so the collection layer needn't. -/
theorem liftBy_joinSpine (c : V → V → V) (h d : Nat) (s : Tree L h) (t : Tree L (h + d)) (D : Nat)
    (hsne : Tree.isEmpty h s = false) (htne : Tree.isEmpty (h + d) t = false)
    (hfs : Full h s) (hft : Full (h + d) t) :
    liftBy D (joinSpine c h d s t)
      = joinEq c (h + d + D) (Tree.cast (by omega) (liftBy (d + D) s)) (liftBy D t) := by
  rw [joinSpine_eq_joinEq_liftBy c h s hsne hfs d t hft,
      liftBy_joinEq c (h + d) (liftBy d s) t (isEmpty_liftBy d s hsne) htne
        (Full_liftBy d s hfs hsne) hft D,
      liftBy_liftBy d D s]

/-- `joinEq` preserves height-minimality (`TopProper`) given the left operand is minimal: a high
bit of `a` survives into the union mask. -/
private theorem TopProper_joinEq (c : V → V → V) : (h : Nat) → (a b : Tree L h) →
    Full h a → Full h b → TopProper h a → TopProper h (joinEq c h a b)
  | 0, _, _, _, _, _ => trivial
  | h + 1, a, b, hfa, hfb, htpa => by
      show 2 ≤ (joinEq c (h + 1) a b).positionsMask
      rw [mask_joinEq c h a b hfa hfb]
      have ha : (2 : UInt32) ≤ a.positionsMask := htpa
      revert ha; bv_decide

/-- `joinSpine` preserves height-minimality: for an equal-height merge (`d = 0`) the left operand's
minimality carries through `joinEq`; for a genuine descent (`d ≥ 1`) the taller tree's minimality
survives the slot-0 `alter`. -/
theorem TopProper_joinSpine (c : V → V → V) (h : Nat) : (d : Nat) → (s : Tree L h) → (t : Tree L (h + d)) →
    Tree.isEmpty h s = false → Full h s → Full (h + d) t → TopProper h s → TopProper (h + d) t →
      TopProper (h + d) (joinSpine c h d s t)
  | 0, s, t, _, hfs, hft, htps, _ => by
      simp only [joinSpine]; exact TopProper_joinEq c h s t hfs hft htps
  | d + 1, s, t, hsne, hfs, hft, _, htpt => by
      rw [joinSpine_eq_joinEq_liftBy c h s hsne hfs (d + 1) t hft]
      show 2 ≤ (joinEq c (h + d + 1) (liftBy (d + 1) s) t).positionsMask
      rw [mask_joinEq c (h + d) (liftBy (d + 1) s) t (Full_liftBy (d + 1) s hfs hsne) hft]
      have key : ∀ (x y : UInt32), 2 ≤ y → 2 ≤ x ||| y := by intro x y hy; bv_decide
      exact key _ _ htpt

/-- `get?` of a spine union: descend the taller tree's slot-0 spine and `joinEq` the shorter tree
there. Stated for any in-range key (`requiredHeight ≤ h + d`); the shorter tree contributes only to
keys it can reach (`requiredHeight ≤ h`), guarded by `liftBy`. -/
theorem get?_joinSpine (c : V → V → V) (h : Nat) (s : Tree L h) (hs : Tree.isEmpty h s = false)
    (hfs : Full h s) (k : Nat) (d : Nat) (t : Tree L (h + d)) (hft : Full (h + d) t)
    (hk : requiredHeight k ≤ h + d) :
    Tree.get? k (h + d) (joinSpine c h d s t)
      = optVjoin c (if requiredHeight k ≤ h then Tree.get? k h s else none) (Tree.get? k (h + d) t) := by
  rw [joinSpine_eq_joinEq_liftBy c h s hs hfs d t hft, get?_joinEq c k (h + d) (liftBy d s) t,
      get?_liftBy h s k d hk]

end Tree

end NatCol
