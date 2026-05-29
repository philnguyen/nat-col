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

/-- A uniform 32-ary trie of the given height. -/
abbrev Tree (leaf : Type u) : Nat → Type u
  | 0 => leaf
  | n + 1 => Node (Tree leaf n)

/-- A leaf collection: maps 5-bit slot indices to values of type `V`. This is the single
seam that distinguishes sets (`UInt32` leaves, `V = Unit`) from maps (`Node α` leaves,
`V = α`); everything else is shared. -/
class LeafOps (L : Type u) (V : outParam (Type u)) where
  empty     : L
  isEmpty   : L → Bool
  size      : L → Nat
  get?      : L → UInt32 → Option V
  insert    : L → UInt32 → V → L
  erase     : L → UInt32 → L
  modify    : L → UInt32 → (V → V) → L
  join      : (V → V → V) → L → L → L
  meet      : (V → V → V) → L → L → L
  restricts : (V → V → Bool) → L → L → Bool
  /-- Present `(slot, value)` pairs in ascending slot order. -/
  toArray   : L → Array (UInt32 × V)

namespace Tree

variable {L : Type u} {V : Type u} [LeafOps L V]

/-- The empty tree of a given height. -/
def empty : (h : Nat) → Tree L h
  | 0 => LeafOps.empty
  | _ + 1 => Node.empty

/-- Is the tree empty? (For canonical trees only the leaf or the top node can be empty.) -/
def isEmpty : (h : Nat) → Tree L h → Bool
  | 0, l => LeafOps.isEmpty l
  | _ + 1, n => Node.isEmpty n

/-- Number of keys present. -/
def size : (h : Nat) → Tree L h → Nat
  | 0, l => LeafOps.size l
  | h + 1, n => n.elements.foldl (fun acc c => acc + size h c) 0
termination_by h => h

/-- Look up the value at key `k`. -/
def get? (k : Nat) : (h : Nat) → Tree L h → Option V
  | 0, l => LeafOps.get? l (chunk k 0)
  | h + 1, n =>
    match Node.get? n (chunk k (h + 1)) with
    | some child => get? k h child
    | none => none
termination_by h => h

/-- A tree of the given height holding the single key `k` ↦ `v`. -/
def singleton (k : Nat) (v : V) : (h : Nat) → Tree L h
  | 0 => LeafOps.insert LeafOps.empty (chunk k 0) v
  | h + 1 => Node.singleton (chunk k (h + 1)) (singleton k v h)
termination_by h => h

/-- Insert / overwrite key `k` ↦ `v`. Assumes `h` is large enough to hold `k`
(the `NatCollection` layer grows the height first when needed). -/
def insert (k : Nat) (v : V) : (h : Nat) → Tree L h → Tree L h
  | 0, l => LeafOps.insert l (chunk k 0) v
  | h + 1, n => n.alter (chunk k (h + 1)) fun
      | some child => some (insert k v h child)
      | none => some (singleton k v h)
termination_by h => h

/-- Erase key `k`, pruning subtrees that become empty (keeps the tree canonical below
the top level). -/
def erase (k : Nat) : (h : Nat) → Tree L h → Tree L h
  | 0, l => LeafOps.erase l (chunk k 0)
  | h + 1, n => n.alter (chunk k (h + 1)) fun
      | some child =>
        let c := erase k h child
        if isEmpty h c then none else some c
      | none => none
termination_by h => h

/-- Apply `f` to the value at key `k`, if present. -/
def modify (k : Nat) (f : V → V) : (h : Nat) → Tree L h → Tree L h
  | 0, l => LeafOps.modify l (chunk k 0) f
  | h + 1, n => n.alter (chunk k (h + 1)) fun
      | some child => some (modify k f h child)
      | none => none
termination_by h => h

/-- Lift a tree up by `d` levels (wrapping it under slot 0). Cast-free: the result type
`Tree L (h + d)` lines up definitionally because `h + (d+1)` reduces to `(h + d) + 1`. -/
def liftBy : (d : Nat) → {h : Nat} → Tree L h → Tree L (h + d)
  | 0, _, t => t
  | _ + 1, _, t => Node.singleton 0 (liftBy _ t)

/-- Transport a tree along a proof of equal heights (compiles to the identity). -/
def cast {ha hb : Nat} (h : ha = hb) (t : Tree L ha) : Tree L hb := h ▸ t

/-- Union of two equal-height trees. Children present on only one side are reused by
`Node.join` without recursion; shared children are merged recursively, combining leaf
values with `c`. -/
def joinEq (c : V → V → V) : (h : Nat) → Tree L h → Tree L h → Tree L h
  | 0, a, b => LeafOps.join c a b
  | h + 1, a, b => Node.join (fun x y => some (joinEq c h x y)) a b
termination_by h => h

/-- Intersection of two equal-height trees. Children present on only one side are dropped
by `Node.meet`; shared subtrees are intersected recursively and pruned if they become
empty. -/
def meetEq (c : V → V → V) : (h : Nat) → Tree L h → Tree L h → Tree L h
  | 0, a, b => LeafOps.meet c a b
  | h + 1, a, b => Node.meet (fun x y =>
      let t := meetEq c h x y
      if isEmpty h t then none else some t) a b
termination_by h => h

/-- `a` restricts `b` (equal heights): `a`'s keys are a subset of `b`'s and `rel` holds
on every coinciding value. -/
def restrictsEq (rel : V → V → Bool) : (h : Nat) → Tree L h → Tree L h → Bool
  | 0, a, b => LeafOps.restricts rel a b
  | h + 1, a, b => Node.restricts (fun x y => restrictsEq rel h x y) a b
termination_by h => h

/-- Structural equality at a fixed height. For canonical trees this coincides with
logical equality. -/
def beq [BEq L] : (h : Nat) → Tree L h → Tree L h → Bool
  | 0, a, b => a == b
  | h + 1, a, b => a.positionsMask == b.positionsMask && a.elements.isEqv b.elements (beq h)
termination_by h => h

/-- Collect `(key, value)` pairs into `acc`, ascending by key. `pfx` carries the key bits
fixed by higher levels. -/
def toArrayAux (pfx : Nat) : (h : Nat) → Tree L h → Array (Nat × V) → Array (Nat × V)
  | 0, l, acc => (LeafOps.toArray l).foldl (fun acc (i, v) => acc.push (pfx ||| i.toNat, v)) acc
  | h + 1, n, acc =>
    n.foldl (fun acc i child => toArrayAux (pfx ||| (i.toNat <<< (5 * (h + 1)))) h child acc) acc
termination_by h => h

/-- All `(key, value)` pairs, ascending by key. -/
def toArray (h : Nat) (t : Tree L h) : Array (Nat × V) := toArrayAux 0 h t #[]

end Tree

end NatCol
