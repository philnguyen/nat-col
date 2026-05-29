import NatCol.Tree

/-!
# `NatCollection`: the generic top-level API

A `NatCollection` pairs a trie with its (minimal) height. All operations are generic over
`[LeafOps L V]`; `NatMap`/`NatSet` are thin instantiations.

## Canonical form

A collection is *canonical* when its height is minimal for its largest key and it contains
no empty subtrees. Every operation here returns a canonical collection, so structural
equality (`beq`) coincides with logical equality.

Two facts drive the implementation:

* **Different heights ⇒ different contents.** A canonical collection's height is a function
  of its largest key, so `beq` can short-circuit to `false` when heights differ.
* **Lifting an empty tree would create junk.** `liftBy` wraps a tree under slot 0; doing
  that to an *empty* tree manufactures spurious empty subtrees. So binary operations and
  `insert` special-case empty operands instead of lifting them.
-/

namespace NatCol

/-- A trie together with its height. -/
structure NatCollection (L : Type u) where
  height : Nat
  tree : Tree L height

namespace NatCollection

variable {L : Type u} {V : Type u} [LeafOps L V]

/-- The empty collection. -/
def empty : NatCollection L := ⟨0, Tree.empty 0⟩

def isEmpty (c : NatCollection L) : Bool := Tree.isEmpty c.height c.tree

def size (c : NatCollection L) : Nat := Tree.size c.height c.tree

/-- Lift a collection's tree up to a common height `H ≥ c.height`. -/
def liftTo (c : NatCollection L) (H : Nat) (le : c.height ≤ H) : Tree L H :=
  Tree.cast (by omega) (Tree.liftBy (H - c.height) c.tree)

/-- Lower the height while the top node is empty or contains only slot 0, restoring
canonical height (needed after `erase`/`meet`). -/
def normalizeAux : (h : Nat) → Tree L h → NatCollection L
  | 0, t => ⟨0, t⟩
  | h + 1, n =>
    if n.positionsMask == 0 then normalizeAux h (Tree.empty h)
    else if n.positionsMask == 1 then
      match n.elements[0]? with
      | some child => normalizeAux h child
      | none => ⟨h + 1, n⟩
    else ⟨h + 1, n⟩
termination_by h => h

def normalize (c : NatCollection L) : NatCollection L := normalizeAux c.height c.tree

/-- Look up the value at key `k`. -/
def get? (c : NatCollection L) (k : Nat) : Option V :=
  if requiredHeight k > c.height then none else Tree.get? k c.height c.tree

/-- Is key `k` present? -/
def contains (c : NatCollection L) (k : Nat) : Bool := (c.get? k).isSome

/-- Insert / overwrite key `k` ↦ `v`, growing the height if `k` needs more chunks. -/
def insert (c : NatCollection L) (k : Nat) (v : V) : NatCollection L :=
  if c.isEmpty then
    ⟨requiredHeight k, Tree.singleton k v (requiredHeight k)⟩
  else
    let H := max c.height (requiredHeight k)
    ⟨H, Tree.insert k v H (c.liftTo H (Nat.le_max_left _ _))⟩

/-- Erase key `k`. -/
def erase (c : NatCollection L) (k : Nat) : NatCollection L :=
  if requiredHeight k > c.height then c
  else normalize ⟨c.height, Tree.erase k c.height c.tree⟩

/-- Apply `f` to the value at key `k`, if present. -/
def modify (c : NatCollection L) (k : Nat) (f : V → V) : NatCollection L :=
  if requiredHeight k > c.height then c
  else ⟨c.height, Tree.modify k f c.height c.tree⟩

/-- Union. Leaf values at coinciding keys are combined with `combine`. -/
def join (combine : V → V → V) (a b : NatCollection L) : NatCollection L :=
  if a.isEmpty then b
  else if b.isEmpty then a
  else
    let H := max a.height b.height
    normalize ⟨H, Tree.joinEq combine H (a.liftTo H (Nat.le_max_left _ _)) (b.liftTo H (Nat.le_max_right _ _))⟩

/-- Intersection. Leaf values at coinciding keys are combined with `combine`. -/
def meet (combine : V → V → V) (a b : NatCollection L) : NatCollection L :=
  if a.isEmpty || b.isEmpty then empty
  else
    let H := max a.height b.height
    normalize ⟨H, Tree.meetEq combine H (a.liftTo H (Nat.le_max_left _ _)) (b.liftTo H (Nat.le_max_right _ _))⟩

/-- `a` restricts `b`: `a`'s keys are a subset of `b`'s, and `rel` holds on every value at
a coinciding key. -/
def restricts (rel : V → V → Bool) (a b : NatCollection L) : Bool :=
  if a.isEmpty then true
  else if b.isEmpty then false
  else
    let H := max a.height b.height
    Tree.restrictsEq rel H (a.liftTo H (Nat.le_max_left _ _)) (b.liftTo H (Nat.le_max_right _ _))

/-- All `(key, value)` pairs, ascending by key. -/
def toList (c : NatCollection L) : List (Nat × V) := (Tree.toArray c.height c.tree).toList

/-- Build a collection from `(key, value)` pairs (later pairs win on duplicate keys). -/
def ofList (l : List (Nat × V)) : NatCollection L := l.foldl (fun c (k, v) => c.insert k v) empty

/-- Structural equality: equal heights and equal trees. Canonical ⇒ logical equality. -/
def beq [BEq L] (a b : NatCollection L) : Bool :=
  if h : a.height = b.height then Tree.beq a.height a.tree (Tree.cast h.symm b.tree) else false

instance [BEq L] : BEq (NatCollection L) := ⟨beq⟩

/-- Hash a collection by its `(key, value)` list. The list is derived structurally, so
`BEq`-equal collections hash equally; since the list is also sorted and canonical, the hash
agrees with logical equality too. -/
instance [Hashable V] : Hashable (NatCollection L) := ⟨fun c => hash c.toList⟩

/-- `beq` decides propositional equality, so the structural `BEq` is lawful. With this,
`LawfulHashable (NatCollection L)` follows automatically from the core
`[LawfulBEq] → [LawfulHashable]` instance. -/
instance [BEq L] [LawfulBEq L] : LawfulBEq (NatCollection L) where
  eq_of_beq {a b} hb := by
    have hb' : NatCollection.beq a b = true := hb
    unfold NatCollection.beq at hb'
    split at hb'
    · rename_i hh
      obtain ⟨ha, ta⟩ := a
      obtain ⟨hbh, tb⟩ := b
      dsimp only at hh hb'
      subst hh
      have : ta = tb := Tree.eq_of_beq _ hb'
      rw [this]
    · exact absurd hb' (by simp)
  rfl {a} := by
    show NatCollection.beq a a = true
    unfold NatCollection.beq
    rw [dif_pos (rfl : a.height = a.height)]
    exact Tree.beq_refl a.height a.tree

/-- Decidable propositional equality, built from the lawful `BEq` (so it agrees with the
`==` test and, via canonical form, with logical equality). -/
instance [BEq L] [LawfulBEq L] : DecidableEq (NatCollection L) := _root_.instDecidableEqOfLawfulBEq

end NatCollection

end NatCol
