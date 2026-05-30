import NatCol.Collection

/-!
# `NatMap`: a map from `Nat` to `α`

`NatMap α` instantiates the generic trie with `Node α` leaves: the leaf is itself a sparse
32-slot map of the low 5 bits to values, so the value type is `α`. The lattice operations
take a `combine : α → α → α` resolving collisions at coinciding keys; `restricts` takes a
predicate `α → α → Bool` checked at coinciding keys.

Like `NatSet`, `NatMap` is a `def` so dot-notation resolves to these wrappers.
-/

namespace NatCol

/-- Leaf operations for maps: a `Node α` is a sparse 32-slot map; the value type is `α`.
The lattice callbacks always return `some` — values never prune; empty *subtrees* are
pruned one level up (in `Tree.meetEq`). -/
instance {α : Type u} : LeafOps (Node α) α where
  empty := Node.empty
  isEmpty n := Node.isEmpty n
  size n := Node.size n
  get? n i := Node.get? n i
  insert n i a := Node.insert n i a
  erase n i := Node.erase n i
  modify n i f := Node.modify n i f
  join c a b := Node.join (fun x y => some (c x y)) a b
  meet c a b := Node.meet (fun x y => some (c x y)) a b
  restricts rel a b := Node.restricts rel a b
  toArray n := n.foldl (fun acc i a => acc.push (i, a)) #[]
  insert_ne_empty n i v := Node.isEmpty_insert n i v
  isEmpty_modify n i g := Node.isEmpty_alter_invariant n i (Option.map g) (fun o => by cases o <;> rfl)
  isEmpty_empty := rfl
  eq_empty_of_isEmpty n h := Node.eq_empty_of_isEmpty n h

/-- A map from natural numbers to `α`. -/
def NatMap (α : Type u) : Type u := NatCollection (Node α)

namespace NatMap

variable {α : Type u}

instance [BEq α] : BEq (NatMap α) := inferInstanceAs (BEq (NatCollection (Node α)))
instance [BEq α] [LawfulBEq α] : LawfulBEq (NatMap α) :=
  inferInstanceAs (LawfulBEq (NatCollection (Node α)))
instance [BEq α] [LawfulBEq α] : DecidableEq (NatMap α) :=
  inferInstanceAs (DecidableEq (NatCollection (Node α)))
instance [Hashable α] : Hashable (NatMap α) := inferInstanceAs (Hashable (NatCollection (Node α)))
instance [BEq α] [LawfulBEq α] [Hashable α] : LawfulHashable (NatMap α) where
  hash_eq _ _ h := by rw [eq_of_beq h]
instance : EmptyCollection (NatMap α) := ⟨NatCollection.empty⟩

/-- The empty map. -/
def empty : NatMap α := ∅
def isEmpty (m : NatMap α) : Bool := NatCollection.isEmpty m
def size (m : NatMap α) : Nat := NatCollection.size m
def contains (m : NatMap α) (k : Nat) : Bool := NatCollection.contains m k
def get? (m : NatMap α) (k : Nat) : Option α := NatCollection.get? m k
def getD (m : NatMap α) (k : Nat) (fallback : α) : α := (m.get? k).getD fallback
def insert (m : NatMap α) (k : Nat) (v : α) : NatMap α := NatCollection.insert m k v
def erase (m : NatMap α) (k : Nat) : NatMap α := NatCollection.erase m k
def modify (m : NatMap α) (k : Nat) (f : α → α) : NatMap α := NatCollection.modify m k f

/-- Union; `combine` resolves values at coinciding keys. -/
def join (combine : α → α → α) (m₁ m₂ : NatMap α) : NatMap α := NatCollection.join combine m₁ m₂
/-- Intersection; `combine` resolves values at coinciding keys. -/
def meet (combine : α → α → α) (m₁ m₂ : NatMap α) : NatMap α := NatCollection.meet combine m₁ m₂
/-- `m₁` restricts `m₂`: `m₁`'s domain ⊆ `m₂`'s, and `rel` holds on values at coinciding keys. -/
def restricts (rel : α → α → Bool) (m₁ m₂ : NatMap α) : Bool := NatCollection.restricts rel m₁ m₂

/-- All `(key, value)` pairs, ascending by key. -/
def toList (m : NatMap α) : List (Nat × α) := NatCollection.toList m
/-- Build a map from `(key, value)` pairs (later pairs win on duplicate keys). -/
def ofList (l : List (Nat × α)) : NatMap α := NatCollection.ofList l

/-- The empty map is a left identity of `join`. -/
@[simp, grind =] theorem join_empty_left (combine : α → α → α) (m : NatMap α) :
    NatMap.empty.join combine m = m := NatCollection.join_empty_left combine m

/-- The empty map is a right identity of `join`. -/
@[simp, grind =] theorem join_empty_right (combine : α → α → α) (m : NatMap α) :
    m.join combine NatMap.empty = m := NatCollection.join_empty_right combine m

/-- The empty map is a left annihilator of `meet`. -/
@[simp, grind =] theorem meet_empty_left (combine : α → α → α) (m : NatMap α) :
    NatMap.empty.meet combine m = NatMap.empty := NatCollection.meet_empty_left combine m

/-- The empty map is a right annihilator of `meet`. -/
@[simp, grind =] theorem meet_empty_right (combine : α → α → α) (m : NatMap α) :
    m.meet combine NatMap.empty = NatMap.empty := NatCollection.meet_empty_right combine m

/-- The empty map restricts every map (its domain is vacuously a subset). -/
@[simp, grind =] theorem restricts_empty_left (rel : α → α → Bool) (m : NatMap α) :
    NatMap.empty.restricts rel m = true := NatCollection.restricts_empty_left rel m

end NatMap

/-! ## Tests -/

section Tests

private def m1 : NatMap Nat := NatMap.empty.insert 1 10 |>.insert 2 20 |>.insert 3 30

-- basic lookups, including across chunk boundaries
#guard (NatMap.empty : NatMap Nat).isEmpty
#guard (NatMap.empty.insert 42 100 : NatMap Nat).size == 1
#guard (NatMap.empty.insert 42 100 : NatMap Nat).get? 42 == some 100
#guard (NatMap.empty.insert 42 100 : NatMap Nat).get? 43 == none
#guard (NatMap.empty.insert 42 100 : NatMap Nat).getD 42 0 == 100
#guard (NatMap.empty.insert 42 100 : NatMap Nat).getD 43 0 == 0
#guard m1.contains 2
#guard !m1.contains 99
#guard (NatMap.empty.insert 1000 7 : NatMap Nat).get? 1000 == some 7  -- multi-chunk key

-- insert overwrites the value, keeps size
#guard (NatMap.empty.insert 42 1 |>.insert 42 2).get? 42 == some 2
#guard (NatMap.empty.insert 42 1 |>.insert 42 2 : NatMap Nat).size == 1

-- modify touches present keys only
#guard (m1.modify 2 (· + 5)).get? 2 == some 25
#guard m1.modify 99 (· + 5) = m1

-- erase
#guard (m1.erase 2).get? 2 == none
#guard (m1.erase 2).size == 2
#guard (NatMap.empty.insert 42 1 |>.erase 42) = (NatMap.empty : NatMap Nat)

-- toList sorted by key irrespective of insertion order
#guard (NatMap.empty.insert 3 30 |>.insert 1 10 |>.insert 2 20).toList == [(1, 10), (2, 20), (3, 30)]
#guard (NatMap.ofList [(5, 50), (1000, 1)]).toList == [(5, 50), (1000, 1)]

-- join: collisions combined (sum), others copied through
#guard ((NatMap.ofList [(1, 10), (2, 20)]).join (· + ·) (NatMap.ofList [(2, 2), (3, 3)])).toList
        == [(1, 10), (2, 22), (3, 3)]
#guard m1.join (· + ·) NatMap.empty = m1                              -- right identity
#guard (NatMap.empty : NatMap Nat).join (· + ·) m1 = m1              -- left identity
#guard m1.join (fun a _ => a) m1 = m1                                 -- idempotent (left-biased)

-- meet: only shared keys survive, combined
#guard ((NatMap.ofList [(1, 10), (2, 20)]).meet (· + ·) (NatMap.ofList [(2, 2), (3, 3)])).toList
        == [(2, 22)]
#guard m1.meet (· + ·) NatMap.empty = (NatMap.empty : NatMap Nat)    -- annihilator
#guard (NatMap.ofList [(1, 1)]).meet (· + ·) (NatMap.ofList [(2, 2)]) = (NatMap.empty : NatMap Nat)  -- disjoint
#guard m1.meet (fun a _ => a) m1 = m1                                 -- idempotent (left-biased)

-- restricts: domain subset + predicate on coinciding values
#guard (NatMap.ofList [(1, 10)]).restricts Nat.ble (NatMap.ofList [(1, 10), (2, 20)])
#guard !(NatMap.ofList [(1, 10), (2, 20)]).restricts Nat.ble (NatMap.ofList [(1, 10)])  -- bigger domain
#guard !(NatMap.ofList [(1, 11)]).restricts Nat.ble (NatMap.ofList [(1, 10)])           -- 11 ≤ 10 fails
#guard (NatMap.empty : NatMap Nat).restricts Nat.ble m1                                 -- empty restricts all
#guard m1.restricts (· == ·) m1                                                         -- reflexive

/-! ### Lattice laws with an associative/commutative combine, on concrete instances -/

private def p : NatMap Nat := NatMap.ofList [(1, 1), (2, 2), (40, 40), (1000, 1000)]
private def q : NatMap Nat := NatMap.ofList [(2, 20), (3, 30), (40, 400)]

-- with `+` (associative & commutative), join is associative & commutative
#guard p.join (· + ·) q = q.join (· + ·) p
#guard (p.join (· + ·) q).join (· + ·) p = p.join (· + ·) (q.join (· + ·) p)
-- meet with `+`: only shared keys (2, 40), values summed
#guard (p.meet (· + ·) q).toList == [(2, 22), (40, 440)]
-- domain of join = union of domains; domain of meet = intersection
#guard (p.join (· + ·) q).size == 5
#guard (p.meet (· + ·) q).size == 2
-- restricts is reflexive/transitive on a chain of growing domains
#guard (NatMap.ofList [(40, 40)]).restricts (· == ·) p
#guard p.restricts (· == ·) p
#guard (NatMap.ofList [(40, 40)]).restricts (· == ·) (p.join (fun x _ => x) q)

-- lawful/decidable equality and a compatible hash (requires the value type to be lawful/hashable)
example : LawfulBEq (NatMap Nat) := inferInstance
example : LawfulHashable (NatMap Nat) := inferInstance
example : DecidableEq (NatMap Nat) := inferInstance
-- insertion order doesn't matter: equal maps compare equal, decide `=`, and hash equally
#guard NatMap.ofList [(1, 10), (2, 20)] = NatMap.ofList [(2, 20), (1, 10)]
#guard ¬ (NatMap.ofList [(1, 10)] = NatMap.ofList [(1, 11)])
#guard (NatMap.ofList [(1, 10), (2, 20)] == NatMap.ofList [(2, 20), (1, 10)]) = true
#guard hash (NatMap.ofList [(1, 10), (2, 20)]) == hash (NatMap.ofList [(2, 20), (1, 10)])

end Tests

end NatCol
