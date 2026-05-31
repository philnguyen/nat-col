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
  restricts_refl rel hrefl n := Node.restricts_self rel n (fun x _ => hrefl x)
  join_comm f g hfg a b := Node.join_comm a b (fun x y => by rw [hfg])
  meet_comm f g hfg a b := Node.meet_comm a b (fun x y => by rw [hfg])

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

-- Membership is on keys: `k ∈ m` reduces to the `Bool` `contains`, so it stays decidable (usable
-- in `#guard` / `decide`); `k ∉ m` is `¬ k ∈ m`, available automatically.
instance : Membership Nat (NatMap α) := ⟨fun m k => m.contains k = true⟩
instance (k : Nat) (m : NatMap α) : Decidable (k ∈ m) :=
  inferInstanceAs (Decidable (m.contains k = true))

/-- The empty map is a left identity of `join`. -/
@[simp, grind =]
theorem join_empty_left (combine : α → α → α) (m : NatMap α) :
    NatMap.empty.join combine m = m := NatCollection.join_empty_left combine m

/-- The empty map is a right identity of `join`. -/
@[simp, grind =]
theorem join_empty_right (combine : α → α → α) (m : NatMap α) :
    m.join combine NatMap.empty = m := NatCollection.join_empty_right combine m

/-- `join` commutes when the combine is flipped: swapping the operands swaps the `combine`
arguments. (Values at coinciding keys are resolved `combine left right`, so the order matters
unless `combine` is symmetric — see `join_comm_of_comm`.) -/
theorem join_comm (combine : α → α → α) (m₁ m₂ : NatMap α) :
    m₁.join combine m₂ = m₂.join (fun x y => combine y x) m₁ :=
  NatCollection.join_comm combine m₁ m₂

/-- `join` is commutative when its combine is symmetric. -/
theorem join_comm_of_comm (combine : α → α → α) (hcomm : ∀ x y, combine x y = combine y x)
    (m₁ m₂ : NatMap α) : m₁.join combine m₂ = m₂.join combine m₁ := by
  have h : (fun x y => combine y x) = combine := funext fun x => funext fun y => hcomm y x
  rw [join_comm, h]

/-- The empty map is a left annihilator of `meet`. -/
@[simp, grind =]
theorem meet_empty_left (combine : α → α → α) (m : NatMap α) :
    NatMap.empty.meet combine m = NatMap.empty := NatCollection.meet_empty_left combine m

/-- The empty map is a right annihilator of `meet`. -/
@[simp, grind =]
theorem meet_empty_right (combine : α → α → α) (m : NatMap α) :
    m.meet combine NatMap.empty = NatMap.empty := NatCollection.meet_empty_right combine m

/-- `meet` commutes when the combine is flipped: swapping the operands swaps the `combine`
arguments. (Values at coinciding keys are resolved `combine left right`, so the order matters
unless `combine` is symmetric — see `meet_comm_of_comm`.) -/
theorem meet_comm (combine : α → α → α) (m₁ m₂ : NatMap α) :
    m₁.meet combine m₂ = m₂.meet (fun x y => combine y x) m₁ :=
  NatCollection.meet_comm combine m₁ m₂

/-- `meet` is commutative when its combine is symmetric. -/
theorem meet_comm_of_comm (combine : α → α → α) (hcomm : ∀ x y, combine x y = combine y x)
    (m₁ m₂ : NatMap α) : m₁.meet combine m₂ = m₂.meet combine m₁ := by
  have h : (fun x y => combine y x) = combine := funext fun x => funext fun y => hcomm y x
  rw [meet_comm, h]

/-- The empty map restricts every map (its domain is vacuously a subset). -/
@[simp, grind =]
theorem restricts_empty_left (rel : α → α → Bool) (m : NatMap α) :
    NatMap.empty.restricts rel m = true := NatCollection.restricts_empty_left rel m

/-- `restricts` is reflexive: a map restricts itself whenever `rel` holds on equal values
(`∀ x, rel x x = true`). Plain (not `@[simp]`): the `rel`-reflexivity hypothesis is a side goal
`simp` can't discharge for an arbitrary `rel`. -/
theorem restricts_refl (rel : α → α → Bool) (hrefl : ∀ x, rel x x = true)
    (m : NatMap α) : m.restricts rel m = true := NatCollection.restricts_refl rel hrefl m

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
#guard 2 ∈ m1
#guard 99 ∉ m1
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

/-! ### Cross-height operands: descend the taller tree's spine, both directions

Keys `1,2,3` need height 0, `5000` height 2, so these exercise `join`/`meet`/`restricts` where the
operands differ in height by two levels, with the taller tree on either side. The non-commutative
`fun x _ => x` combine checks that flipping the callback when the left operand is taller still
applies it as `combine left-value right-value`. -/

-- join: collisions combined, taller operand on either side; `+` is commutative so order is symmetric
#guard ((NatMap.ofList [(1, 10), (2, 20)]).join (· + ·) (NatMap.ofList [(1, 1), (5000, 500)])).toList
        == [(1, 11), (2, 20), (5000, 500)]                                              -- rhs taller
#guard ((NatMap.ofList [(1, 1), (5000, 500)]).join (· + ·) (NatMap.ofList [(1, 10), (2, 20)])).toList
        == [(1, 11), (2, 20), (5000, 500)]                                              -- lhs taller
-- left-biased combine pins down argument order across heights (left value must win both ways)
#guard ((NatMap.ofList [(1, 10)]).join (fun x _ => x) (NatMap.ofList [(1, 99), (5000, 500)])).toList
        == [(1, 10), (5000, 500)]                                                       -- rhs taller
#guard ((NatMap.ofList [(1, 10), (5000, 500)]).join (fun x _ => x) (NatMap.ofList [(1, 99)])).toList
        == [(1, 10), (5000, 500)]                                                       -- lhs taller (flipped)
-- `join_comm` flip law: swapping operands and flipping the (non-symmetric) combine is the identity
#guard (NatMap.ofList [(1, 10), (2, 20)]).join (fun x _ => x) (NatMap.ofList [(1, 99), (5000, 5)])
     = (NatMap.ofList [(1, 99), (5000, 5)]).join (fun _ y => y) (NatMap.ofList [(1, 10), (2, 20)])

-- meet: only shared keys survive at the smaller height, taller operand on either side
#guard ((NatMap.ofList [(1, 10), (2, 20), (5000, 500)]).meet (· + ·) (NatMap.ofList [(1, 1), (3, 3)])).toList
        == [(1, 11)]                                                                    -- lhs taller
#guard ((NatMap.ofList [(1, 1), (3, 3)]).meet (· + ·) (NatMap.ofList [(1, 10), (2, 20), (5000, 500)])).toList
        == [(1, 11)]                                                                    -- rhs taller
#guard ((NatMap.ofList [(1, 10), (5000, 5)]).meet (fun x _ => x) (NatMap.ofList [(1, 99)])).toList
        == [(1, 10)]                                                                    -- lhs taller (flipped)
-- `meet_comm` flip law: swapping operands and flipping the (non-symmetric) combine is the identity
#guard (NatMap.ofList [(1, 10), (2, 20)]).meet (fun x _ => x) (NatMap.ofList [(1, 99), (5000, 5)])
     = (NatMap.ofList [(1, 99), (5000, 5)]).meet (fun _ y => y) (NatMap.ofList [(1, 10), (2, 20)])

-- restricts: rhs taller can hold; lhs taller never does; absent key fails
#guard (NatMap.ofList [(1, 10)]).restricts Nat.ble (NatMap.ofList [(1, 10), (5000, 500)])     -- rhs taller, holds
#guard !(NatMap.ofList [(1, 10), (5000, 500)]).restricts Nat.ble (NatMap.ofList [(1, 10)])    -- lhs taller, fails
#guard !(NatMap.ofList [(2, 10)]).restricts Nat.ble (NatMap.ofList [(1, 10), (5000, 500)])    -- rhs taller, key absent

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
