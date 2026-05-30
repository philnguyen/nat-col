import NatCol.Collection

/-!
# `NatSet`: a set of `Nat`

`NatSet` instantiates the generic trie with `UInt32` leaves: a leaf is itself a 32-element
bitset of the low 5 bits, so leaves carry no boxed payload (the value type is `Unit`).
Lattice operations bottom out in plain bitwise `|||` / `&&&` at the leaf.

`NatSet` is a `def` (not an `abbrev`) so that dot-notation resolves to these wrappers
(e.g. single-argument `s.insert 42`) rather than to the underlying `NatCollection`.
-/

namespace NatCol

/-- Leaf operations for sets: a `UInt32` is a 32-element bitset; the value type is `Unit`. -/
instance : LeafOps UInt32 Unit where
  empty := 0
  isEmpty u := u == 0
  size u := popCount u
  get? u i := if testBit u i then some () else none
  insert u i _ := setBit u i
  erase u i := clearBit u i
  modify u _ _ := u
  join _ a b := a ||| b
  meet _ a b := a &&& b
  restricts _ a b := (a &&& b) == a
  toArray u := Nat.fold 32 (fun i _ acc =>
    let iu := UInt32.ofNat i
    if testBit u iu then acc.push (iu, ()) else acc) #[]
  insert_ne_empty u i _ := beq_eq_false_iff_ne.mpr (setBit_ne_zero u i)
  isEmpty_modify _ _ _ := rfl
  isEmpty_empty := by decide
  eq_empty_of_isEmpty _ h := eq_of_beq h
  restricts_refl _ _ u := by
    show ((u &&& u) == u) = true
    simp [show u &&& u = u from by bv_decide]

/-- A set of natural numbers. -/
def NatSet : Type := NatCollection UInt32

namespace NatSet

instance : BEq NatSet := inferInstanceAs (BEq (NatCollection UInt32))
instance : LawfulBEq NatSet := inferInstanceAs (LawfulBEq (NatCollection UInt32))
instance : DecidableEq NatSet := inferInstanceAs (DecidableEq (NatCollection UInt32))
instance : Hashable NatSet := inferInstanceAs (Hashable (NatCollection UInt32))
instance : LawfulHashable NatSet where
  hash_eq _ _ h := by rw [eq_of_beq h]
instance : EmptyCollection NatSet := ⟨NatCollection.empty⟩

/-- The empty set. -/
def empty : NatSet := ∅
def isEmpty (s : NatSet) : Bool := NatCollection.isEmpty s
def size (s : NatSet) : Nat := NatCollection.size s
def contains (s : NatSet) (k : Nat) : Bool := NatCollection.contains s k
def insert (s : NatSet) (k : Nat) : NatSet := NatCollection.insert s k ()
def erase (s : NatSet) (k : Nat) : NatSet := NatCollection.erase s k

/-- Union. -/
def union (s t : NatSet) : NatSet := NatCollection.join (fun _ _ => ()) s t
/-- Intersection. -/
def inter (s t : NatSet) : NatSet := NatCollection.meet (fun _ _ => ()) s t
/-- Subset test. -/
def subset (s t : NatSet) : Bool := NatCollection.restricts (fun _ _ => true) s t

instance : Union NatSet := ⟨union⟩
instance : Inter NatSet := ⟨inter⟩

-- `subset` is `Bool`-valued, so phrase `s ⊆ t` as `subset … = true` and make it
-- decidable, keeping it usable in `#guard` / `decide`.
instance : HasSubset NatSet := ⟨fun s t => s.subset t = true⟩
instance (s t : NatSet) : Decidable (s ⊆ t) := inferInstanceAs (Decidable (s.subset t = true))

-- `k ∈ s` reduces to the `Bool` `contains`, so it stays decidable (usable in `#guard` / `decide`);
-- `k ∉ s` is `¬ k ∈ s`, available automatically.
instance : Membership Nat NatSet := ⟨fun s k => s.contains k = true⟩
instance (k : Nat) (s : NatSet) : Decidable (k ∈ s) :=
  inferInstanceAs (Decidable (s.contains k = true))

/-- Elements in ascending order. -/
def toList (s : NatSet) : List Nat := (NatCollection.toList s).map Prod.fst
/-- Build a set from a list of elements. -/
def ofList (l : List Nat) : NatSet := l.foldl (fun s k => s.insert k) empty

/-- The empty set is a left identity of `∪` (union). -/
@[simp, grind =] theorem union_empty_left (s : NatSet) : NatSet.empty ∪ s = s :=
  NatCollection.join_empty_left (fun _ _ => ()) s

/-- The empty set is a right identity of `∪` (union). -/
@[simp, grind =] theorem union_empty_right (s : NatSet) : s ∪ NatSet.empty = s :=
  NatCollection.join_empty_right (fun _ _ => ()) s

/-- The empty set is a left annihilator of `∩` (intersection). -/
@[simp, grind =] theorem inter_empty_left (s : NatSet) : NatSet.empty ∩ s = NatSet.empty :=
  NatCollection.meet_empty_left (fun _ _ => ()) s

/-- The empty set is a right annihilator of `∩` (intersection). -/
@[simp, grind =] theorem inter_empty_right (s : NatSet) : s ∩ NatSet.empty = NatSet.empty :=
  NatCollection.meet_empty_right (fun _ _ => ()) s

/-- The empty set is a subset of (restricts) every set. -/
@[simp] theorem subset_empty_left (s : NatSet) : NatSet.empty ⊆ s :=
  NatCollection.restricts_empty_left (fun _ _ => true) s

/-- Subset is reflexive: every set is a subset of itself. -/
@[simp] theorem subset_refl (s : NatSet) : s ⊆ s :=
  NatCollection.restricts_refl (fun _ _ => true) (fun _ => rfl) s

end NatSet

/-! ## Tests -/

section Tests

-- membership / size on a few common and edge keys (0, within a leaf, across leaves)
#guard NatSet.empty.isEmpty
#guard (∅ : NatSet).size == 0
#guard 42 ∉ (∅ : NatSet)
#guard (NatSet.empty.insert 42).size == 1
#guard 42 ∈ (NatSet.empty.insert 42)
#guard 43 ∉ (NatSet.empty.insert 42)
#guard 0 ∈ (NatSet.empty.insert 0)
#guard 32 ∉ (NatSet.empty.insert 0)              -- 0 and 32 differ only above the first chunk

-- idempotent insert, coherent size and equality
#guard (NatSet.empty.insert 42 |>.insert 42) = NatSet.empty.insert 42
#guard (NatSet.empty.insert 42 |>.insert 42).size == 1
#guard (NatSet.empty.insert 1 |>.insert 2 |>.insert 3).size == 3

-- ordering of toList is ascending regardless of insertion order
#guard (NatSet.empty.insert 42 |>.insert 34 |>.toList) == [34, 42]
#guard (NatSet.empty.insert 5 |>.insert 1000 |>.insert 0 |>.toList) == [0, 5, 1000]

-- erase undoes insert; erasing an absent key is a no-op; erase back to empty is canonical
#guard (NatSet.empty.insert 42 |>.erase 42) = (∅ : NatSet)
#guard (NatSet.empty.insert 42 |>.erase 42).isEmpty
#guard (NatSet.empty.insert 42 |>.erase 99) = NatSet.empty.insert 42
#guard (NatSet.empty.insert 5 |>.insert 1000 |>.erase 1000) = NatSet.empty.insert 5

-- ofList / toList round trip (deduplicated, sorted)
#guard (NatSet.ofList [3, 1, 2, 1, 3]).toList == [1, 2, 3]
#guard (NatSet.ofList [100, 2000, 30000]).size == 3

-- union (via the `∪` notation)
#guard ((NatSet.ofList [1, 2]) ∪ (NatSet.ofList [2, 3])).toList == [1, 2, 3]
#guard (NatSet.ofList [1, 2]) ∪ ∅ = NatSet.ofList [1, 2]               -- right identity
#guard (∅ : NatSet) ∪ (NatSet.ofList [1, 2]) = NatSet.ofList [1, 2]    -- left identity
#guard (NatSet.ofList [1, 2]) ∪ (NatSet.ofList [1, 2]) = NatSet.ofList [1, 2]  -- idempotent
#guard ((NatSet.ofList [1, 1000]) ∪ (NatSet.ofList [2, 5])).toList == [1, 2, 5, 1000]  -- mixed heights

-- intersection (via the `∩` notation)
#guard ((NatSet.ofList [1, 2, 3]) ∩ (NatSet.ofList [2, 3, 4])).toList == [2, 3]
#guard (NatSet.ofList [1, 2]) ∩ ∅ = (∅ : NatSet)                       -- right annihilator
#guard (∅ : NatSet) ∩ (NatSet.ofList [1, 2]) = (∅ : NatSet)            -- left annihilator
#guard (NatSet.ofList [1, 2]) ∩ (NatSet.ofList [1, 2]) = NatSet.ofList [1, 2]  -- idempotent
#guard (NatSet.ofList [1, 2]) ∩ (NatSet.ofList [3, 4]) = (∅ : NatSet)  -- disjoint -> empty
#guard ((NatSet.ofList [1, 1000]) ∩ (NatSet.ofList [1000, 2])).toList == [1000]  -- mixed heights, shrinks

-- subset (via the `⊆` notation)
#guard (∅ : NatSet) ⊆ (NatSet.ofList [1, 2])                               -- empty restricts all
#guard (NatSet.ofList [1, 2]) ⊆ (NatSet.ofList [1, 2, 3])
#guard (NatSet.ofList [1, 2]) ⊆ (NatSet.ofList [1, 2])                      -- reflexive
#guard ¬ ((NatSet.ofList [1, 2, 3]) ⊆ (NatSet.ofList [1, 2]))
#guard ¬ ((NatSet.ofList [1, 1000]) ⊆ (NatSet.ofList [1, 2]))               -- taller -> not subset

/-! ### Cross-height operands: descend the taller tree's spine, both directions

`1,2,3` need height 0 (`< 32`), `40,50` height 1 (`< 1024`), `5000` height 2 (`< 32768`), so these
exercise `join`/`meet`/`restricts` where the operands differ in height by one and two levels, with
the taller tree on either side, plus the disjoint-spine case. -/

-- union: result lives at the taller height; taller operand on either side
#guard ((NatSet.ofList [1, 2]) ∪ (NatSet.ofList [1, 5000])).toList == [1, 2, 5000]   -- rhs taller (d=2)
#guard ((NatSet.ofList [1, 5000]) ∪ (NatSet.ofList [1, 2])).toList == [1, 2, 5000]   -- lhs taller (d=2)
#guard ((NatSet.ofList [40]) ∪ (NatSet.ofList [5000])).toList == [40, 5000]          -- disjoint spines
#guard (NatSet.ofList [1, 2]) ∪ (NatSet.ofList [1, 5000]) = (NatSet.ofList [1, 5000]) ∪ (NatSet.ofList [1, 2])

-- intersection: result lives at the smaller height; taller operand on either side
#guard ((NatSet.ofList [1, 2, 5000]) ∩ (NatSet.ofList [1, 3])).toList == [1]         -- lhs taller (d=2)
#guard ((NatSet.ofList [1, 3]) ∩ (NatSet.ofList [1, 2, 5000])).toList == [1]         -- rhs taller (d=2)
#guard ((NatSet.ofList [40]) ∩ (NatSet.ofList [5000])) = (∅ : NatSet)                -- disjoint spines

-- subset: rhs taller can still hold; lhs taller never does
#guard (NatSet.ofList [1]) ⊆ (NatSet.ofList [1, 5000])                               -- rhs taller, holds
#guard ¬ ((NatSet.ofList [1, 5000]) ⊆ (NatSet.ofList [1]))                           -- lhs taller, fails
#guard ¬ ((NatSet.ofList [2]) ⊆ (NatSet.ofList [1, 5000]))                           -- rhs taller, key absent

/-! ### Lattice laws across operations, on concrete (mixed-height) instances -/

private def a : NatSet := NatSet.ofList [1, 2, 40, 1000]
private def b : NatSet := NatSet.ofList [2, 3, 40, 50]
private def c : NatSet := NatSet.ofList [3, 40, 2000]

-- commutativity
#guard a ∪ b = b ∪ a
#guard a ∩ b = b ∩ a
-- associativity
#guard (a ∪ b) ∪ c = a ∪ (b ∪ c)
#guard (a ∩ b) ∩ c = a ∩ (b ∩ c)
-- idempotence
#guard a ∪ a = a
#guard a ∩ a = a
-- absorption
#guard a ∪ (a ∩ b) = a
#guard a ∩ (a ∪ b) = a
-- inclusion–exclusion on sizes
#guard (a ∪ b).size + (a ∩ b).size == a.size + b.size
-- union ⊇ each side; inter ⊆ each side
#guard a ⊆ (a ∪ b)
#guard b ⊆ (a ∪ b)
#guard (a ∩ b) ⊆ a
#guard (a ∩ b) ⊆ b
-- subset is transitive and antisymmetric (concretely)
#guard (NatSet.ofList [40]) ⊆ a ∧ a ⊆ (a ∪ b) ∧ (NatSet.ofList [40]) ⊆ (a ∪ b)
#guard a ⊆ b → b ⊆ a → a = b  -- antisymmetry

/-! ### Height growth then shrink round-trips back to a canonical value -/

-- inserting a deep key then erasing it returns the original (canonical) set
#guard (a.insert 1000000 |>.erase 1000000) = a
-- union with a tall singleton then intersecting it away shrinks back
#guard (a ∪ (NatSet.ofList [5000000])) ∩ a = a
-- building the same set two ways compares equal regardless of height history
#guard NatSet.ofList [1, 2, 40, 1000] = (NatSet.empty.insert 1000 |>.insert 40 |>.insert 2 |>.insert 1)

/-! ### Small stress test -/

private def big : NatSet := NatSet.ofList (List.range 100)

#guard big.size == 100
#guard 0 ∈ big ∧ 99 ∈ big ∧ 100 ∉ big
#guard big.toList == List.range 100
-- erasing every even number leaves the 50 odds, in order
private def odds : NatSet := (List.range 100).foldl (fun s k => if k % 2 == 0 then s.erase k else s) big
#guard odds.size == 50
#guard odds.toList == ((List.range 100).filter (fun k => k % 2 == 1))
#guard odds ⊆ big
#guard big ∩ odds = odds
#guard big ∪ odds = big

-- lawful structural equality, decidable propositional equality, and a hash that respects it
example : LawfulBEq NatSet := inferInstance
example : LawfulHashable NatSet := inferInstance
example : DecidableEq NatSet := inferInstance
-- with `DecidableEq`, `#guard` can take propositional `=` directly (decided via `beq`)
#guard NatSet.ofList [1, 2, 3] = NatSet.ofList [3, 2, 1, 2]
#guard ¬ (NatSet.ofList [1, 2] = NatSet.ofList [1, 2, 3])
-- the same set built two ways is `==` and hashes equally (canonical form)
#guard (NatSet.ofList [1, 2, 3] == NatSet.ofList [3, 2, 1, 2]) = true
#guard hash (NatSet.ofList [1, 2, 3]) == hash (NatSet.ofList [3, 2, 1, 2])
-- mixed heights collapse to the same canonical value, so hashes still agree
#guard hash (NatSet.ofList [1, 1000] |>.erase 1000) == hash (NatSet.ofList [1])

end Tests

end NatCol
