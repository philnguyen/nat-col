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
  toArray u := (List.range 32).foldl (fun acc i =>
    let iu := UInt32.ofNat i
    if testBit u iu then acc.push (iu, ()) else acc) #[]

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

/-- Elements in ascending order. -/
def toList (s : NatSet) : List Nat := (NatCollection.toList s).map Prod.fst
/-- Build a set from a list of elements. -/
def ofList (l : List Nat) : NatSet := l.foldl (fun s k => s.insert k) empty

end NatSet

/-! ## Tests -/

section Tests

-- membership / size on a few common and edge keys (0, within a leaf, across leaves)
#guard NatSet.empty.isEmpty
#guard (∅ : NatSet).size == 0
#guard !(∅ : NatSet).contains 42
#guard (NatSet.empty.insert 42).size == 1
#guard (NatSet.empty.insert 42).contains 42
#guard !(NatSet.empty.insert 42).contains 43
#guard (NatSet.empty.insert 0).contains 0
#guard !(NatSet.empty.insert 0).contains 32      -- 0 and 32 differ only above the first chunk

-- idempotent insert, coherent size and equality
#guard (NatSet.empty.insert 42 |>.insert 42) == NatSet.empty.insert 42
#guard (NatSet.empty.insert 42 |>.insert 42).size == 1
#guard (NatSet.empty.insert 1 |>.insert 2 |>.insert 3).size == 3

-- ordering of toList is ascending regardless of insertion order
#guard (NatSet.empty.insert 42 |>.insert 34 |>.toList) == [34, 42]
#guard (NatSet.empty.insert 5 |>.insert 1000 |>.insert 0 |>.toList) == [0, 5, 1000]

-- erase undoes insert; erasing an absent key is a no-op; erase back to empty is canonical
#guard (NatSet.empty.insert 42 |>.erase 42) == (∅ : NatSet)
#guard (NatSet.empty.insert 42 |>.erase 42).isEmpty
#guard (NatSet.empty.insert 42 |>.erase 99) == NatSet.empty.insert 42
#guard (NatSet.empty.insert 5 |>.insert 1000 |>.erase 1000) == NatSet.empty.insert 5

-- ofList / toList round trip (deduplicated, sorted)
#guard (NatSet.ofList [3, 1, 2, 1, 3]).toList == [1, 2, 3]
#guard (NatSet.ofList [100, 2000, 30000]).size == 3

-- union (via the `∪` notation)
#guard ((NatSet.ofList [1, 2]) ∪ (NatSet.ofList [2, 3])).toList == [1, 2, 3]
#guard (NatSet.ofList [1, 2]) ∪ ∅ == NatSet.ofList [1, 2]               -- right identity
#guard (∅ : NatSet) ∪ (NatSet.ofList [1, 2]) == NatSet.ofList [1, 2]    -- left identity
#guard (NatSet.ofList [1, 2]) ∪ (NatSet.ofList [1, 2]) == NatSet.ofList [1, 2]  -- idempotent
#guard ((NatSet.ofList [1, 1000]) ∪ (NatSet.ofList [2, 5])).toList == [1, 2, 5, 1000]  -- mixed heights

-- intersection (via the `∩` notation)
#guard ((NatSet.ofList [1, 2, 3]) ∩ (NatSet.ofList [2, 3, 4])).toList == [2, 3]
#guard (NatSet.ofList [1, 2]) ∩ ∅ == (∅ : NatSet)                       -- right annihilator
#guard (∅ : NatSet) ∩ (NatSet.ofList [1, 2]) == (∅ : NatSet)            -- left annihilator
#guard (NatSet.ofList [1, 2]) ∩ (NatSet.ofList [1, 2]) == NatSet.ofList [1, 2]  -- idempotent
#guard (NatSet.ofList [1, 2]) ∩ (NatSet.ofList [3, 4]) == (∅ : NatSet)  -- disjoint -> empty
#guard ((NatSet.ofList [1, 1000]) ∩ (NatSet.ofList [1000, 2])).toList == [1000]  -- mixed heights, shrinks

-- subset (via the `⊆` notation)
#guard (∅ : NatSet) ⊆ (NatSet.ofList [1, 2])                               -- empty restricts all
#guard (NatSet.ofList [1, 2]) ⊆ (NatSet.ofList [1, 2, 3])
#guard (NatSet.ofList [1, 2]) ⊆ (NatSet.ofList [1, 2])                      -- reflexive
#guard ¬ ((NatSet.ofList [1, 2, 3]) ⊆ (NatSet.ofList [1, 2]))
#guard ¬ ((NatSet.ofList [1, 1000]) ⊆ (NatSet.ofList [1, 2]))               -- taller -> not subset

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
