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
----------------------------------------------------------------------------------------------------
-- Implementation
----------------------------------------------------------------------------------------------------

/-- Leaf operations for sets: a `UInt32` is a 32-element bitset; the value type is `Unit`. -/
instance : LeafOps UInt32 Unit where
  empty := 0
  isEmpty u := u == 0
  size := popCount
  get? u i := if testBit u i then some () else none
  insert u i _ := setBit u i
  erase := clearBit
  modify u _ _ := u
  join _ a b := a ||| b
  meet _ a b := a &&& b
  restricts _ a b := (a &&& b) == a
  toArray u := Nat.fold 32 (fun i _ acc =>
    let iu := UInt32.ofNat i
    if testBit u iu then acc.push (iu, ()) else acc) #[]
  filter p u := Nat.fold 32 (fun i _ acc =>
    let iu := UInt32.ofNat i
    if testBit u iu && p iu () then setBit acc iu else acc) (0 : UInt32)
  insert_ne_empty u i _ := beq_eq_false_iff_ne.mpr (setBit_ne_zero u i)
  isEmpty_modify _ _ _ := rfl
  isEmpty_empty := by decide
  eq_empty_of_isEmpty _ h := eq_of_beq h
  restricts_refl _ _ u := by
    show ((u &&& u) == u) = true
    simp [show u &&& u = u from by bv_decide]
  join_comm _ _ _ a b := by
    show (a ||| b) = (b ||| a)
    bv_decide
  meet_comm _ _ _ a b := by
    show (a &&& b) = (b &&& a)
    bv_decide
  join_assoc _ _ a b d := by
    show (a ||| b) ||| d = a ||| (b ||| d)
    bv_decide
  isEmpty_join _ a b hne := by
    show ((a ||| b) == 0) = false
    have : (a == 0) = false := hne
    bv_decide
  get?_empty i := by simp [testBit_zero]
  get?_meet _ a b i _ := by
    have htb : testBit (a &&& b) i = (testBit a i && testBit b i) := by unfold testBit; bv_decide
    show (if testBit (a &&& b) i then some () else none)
        = optVmeet _ (if testBit a i then some () else none) (if testBit b i then some () else none)
    rw [htb]
    by_cases ha : testBit a i = true <;> by_cases hb : testBit b i = true <;> simp [ha, hb, optVmeet]
  get?_join c a b i _ := by
    have htb : testBit (a ||| b) i = (testBit a i || testBit b i) := testBit_or a b i
    show (if testBit (a ||| b) i then some () else none)
        = optVjoin c (if testBit a i then some () else none) (if testBit b i then some () else none)
    rw [htb]
    by_cases ha : testBit a i = true <;> by_cases hb : testBit b i = true <;> simp [ha, hb, optVjoin]
  get?_insert l i j v hi hj := by
    cases v
    show (if testBit (setBit l i) j then some () else none)
        = if j = i then some () else (if testBit l j then some () else none)
    rw [testBit_setBit l i j hi hj]
    by_cases hji : j = i
    · subst hji
      simp
    · rw [if_neg hji, beq_eq_false_iff_ne.mpr (fun hc => hji hc.symm), Bool.or_false]
  get?_ext a b h := by
    apply eq_of_testBit_eq
    intro i hi
    have hi' := h i hi
    by_cases ha : testBit a i = true <;> by_cases hb : testBit b i = true <;> simp_all
  exists_get?_of_ne_empty u h := by
    have hu : u ≠ 0 := beq_eq_false_iff_ne.mp h
    rcases Classical.em (∃ i, i < 32 ∧ testBit u i = true) with ⟨i, hi, hb⟩ | hno
    · exact ⟨i, hi, by simp [hb]⟩
    · exfalso
      apply hu
      apply eq_of_testBit_eq
      intro i hi
      rw [testBit_zero]
      cases hb : testBit u i with
      | false => rfl
      | true => exact absurd ⟨i, hi, hb⟩ hno
  get?_restricts rel hrefl a b := by
    show ((a &&& b) == a) = true ↔
      ∀ i, i < 32 → optRel rel (if testBit a i then some () else none)
        (if testBit b i then some () else none) = true
    have hrefl' : rel () () = true := hrefl ()
    rw [beq_iff_eq]
    constructor
    · -- mask subset ⇒ every present-on-left slot is present (and `rel` is vacuous via reflexivity)
      intro hM i _
      cases hai : testBit a i with
      | false => simp [optRel]
      | true =>
        have hbi : testBit b i = true := by
          have hh : testBit (a &&& b) i = testBit a i := by rw [hM]
          rw [testBit_and, hai] at hh; simpa using hh
        simp [hbi, optRel, hrefl']
    · -- per-slot `optRel` ⇒ mask subset (a present-on-left/absent-on-right slot would be `false`)
      intro hrhs
      apply eq_of_testBit_eq
      intro i hi
      rw [testBit_and]
      cases hai : testBit a i with
      | false => simp
      | true =>
        have hbi : testBit b i = true := by
          cases hb : testBit b i with
          | true => rfl
          | false => exfalso; have hh := hrhs i hi; simp [hai, hb, optRel] at hh
        simp [hbi]

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
def isEmpty : NatSet → Bool := NatCollection.isEmpty
def size : NatSet → Nat := NatCollection.size
def contains : NatSet → Nat → Bool := NatCollection.contains
def insert (s : NatSet) (k : Nat) : NatSet := NatCollection.insert s k ()
def erase : NatSet → Nat → NatSet := NatCollection.erase

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

/-- Fold `f` over elements in ascending order, starting from `init`. -/
def fold {β : Type w} (f : β → Nat → β) (init : β) (s : NatSet) : β :=
  NatCollection.fold (fun acc k _ => f acc k) init s

/-- Monadic fold over elements in ascending order, threading the accumulator through `m`. The
monadic companion of `fold` (recovered by instantiating `m := Id`). -/
def foldM {β : Type w} {m : Type w → Type w'} [Monad m] (f : β → Nat → m β) (init : β) (s : NatSet) :
    m β :=
  NatCollection.foldM (fun acc k _ => f acc k) init s

/-- Whether every element satisfies `p`, short-circuiting at the first that fails (vacuously true on
the empty set). Same value as `s.fold (fun acc k => acc && p k) true`, but stops at the first
failing element. -/
def all (p : Nat → Bool) (s : NatSet) : Bool := NatCollection.all (fun k _ => p k) s

/-- Whether some element satisfies `p`, short-circuiting at the first that holds (vacuously false on
the empty set). Same value as `s.fold (fun acc k => acc || p k) false`. -/
def any (p : Nat → Bool) (s : NatSet) : Bool := NatCollection.any (fun k _ => p k) s

/-- Keep only the elements satisfying `p`. The result is canonical, so it equals the set built
directly from the surviving elements (and its height shrinks when the deep keys are removed). -/
def filter (p : Nat → Bool) (s : NatSet) : NatSet := NatCollection.filter (fun k _ => p k) s

/-- Monadic `all`: whether every element satisfies the monadic predicate `p`, threading effects in
ascending order and short-circuiting at the first failure. The monadic companion of `all`. -/
def allM {m : Type → Type w} [Monad m] (p : Nat → m Bool) (s : NatSet) : m Bool :=
  NatCollection.allM (fun k _ => p k) s

/-- Monadic `any`: whether some element satisfies `p`, short-circuiting at the first success. -/
def anyM {m : Type → Type w} [Monad m] (p : Nat → m Bool) (s : NatSet) : m Bool :=
  NatCollection.anyM (fun k _ => p k) s

/-- Monadic `filter`: keep the elements for which `p` returns `true`, running `p` on every element
in ascending order and threading its effects through `m`. The result is canonical — rebuilt from
the survivors (see `NatCollection.filterM`) — so it equals the pure `filter` when `p` is
effect-free. -/
def filterM {m : Type → Type w} [Monad m] (p : Nat → m Bool) (s : NatSet) : m NatSet :=
  NatCollection.filterM (fun k _ => p k) s

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

-- fold visits elements in ascending order, regardless of insertion order or height
#guard (NatSet.ofList [3, 1, 2]).fold (fun acc k => acc + k) 0 == 6
#guard (NatSet.ofList [3, 1, 2]).fold (fun acc k => acc ++ [k]) [] == [1, 2, 3]
#guard (∅ : NatSet).fold (fun acc k => acc + k) 0 == 0
#guard (NatSet.ofList [1, 1000, 5]).fold (fun acc k => acc ++ [k]) [] == [1, 5, 1000]  -- mixed heights

-- foldM in `Id` reproduces `fold`; in a real monad it threads effects — `Except` short-circuits at
-- the first element ≥ 100, and `StateM` records the ascending visit order (here across heights).
#guard Id.run ((NatSet.ofList [3, 1, 2]).foldM (fun acc k => pure (acc + k)) 0) == 6
#guard (match ((NatSet.ofList [1, 200, 5, 300]).foldM
          (fun acc k => if k ≥ 100 then throw k else pure (acc + k)) 0 : Except Nat Nat) with
        | .error e => e | .ok _ => 0) == 200        -- stops at the first element ≥ 100
#guard ((NatSet.ofList [1, 5, 1000]).foldM (m := StateM (List Nat))
          (fun (_ : Unit) k => modify (· ++ [k])) () |>.run []).2 == [1, 5, 1000]

-- all / any over elements, short-circuiting. The result is independent of where the scan stops, so
-- it must agree with the naive `fold`-based `&&` / `||` (which always visits every element).
#guard (NatSet.ofList [2, 4, 6]).all (fun k => k % 2 == 0)
#guard !(NatSet.ofList [2, 4, 5, 6]).all (fun k => k % 2 == 0)        -- 5 fails mid-scan
#guard (NatSet.ofList [1, 3, 4, 5]).any (fun k => k % 2 == 0)         -- 4 holds mid-scan
#guard !(NatSet.ofList [1, 3, 5]).any (fun k => k % 2 == 0)
#guard (∅ : NatSet).all (fun _ => false)                             -- vacuously true
#guard !(∅ : NatSet).any (fun _ => true)                             -- vacuously false
#guard (NatSet.ofList [2, 4, 5000]).all (fun k => k % 2 == 0)         -- mixed heights, all even
#guard (NatSet.ofList [1, 3, 5000]).any (fun k => k % 2 == 0)         -- mixed heights, 5000 even
-- headline: short-circuit `all`/`any` agree in value with the naive `fold` computations
#guard (NatSet.ofList [2, 4, 5, 6]).all (fun k => k % 2 == 0)
        == (NatSet.ofList [2, 4, 5, 6]).fold (fun acc k => acc && (k % 2 == 0)) true
#guard (NatSet.ofList [1, 3, 4, 5]).any (fun k => k % 2 == 0)
        == (NatSet.ofList [1, 3, 4, 5]).fold (fun acc k => acc || (k % 2 == 0)) false
#guard (NatSet.ofList [2, 4, 5000]).all (fun k => k % 2 == 0)
        == (NatSet.ofList [2, 4, 5000]).fold (fun acc k => acc && (k % 2 == 0)) true
#guard (∅ : NatSet).any (fun k => k % 2 == 0)
        == (∅ : NatSet).fold (fun acc k => acc || (k % 2 == 0)) false

-- filter keeps exactly the elements satisfying the predicate. The result is canonical, so it is
-- *equal* (not merely same-elements) to the set built directly from the survivors.
#guard (NatSet.ofList [1, 2, 3, 4, 5, 6]).filter (fun k => k % 2 == 0) = NatSet.ofList [2, 4, 6]
#guard ((NatSet.ofList [1, 2, 3, 4, 5, 6]).filter (fun k => k % 2 == 0)).toList == [2, 4, 6]
#guard (NatSet.ofList [1, 2, 3]).filter (fun _ => true) = NatSet.ofList [1, 2, 3]   -- keep all
#guard (NatSet.ofList [1, 2, 3]).filter (fun _ => false) = (∅ : NatSet)             -- drop all
#guard (∅ : NatSet).filter (fun _ => true) = (∅ : NatSet)                           -- empty
-- filtering away the deep keys shrinks the height back to canonical (mixed-height input)
#guard (NatSet.ofList [1, 2, 5000]).filter (fun k => k ≤ 99) = NatSet.ofList [1, 2]
#guard hash ((NatSet.ofList [1, 2, 5000]).filter (fun k => k ≤ 99)) == hash (NatSet.ofList [1, 2])
-- filter agrees with `List.filter` through `toList` (order preserved, mixed heights)
#guard ((NatSet.ofList [1, 40, 99, 5000]).filter (fun k => k % 2 == 1)).toList
        == ((NatSet.ofList [1, 40, 99, 5000]).toList.filter (fun k => k % 2 == 1))

-- monadic allM / anyM / filterM: in `Id` they reproduce the pure ops; in a real monad they thread
-- effects in ascending order. `StateM` records the visit order, which also exposes short-circuiting.
#guard Id.run ((NatSet.ofList [2, 4, 6]).allM (fun k => pure (k % 2 == 0)))
#guard !Id.run ((NatSet.ofList [2, 5, 6]).anyM (fun k => pure (k > 100)))
#guard Id.run ((NatSet.ofList [1, 2, 3]).filterM (fun k => pure (k % 2 == 1))) = NatSet.ofList [1, 3]
-- allM stops at the first failure (5 is odd), so 6 is never visited (the StateM log ends at 5)
#guard Id.run (((NatSet.ofList [2, 4, 5, 6]).allM (m := StateM (List Nat))
          (fun k => do modify (· ++ [k]); pure (k % 2 == 0))).run []) == (false, [2, 4, 5])
-- anyM stops at the first success (4 is even), so 5 and 6 are never visited
#guard Id.run (((NatSet.ofList [1, 3, 4, 5, 6]).anyM (m := StateM (List Nat))
          (fun k => do modify (· ++ [k]); pure (k % 2 == 0))).run []) == (true, [1, 3, 4])
-- allM / anyM agree in value with the pure all / any
#guard Id.run ((NatSet.ofList [2, 4, 5, 6]).allM (fun k => pure (k % 2 == 0)))
        == (NatSet.ofList [2, 4, 5, 6]).all (fun k => k % 2 == 0)
#guard Id.run ((NatSet.ofList [1, 3, 4, 5]).anyM (fun k => pure (k % 2 == 0)))
        == (NatSet.ofList [1, 3, 4, 5]).any (fun k => k % 2 == 0)
-- filterM in `Id` agrees with the pure filter; it visits every element in ascending order; and in
-- `Except` a throwing predicate short-circuits at the first offending element (300 is never seen).
#guard Id.run ((NatSet.ofList [1, 2, 3, 4, 5, 6]).filterM (fun k => pure (k % 2 == 0)))
        = (NatSet.ofList [1, 2, 3, 4, 5, 6]).filter (fun k => k % 2 == 0)
#guard (((NatSet.ofList [1, 5, 1000]).filterM (m := StateM (List Nat))
          (fun k => do modify (· ++ [k]); pure true)).run []).2 == [1, 5, 1000]
#guard (match ((NatSet.ofList [1, 200, 5, 300]).filterM
          (fun k => if k ≥ 100 then throw k else pure (k % 2 == 0)) : Except Nat NatSet) with
        | .error e => e | .ok _ => 0) == 200

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

----------------------------------------------------------------------------------------------------
-- Theorems
----------------------------------------------------------------------------------------------------

namespace NatSet

/-- The empty set is a left identity of `∪` (union). -/
@[simp, grind =]
theorem union_empty_left (s : NatSet) : NatSet.empty ∪ s = s :=
  NatCollection.join_empty_left (fun _ _ => ()) s

/-- The empty set is a right identity of `∪` (union). -/
@[simp, grind =]
theorem union_empty_right (s : NatSet) : s ∪ NatSet.empty = s :=
  NatCollection.join_empty_right (fun _ _ => ()) s

/-- Union is commutative. (The set `combine` is constantly `()`, so flipping it is a no-op and the
flip law `NatCollection.join_comm` gives unconditional commutativity.) -/
theorem union_comm (s t : NatSet) : s ∪ t = t ∪ s :=
  NatCollection.join_comm (fun _ _ => ()) s t

/-- Union is associative. (The set `combine` is constantly `()`, which is trivially associative, so
`NatCollection.join_assoc` applies with no side condition.) -/
theorem union_assoc (s t u : NatSet) : (s ∪ t) ∪ u = s ∪ (t ∪ u) :=
  NatCollection.join_assoc (fun _ _ => ()) (fun _ _ _ => rfl) s t u

/-- The empty set is a left annihilator of `∩` (intersection). -/
@[simp, grind =]
theorem inter_empty_left (s : NatSet) : NatSet.empty ∩ s = NatSet.empty :=
  NatCollection.meet_empty_left (fun _ _ => ()) s

/-- The empty set is a right annihilator of `∩` (intersection). -/
@[simp, grind =]
theorem inter_empty_right (s : NatSet) : s ∩ NatSet.empty = NatSet.empty :=
  NatCollection.meet_empty_right (fun _ _ => ()) s

/-- Intersection is commutative. (The set `combine` is constantly `()`, so flipping it is a no-op
and the flip law `NatCollection.meet_comm` gives unconditional commutativity.) -/
theorem inter_comm (s t : NatSet) : s ∩ t = t ∩ s :=
  NatCollection.meet_comm (fun _ _ => ()) s t

/-- Intersection is associative. (The set `combine` is constantly `()`, which is trivially
associative, so `NatCollection.meet_assoc` applies with no side condition.) -/
theorem inter_assoc (s t u : NatSet) : (s ∩ t) ∩ u = s ∩ (t ∩ u) :=
  NatCollection.meet_assoc (fun _ _ => ()) (fun _ _ _ => rfl) s t u

/-- The empty set is a subset of (restricts) every set. -/
@[simp]
theorem subset_empty_left (s : NatSet) : NatSet.empty ⊆ s :=
  NatCollection.restricts_empty_left (fun _ _ => true) s

/-- Subset is reflexive: every set is a subset of itself. -/
@[simp]
theorem subset_refl (s : NatSet) : s ⊆ s :=
  NatCollection.restricts_refl (fun _ _ => true) (fun _ => rfl) s

/-- Intersection is a lower bound: `s ∩ t ⊆ s`. -/
theorem inter_subset_left (s t : NatSet) : s ∩ t ⊆ s :=
  NatCollection.meet_restricts_left (fun _ _ => true) (fun _ => rfl) (fun _ _ => ()) (fun _ _ => rfl) s t

/-- Intersection is a lower bound: `s ∩ t ⊆ t`. -/
theorem inter_subset_right (s t : NatSet) : s ∩ t ⊆ t :=
  NatCollection.meet_restricts_right (fun _ _ => true) (fun _ => rfl) (fun _ _ => ()) (fun _ _ => rfl) s t

/-- Intersection is the greatest lower bound: any set below both `s` and `t` is below `s ∩ t`.
Together with `inter_subset_left`/`inter_subset_right`, this makes `s ∩ t` the infimum of `s`, `t`
for `⊆`. -/
theorem subset_inter {s t u : NatSet} (h₁ : u ⊆ s) (h₂ : u ⊆ t) : u ⊆ s ∩ t :=
  NatCollection.meet_glb (fun _ _ => true) (fun _ => rfl) (fun _ _ => ()) (fun _ _ _ _ _ => rfl) u s t h₁ h₂

/-- Union is an upper bound: `s ⊆ s ∪ t`. -/
theorem subset_union_left (s t : NatSet) : s ⊆ s ∪ t :=
  NatCollection.restricts_join_left (fun _ _ => true) (fun _ => rfl) (fun _ _ => ()) (fun _ _ => rfl) s t

/-- Union is an upper bound: `t ⊆ s ∪ t`. -/
theorem subset_union_right (s t : NatSet) : t ⊆ s ∪ t :=
  NatCollection.restricts_join_right (fun _ _ => true) (fun _ => rfl) (fun _ _ => ()) (fun _ _ => rfl) s t

/-- Union is the least upper bound: any set containing both `s` and `t` contains `s ∪ t`. Together
with `subset_union_left`/`subset_union_right`, this makes `s ∪ t` the supremum of `s`, `t` for `⊆`. -/
theorem union_subset {s t u : NatSet} (h₁ : s ⊆ u) (h₂ : t ⊆ u) : s ∪ t ⊆ u :=
  NatCollection.join_lub (fun _ _ => true) (fun _ => rfl) (fun _ _ => ()) (fun _ _ _ _ _ => rfl) s t u h₁ h₂

/-- Subset is transitive: `s ⊆ t` and `t ⊆ u` give `s ⊆ u`. The set predicate `fun _ _ => true`
is trivially reflexive and transitive, so no side conditions are needed. -/
theorem subset_trans {s t u : NatSet} (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u :=
  NatCollection.restricts_trans (fun _ _ => true) (fun _ => rfl) (fun _ _ _ _ _ => rfl) s t u hst htu

/-- Subset is anti-symmetric: `s ⊆ t` and `t ⊆ s` force `s = t`. The set predicate
`fun _ _ => true` is trivially reflexive and (since `Unit` is a subsingleton) anti-symmetric, so
no side conditions are needed. -/
theorem subset_antisymm {s t : NatSet} (hst : s ⊆ t) (hts : t ⊆ s) : s = t :=
  NatCollection.restricts_antisymm (fun _ _ => true) (fun _ => rfl) (fun _ _ _ _ => rfl) s t hst hts

/-- A freshly-inserted element is a member: `k ∈ s.insert k`. -/
@[simp]
theorem mem_insert_self (s : NatSet) (k : Nat) : k ∈ s.insert k := by
  show (NatCollection.get? (NatCollection.insert s k ()) k).isSome = true
  rw [NatCollection.get?_insert s k () k]
  simp

/-- Inserting an element already in the set returns the same set. -/
theorem insert_of_mem {s : NatSet} {k : Nat} (h : k ∈ s) : s.insert k = s := by
  have hk : NatCollection.get? s k = some () := by
    have hb : (NatCollection.get? s k).isSome = true := h
    cases hg : NatCollection.get? s k with
    | none => rw [hg] at hb; exact absurd hb (by decide)
    | some u => exact congrArg some (Subsingleton.elim u ())
  apply NatCollection.ext_get?
  intro j
  show NatCollection.get? (NatCollection.insert s k ()) j = NatCollection.get? s j
  rw [NatCollection.get?_insert s k () j]
  by_cases hj : j = k
  · rw [if_pos hj, hj, hk]
  · rw [if_neg hj]

/-- The union of a set with itself is the set. -/
@[simp]
theorem union_self (s : NatSet) : s ∪ s = s := by
  apply NatCollection.ext_get?
  intro k
  show NatCollection.get? (NatCollection.join (fun _ _ => ()) s s) k = NatCollection.get? s k
  rw [NatCollection.get?_join (fun _ _ => ()) s s k]
  cases NatCollection.get? s k with
  | none => rfl
  | some u => cases u; rfl

/-- The intersection of a set with itself is the set. -/
@[simp]
theorem inter_self (s : NatSet) : s ∩ s = s := by
  apply NatCollection.ext_get?
  intro k
  show NatCollection.get? (NatCollection.meet (fun _ _ => ()) s s) k = NatCollection.get? s k
  rw [NatCollection.get?_meet (fun _ _ => ()) s s k]
  cases NatCollection.get? s k with
  | none => rfl
  | some u => cases u; rfl

/-- Intersection distributes over union: `s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u)`. The set `combine` is
constantly `()`, so the distributivity side-condition is trivially `rfl`. -/
theorem inter_union_distrib (s t u : NatSet) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
  NatCollection.meet_join_distrib (fun _ _ => ()) (fun _ _ => ()) (fun _ _ _ => rfl) s t u

/-- Union distributes over intersection: `s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u)`. The set `combine` is
constantly `()`, so every lattice side-condition (idempotence, absorption, distributivity) is
trivially `rfl`. -/
theorem union_inter_distrib (s t u : NatSet) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
  NatCollection.join_meet_distrib (fun _ _ => ()) (fun _ _ => ())
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) s t u

end NatSet

end NatCol
