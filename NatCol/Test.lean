import NatCol.Set
import NatCol.Map

/-!
# Cross-operation coherence tests

These exercise how operations interact, at the level of the public API (not the trie
representation): lattice laws on concrete instances, inclusion–exclusion, height
growth/shrink round-trips, and a small stress test. The per-operation tests live beside
their definitions in `Set.lean` / `Map.lean`; the future theorem iteration will state
these as proven, universally-quantified theorems.
-/

namespace NatCol
section Tests

/-! ## Sets: lattice laws on concrete (mixed-height) instances -/

private def a : NatSet := NatSet.ofList [1, 2, 40, 1000]
private def b : NatSet := NatSet.ofList [2, 3, 40, 50]
private def c : NatSet := NatSet.ofList [3, 40, 2000]

-- commutativity
#guard a ∪ b == b ∪ a
#guard a ∩ b == b ∩ a

-- associativity
#guard (a ∪ b) ∪ c == a ∪ (b ∪ c)
#guard (a ∩ b) ∩ c == a ∩ (b ∩ c)

-- idempotence
#guard a ∪ a == a
#guard a ∩ a == a

-- absorption
#guard a ∪ (a ∩ b) == a
#guard a ∩ (a ∪ b) == a

-- inclusion–exclusion on sizes
#guard (a ∪ b).size + (a ∩ b).size == a.size + b.size

-- union ⊇ each side; inter ⊆ each side
#guard a ⊆ (a ∪ b)
#guard b ⊆ (a ∪ b)
#guard (a ∩ b) ⊆ a
#guard (a ∩ b) ⊆ b

-- subset is transitive and antisymmetric (concretely)
#guard (NatSet.ofList [40]) ⊆ a ∧ a ⊆ (a ∪ b) ∧ (NatSet.ofList [40]) ⊆ (a ∪ b)
#guard a ⊆ b → b ⊆ a → a == b  -- antisymmetry

/-! ## Height growth then shrink round-trips back to a canonical value -/

-- inserting a deep key then erasing it returns the original (canonical) set
#guard (a.insert 1000000 |>.erase 1000000) == a
-- union with a tall singleton then intersecting it away shrinks back
#guard (a ∪ (NatSet.ofList [5000000])) ∩ a == a
-- building the same set two ways compares equal regardless of height history
#guard NatSet.ofList [1, 2, 40, 1000] == (NatSet.empty.insert 1000 |>.insert 40 |>.insert 2 |>.insert 1)

/-! ## Small stress test -/

private def big : NatSet := NatSet.ofList (List.range 100)

#guard big.size == 100
#guard big.contains 0 && big.contains 99 && !big.contains 100
#guard big.toList == List.range 100
-- erasing every even number leaves the 50 odds, in order
private def odds : NatSet := (List.range 100).foldl (fun s k => if k % 2 == 0 then s.erase k else s) big
#guard odds.size == 50
#guard odds.toList == ((List.range 100).filter (fun k => k % 2 == 1))
#guard odds ⊆ big
#guard big ∩ odds == odds
#guard big ∪ odds == big

/-! ## Maps: lattice laws with associative/commutative combine -/

private def p : NatMap Nat := NatMap.ofList [(1, 1), (2, 2), (40, 40), (1000, 1000)]
private def q : NatMap Nat := NatMap.ofList [(2, 20), (3, 30), (40, 400)]

-- with `+` (associative & commutative), join is associative & commutative
#guard p.join (· + ·) q == q.join (· + ·) p
#guard (p.join (· + ·) q).join (· + ·) p == p.join (· + ·) (q.join (· + ·) p)

-- meet with `+`: only shared keys (2, 40), values summed
#guard (p.meet (· + ·) q).toList == [(2, 22), (40, 440)]

-- domain of join = union of domains; domain of meet = intersection
#guard (p.join (· + ·) q).size == 5
#guard (p.meet (· + ·) q).size == 2

-- restricts is reflexive/transitive on a chain of growing domains
#guard (NatMap.ofList [(40, 40)]).restricts (· == ·) p
#guard p.restricts (· == ·) p
#guard (NatMap.ofList [(40, 40)]).restricts (· == ·) (p.join (fun x _ => x) q)

end Tests
end NatCol
