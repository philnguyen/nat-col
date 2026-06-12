import NatCol.Set

/-!
# `NatMap`: a map from `Nat` to `α`

`NatMap α` instantiates the generic trie with `Node α` leaves: the leaf is itself a sparse
32-slot map of the low 5 bits to values, so the value type is `α`. The lattice operations
take a `combine : α → α → α` resolving collisions at coinciding keys; `restricts` takes a
predicate `α → α → Bool` checked at coinciding keys.

Like `NatSet`, `NatMap` is a `def` so dot-notation resolves to these wrappers.
-/

namespace NatCol
----------------------------------------------------------------------------------------------------
-- Implementation
----------------------------------------------------------------------------------------------------

/-- Leaf operations for maps: a `Node α` is a sparse 32-slot map; the value type is `α`.
The lattice callbacks always return `some` — values never prune; empty *subtrees* are
pruned one level up (in `PTree.meet`'s `finalize` re-compression). -/
instance {α : Type u} : LeafOps (Node α) α where
  empty := Node.empty
  isEmpty := Node.isEmpty
  size := Node.size
  get? := Node.get?
  contains n i := testBit n.positionsMask i
  insert := Node.insert
  erase := Node.erase
  modify := Node.modify
  join c a b := Node.join (fun x y => some (c x y)) a b
  meet c a b := Node.meet (fun x y => some (c x y)) a b
  restricts := Node.restricts
  disjoint a b := (a.positionsMask &&& b.positionsMask) == 0
  diff a b := Node.filterMap (fun i v => if testBit b.positionsMask i then none else some v) a
  symmDiff a b := Node.join (fun _ _ => none) a b
  toArray n := n.fold (fun acc i a => acc.push (i, a)) #[]
  filter p n := Node.filterMap (fun i a => if p i a then some a else none) n
  someSlot n := lowestSetIdx n.positionsMask
  slotsMask n := n.positionsMask
  contains_eq_isSome n i := Node.testBit_eq_isSome_get? n i
  insert_ne_empty := Node.isEmpty_insert
  isEmpty_modify n i g := Node.isEmpty_alter_invariant n i (Option.map g) (fun o => by cases o <;> rfl)
  isEmpty_empty := rfl
  eq_empty_of_isEmpty := Node.eq_empty_of_isEmpty
  restricts_refl rel hrefl n := Node.restricts_self rel n (fun x _ => hrefl x)
  join_comm f g hfg a b := Node.join_comm a b (fun x y => by rw [hfg])
  meet_comm f g hfg a b := Node.meet_comm a b (fun x y => by rw [hfg])
  join_assoc c hc a b d :=
    Node.join_assoc _ a b d (fun s _ => Node.optJoin_someC_assoc c hc (a.get? s) (b.get? s) (d.get? s))
  isEmpty_join := Node.isEmpty_join_left
  get?_empty := Node.get?_empty
  get?_meet c a b i hi := by
    show Node.get? (Node.meet (fun x y => some (c x y)) a b) i = optVmeet c (Node.get? a i) (Node.get? b i)
    rw [Node.get?_meet (fun x y => some (c x y)) a b i hi]
    cases Node.get? a i <;> cases Node.get? b i <;> rfl
  get?_join c a b i hi := by
    show Node.get? (Node.join (fun x y => some (c x y)) a b) i = optVjoin c (Node.get? a i) (Node.get? b i)
    rw [Node.get?_join (fun x y => some (c x y)) a b i hi]
    cases Node.get? a i <;> cases Node.get? b i <;> rfl
  get?_insert l i j v hi hj := Node.get?_insert l i v j hi hj
  get?_erase l i j hi hj := Node.get?_erase l i j hi hj
  get?_filter p n j hj :=
    Node.get?_filterMap (fun i a => if p i a then some a else none) n j hj
  get?_ext a b h := Node.ext h
  get?_restricts rel _ a b := Node.restricts_iff rel a b
  someSlot_lt n h := lowestSetIdx_lt n.positionsMask (beq_eq_false_iff_ne.mp h)
  contains_someSlot n h := testBit_lowestSetIdx n.positionsMask (beq_eq_false_iff_ne.mp h)
  testBit_slotsMask _ _ _ := rfl
  disjoint_eq_slotsMask _ _ := rfl
  isEmpty_diff_self n := by
    -- every present slot of `n` has its bit set in `n.positionsMask`, so the `filterMap`
    -- drops everything and the result is the empty node
    have h : Node.filterMap (fun i v => if testBit n.positionsMask i then none else some v) n
        = Node.empty := by
      apply Node.ext
      intro i hi
      rw [Node.get?_filterMap _ n i hi, Node.get?_empty]
      cases hg : n.get? i with
      | none => rfl
      | some v =>
        have htb : testBit n.positionsMask i = true := by
          rw [Node.testBit_eq_isSome_get?, hg]; rfl
        simp [htb]
    show Node.isEmpty (Node.filterMap (fun i v => if testBit n.positionsMask i then none else some v) n) = true
    rw [h]; rfl

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
def isEmpty : NatMap α → Bool := NatCollection.isEmpty
def size : NatMap α → Nat := NatCollection.size
def contains : NatMap α → Nat → Bool := NatCollection.contains
def get? : NatMap α → Nat → Option α := NatCollection.get?
def getD (m : NatMap α) (k : Nat) (fallback : α) : α := (m.get? k).getD fallback
def insert : NatMap α → Nat → α → NatMap α := NatCollection.insert
def erase : NatMap α → Nat → NatMap α := NatCollection.erase
def modify : NatMap α → Nat → (α → α) → NatMap α := NatCollection.modify

/-- Rewrite the entry at `k` through `f`: `f` receives the current value (`some v` if present,
`none` if absent) and returns the value to store, or `none` to leave the key absent. Generalizes
`insert`, `erase`, and `modify`. -/
def alter : NatMap α → Nat → (Option α → Option α) → NatMap α := NatCollection.alter

/-- The least key, `none` on the empty map. O(depth) — an ordered query a hash map answers only
by scanning all n entries. -/
def minKey? : NatMap α → Option Nat := NatCollection.minKey?
/-- The greatest key, `none` on the empty map. O(depth). -/
def maxKey? : NatMap α → Option Nat := NatCollection.maxKey?
/-- The entry with the least key, `none` on the empty map. O(depth). -/
def minEntry? : NatMap α → Option (Nat × α) := NatCollection.minEntry?
/-- The entry with the greatest key, `none` on the empty map. O(depth). -/
def maxEntry? : NatMap α → Option (Nat × α) := NatCollection.maxEntry?
/-- The entry with the least key strictly greater than `k` (successor), `none` if there is none.
O(depth). -/
def entryGT? : NatMap α → Nat → Option (Nat × α) := NatCollection.entryGT?
/-- The entry with the greatest key strictly less than `k` (predecessor), `none` if there is
none. O(depth). -/
def entryLT? : NatMap α → Nat → Option (Nat × α) := NatCollection.entryLT?
/-- The entry with the least key `≥ k`: the entry at `k` itself when present, else the
successor's. -/
def entryGE? : NatMap α → Nat → Option (Nat × α) := NatCollection.entryGE?
/-- The entry with the greatest key `≤ k`: the entry at `k` itself when present, else the
predecessor's. -/
def entryLE? : NatMap α → Nat → Option (Nat × α) := NatCollection.entryLE?
/-- The least-key entry together with the map without it, `none` on the empty map (the
priority-queue step). -/
def popMinEntry? : NatMap α → Option ((Nat × α) × NatMap α) := NatCollection.popMinEntry?
/-- The greatest-key entry together with the map without it, `none` on the empty map. -/
def popMaxEntry? : NatMap α → Option ((Nat × α) × NatMap α) := NatCollection.popMaxEntry?

/-- Union; `combine` resolves values at coinciding keys. -/
def join : (α → α → α) → NatMap α → NatMap α → NatMap α := NatCollection.join
/-- Intersection; `combine` resolves values at coinciding keys. -/
def meet : (α → α → α) → NatMap α → NatMap α → NatMap α := NatCollection.meet
/-- `m₁` restricts `m₂`: `m₁`'s domain ⊆ `m₂`'s, and `rel` holds on values at coinciding keys. -/
def restricts : (α → α → Bool) → NatMap α → NatMap α → Bool := NatCollection.restricts
/-- Whether `m₁` and `m₂` share no key (domain disjointness — values are irrelevant).
Short-circuits at the first shared key and never allocates. -/
def isDisjoint : NatMap α → NatMap α → Bool := NatCollection.isDisjoint
/-- Difference: the entries of `m₁` whose key is absent from `m₂` (`m₂`'s values are irrelevant;
surviving values are untouched). A structural merge walk, not a per-key probe. -/
def diff : NatMap α → NatMap α → NatMap α := NatCollection.diff
/-- Symmetric difference: the entries whose key is in exactly one of `m₁`, `m₂` (entries at
shared keys are dropped, whatever their values). A structural merge walk. -/
def symmDiff : NatMap α → NatMap α → NatMap α := NatCollection.symmDiff
/-- Split at `k`: the entries with key `< k`, the value at `k` (if any), and the entries with
key `> k` — structural prunes along `k`'s routed path; off-path subtrees are shared. -/
def split (m : NatMap α) (k : Nat) : NatMap α × Option α × NatMap α :=
  (NatCollection.filterLt m k, m.get? k, NatCollection.filterGE m (k + 1))
/-- The entries with key in the inclusive range `[lo, hi]` — a double structural prune. -/
def range (m : NatMap α) (lo hi : Nat) : NatMap α := NatCollection.range m lo hi

/-- All `(key, value)` pairs, ascending by key. -/
def toList : NatMap α → List (Nat × α) := NatCollection.toList
/-- Build a map from `(key, value)` pairs (later pairs win on duplicate keys). -/
def ofList : List (Nat × α) → NatMap α := NatCollection.ofList

/-- All keys, ascending. -/
def keys (m : NatMap α) : List Nat :=
  (NatCollection.fold (fun acc k _ => acc.push k) #[] m).toList
/-- All values, in ascending key order. -/
def values (m : NatMap α) : List α :=
  (NatCollection.fold (fun acc _ v => acc.push v) #[] m).toList

/-- The set of keys, as a `NatSet`. One structural pass (`PTree.map`): a map leaf's occupancy
bitmask *is* the corresponding set leaf, so the trie's shape — prefixes, levels, masks — carries
over unchanged and only the values are dropped. The mask is preserved exactly, which is what
`PTree.WF_map` needs to transfer canonicity. -/
def domain (m : NatMap α) : NatSet :=
  ⟨PTree.map (fun l => l.positionsMask) m.tree,
   PTree.WF_map (fun l => l.positionsMask) (fun _ => rfl) (fun _ _ => rfl) m.tree m.wf⟩

/-- `repr` renders the `ofList` of the ascending `(key, value)` list — valid Lean that rebuilds
the map. -/
instance [Repr α] : Repr (NatMap α) where
  reprPrec m prec := Repr.addAppParen ("NatMap.ofList " ++ repr m.toList) prec

/-- `toString` displays the entries in ascending key order as `{k₁ ↦ v₁, k₂ ↦ v₂, …}`. -/
instance [ToString α] : ToString (NatMap α) where
  toString m :=
    "{" ++ String.intercalate ", " (m.toList.map (fun (k, v) => s!"{k} ↦ {v}")) ++ "}"

/-- Fold `f` over `(key, value)` entries in ascending key order, starting from `init`. -/
def fold {β : Type w} : (β → Nat → α → β) → β → NatMap α → β := NatCollection.fold

/-- Monadic fold over `(key, value)` entries in ascending key order, threading the accumulator
through `mo`. The monadic companion of `fold` (recovered by instantiating `mo := Id`). -/
def foldM {β : Type w} {mo : Type w → Type w'} [Monad mo] :
    (β → Nat → α → mo β) → β → NatMap α → mo β := NatCollection.foldM

/-- Whether every entry satisfies `p` (a predicate on key and value), short-circuiting at the first
that fails (vacuously true on the empty map). Same value as
`m.fold (fun acc k v => acc && p k v) true`, but stops at the first failing entry. -/
def all : (Nat → α → Bool) → NatMap α → Bool := NatCollection.all

/-- Whether some entry satisfies `p`, short-circuiting at the first that holds (vacuously false on
the empty map). Same value as `m.fold (fun acc k v => acc || p k v) false`. -/
def any : (Nat → α → Bool) → NatMap α → Bool := NatCollection.any

/-- Keep only the entries `(key, value)` satisfying `p`. The result is canonical, so it equals the
map built directly from the surviving entries (and its height shrinks when deep keys are removed). -/
def filter : (Nat → α → Bool) → NatMap α → NatMap α := NatCollection.filter

/-- Split `m` by `p`: the first component keeps the entries satisfying `p`, the second the rest.
Two structural `filter` passes, so both parts are canonical. -/
def partition (p : Nat → α → Bool) (m : NatMap α) : NatMap α × NatMap α :=
  NatCollection.partition p m

/-- Monadic `all` over entries (predicate on key and value), threading effects in ascending key
order and short-circuiting at the first failure. The monadic companion of `all`. -/
def allM {mo : Type → Type w} [Monad mo] : (Nat → α → mo Bool) → NatMap α → mo Bool :=
  NatCollection.allM

/-- Monadic `any` over entries, short-circuiting at the first success. The monadic companion of
`any`. -/
def anyM {mo : Type → Type w} [Monad mo] : (Nat → α → mo Bool) → NatMap α → mo Bool :=
  NatCollection.anyM

/-- Monadic `filter`: keep the entries for which `p` returns `true`, running `p` on every entry in
ascending key order and threading its effects through `mo`. The result is canonical — rebuilt from
the survivors (see `NatCollection.filterM`) — so it equals the pure `filter` when `p` is
effect-free. Restricted to `α : Type`, as `NatCollection.filterM` is. -/
def filterM {α : Type} {mo : Type → Type w} [Monad mo] :
    (Nat → α → mo Bool) → NatMap α → mo (NatMap α) := NatCollection.filterM

-- Membership is on keys: `k ∈ m` reduces to the `Bool` `contains`, so it stays decidable (usable
-- in `#guard` / `decide`); `k ∉ m` is `¬ k ∈ m`, available automatically.
instance : Membership Nat (NatMap α) := ⟨fun m k => m.contains k = true⟩
instance (k : Nat) (m : NatMap α) : Decidable (k ∈ m) :=
  inferInstanceAs (Decidable (m.contains k = true))

end NatMap

/-! ### `map`: the functorial action on values

`NatMap.map f` rewrites every stored value with `f`, leaving the trie's shape — prefixes, levels,
masks, which keys are present — untouched, so only the value type changes (`α` to `β`). It is
`PTree.map (Node.map f)`: `Node.map` rewrites a leaf node's values, and `PTree.map` carries it over
every leaf. The canonical-shape invariant carries over because `Node.map` preserves a node's slot
mask (`Node.map_positionsMask`), hence its emptiness and slot-membership — exactly what `PTree.WF_map`
needs. -/

/-- Map a function over every value of a `NatMap`, keeping keys and structure. This is the
functorial action `f <$> m` (see the `Functor`/`LawfulFunctor` instances). -/
def NatMap.map {α β : Type u} (f : α → β) (m : NatMap α) : NatMap β :=
  ⟨PTree.map (Node.map f) m.tree,
   PTree.WF_map (Node.map f) (fun l => Node.isEmpty_map f l)
     (fun l i => by
        show testBit (Node.map f l).positionsMask i = testBit l.positionsMask i
        rw [Node.map_positionsMask]) m.tree m.wf⟩

instance : Functor NatMap where
  map := NatMap.map

/-! ## Tests -/

section Tests

private def m1 : NatMap Nat := NatMap.empty.insert 1 10 |>.insert 2 20 |>.insert 3 30

-- basic lookups, including across chunk boundaries
#guard (NatMap.empty : NatMap Nat).isEmpty
#guard (NatMap.empty.insert 42 100 : NatMap Nat).size = 1
#guard (NatMap.empty.insert 42 100 : NatMap Nat).get? 42 = some 100
#guard (NatMap.empty.insert 42 100 : NatMap Nat).get? 43 = none
#guard (NatMap.empty.insert 42 100 : NatMap Nat).getD 42 0 = 100
#guard (NatMap.empty.insert 42 100 : NatMap Nat).getD 43 0 = 0
#guard 2 ∈ m1
#guard 99 ∉ m1
#guard (NatMap.empty.insert 1000 7 : NatMap Nat).get? 1000 = some 7  -- multi-chunk key

-- insert overwrites the value, keeps size
#guard (NatMap.empty.insert 42 1 |>.insert 42 2).get? 42 = some 2
#guard (NatMap.empty.insert 42 1 |>.insert 42 2 : NatMap Nat).size = 1

-- modify touches present keys only
#guard (m1.modify 2 (· + 5)).get? 2 = some 25
#guard m1.modify 99 (· + 5) = m1

-- alter generalizes insert / modify / erase through one callback on the current value
#guard (m1.alter 5 (fun _ => some 50)).get? 5 = some 50                -- absent key: insert
#guard (m1.alter 2 (fun v => v.map (· + 5))).get? 2 = some 25          -- present key: modify
#guard m1.alter 2 (fun _ => none) = m1.erase 2                         -- present key: erase
#guard m1.alter 99 (fun v => v) = m1                                   -- absent, stays none: no-op
#guard (NatMap.empty.insert 42 1).alter 42 (fun _ => none) = (NatMap.empty : NatMap Nat)  -- collapses canonically

-- erase
#guard (m1.erase 2).get? 2 = none
#guard (m1.erase 2).size = 2
#guard (NatMap.empty.insert 42 1 |>.erase 42) = (NatMap.empty : NatMap Nat)

-- isDisjoint: domain disjointness (values are irrelevant)
#guard (NatMap.ofList [(1, 10)]).isDisjoint (NatMap.ofList [(2, 20)])
#guard !((NatMap.ofList [(1, 10)]).isDisjoint (NatMap.ofList [(1, 99)]))  -- same key, ≠ values
#guard (NatMap.empty : NatMap Nat).isDisjoint (NatMap.ofList [(1, 10)])
#guard !((NatMap.ofList [(1, 1), (5000, 2)]).isDisjoint (NatMap.ofList [(5000, 9)]))

-- diff: keys of the second map are removed (its values are irrelevant); structural merge
#guard (NatMap.ofList [(1, 10), (2, 20), (5000, 3)]).diff (NatMap.ofList [(2, 99)])
  == NatMap.ofList [(1, 10), (5000, 3)]
#guard (NatMap.ofList [(1, 10)]).diff (NatMap.ofList [(1, 99)]) == (∅ : NatMap Nat)
#guard (NatMap.ofList [(1, 10), (2, 20)]).diff (∅ : NatMap Nat) == NatMap.ofList [(1, 10), (2, 20)]
#guard ((∅ : NatMap Nat).diff (NatMap.ofList [(1, 10)])).isEmpty
#guard (NatMap.ofList [(1, 10), (5000, 3)]).diff (NatMap.ofList [(5000, 0)])
  == NatMap.ofList [(1, 10)]                                              -- collapses canonically

-- symmDiff: entries whose key is in exactly one map (shared keys drop, whatever the values)
#guard (NatMap.ofList [(1, 10), (2, 20)]).symmDiff (NatMap.ofList [(2, 99), (3, 30)])
  == NatMap.ofList [(1, 10), (3, 30)]
#guard
  let m := NatMap.ofList [(1, 10), (5000, 3)]
  (m.symmDiff m).isEmpty && m.symmDiff (∅ : NatMap Nat) == m
#guard (NatMap.ofList [(1, 10)]).symmDiff (NatMap.ofList [(1, 99)]) == (∅ : NatMap Nat)

-- split: (keys < k, value at k, keys > k); range: inclusive key window
#guard (NatMap.ofList [(1, 10), (5, 50), (9, 90)]).split 5
  == (NatMap.ofList [(1, 10)], some 50, NatMap.ofList [(9, 90)])
#guard (NatMap.ofList [(1, 10), (9, 90)]).split 5
  == (NatMap.ofList [(1, 10)], none, NatMap.ofList [(9, 90)])
#guard (NatMap.ofList [(1, 10), (32, 320), (5000, 3)]).range 2 5000
  == NatMap.ofList [(32, 320), (5000, 3)]
#guard ((NatMap.ofList [(1, 10), (9, 90)]).range 2 8).isEmpty

-- partition: split by predicate; parts are canonical, disjoint, and join back to the original
#guard
  let parts := (NatMap.ofList [(1, 1), (2, 2), (3, 3), (5000, 4)]).partition (fun k _ => k % 2 == 0)
  parts.1 == NatMap.ofList [(2, 2), (5000, 4)] && parts.2 == NatMap.ofList [(1, 1), (3, 3)]
#guard
  let m := NatMap.ofList [(1, 1), (2, 2), (3, 3), (5000, 4)]
  let parts := m.partition (fun _ v => v % 2 == 0)
  parts.1.join (fun x _ => x) parts.2 == m && parts.1.isDisjoint parts.2
#guard
  let parts := (NatMap.empty : NatMap Nat).partition (fun _ _ => true)
  parts.1.isEmpty && parts.2.isEmpty

-- ordered queries: min/max, successor/predecessor (values ride along), pop
#guard (NatMap.ofList [(2, 20), (9, 90)]).minEntry? = some (2, 20)
#guard (NatMap.ofList [(2, 20), (9, 90)]).maxEntry? = some (9, 90)
#guard (NatMap.ofList [(2, 20), (9, 90)]).minKey? = some 2
#guard (NatMap.ofList [(2, 20), (5000, 3)]).maxKey? = some 5000                -- mixed heights
#guard (NatMap.empty : NatMap Nat).minEntry? = none
#guard (NatMap.empty : NatMap Nat).maxKey? = none
#guard (NatMap.ofList [(3, 30), (40, 400)]).entryGT? 3 = some (40, 400)
#guard (NatMap.ofList [(3, 30), (40, 400)]).entryGT? 40 = none
#guard (NatMap.ofList [(3, 30), (40, 400)]).entryLT? 40 = some (3, 30)
#guard (NatMap.ofList [(3, 30), (40, 400)]).entryLT? 3 = none
#guard (NatMap.ofList [(3, 30), (40, 400)]).entryGE? 3 = some (3, 30)
#guard (NatMap.ofList [(3, 30), (40, 400)]).entryGE? 4 = some (40, 400)
#guard (NatMap.ofList [(3, 30), (40, 400)]).entryLE? 39 = some (3, 30)
#guard (NatMap.ofList [(3, 30), (40, 400)]).entryLE? 40 = some (40, 400)
#guard (NatMap.ofList [(1, 10), (2, 20)]).popMinEntry? = some ((1, 10), NatMap.ofList [(2, 20)])
#guard (NatMap.ofList [(1, 10), (2, 20)]).popMaxEntry? = some ((2, 20), NatMap.ofList [(1, 10)])
#guard (NatMap.empty : NatMap Nat).popMinEntry? = none

-- toList sorted by key irrespective of insertion order
#guard (NatMap.empty.insert 3 30 |>.insert 1 10 |>.insert 2 20).toList = [(1, 10), (2, 20), (3, 30)]
#guard (NatMap.ofList [(5, 50), (1000, 1)]).toList = [(5, 50), (1000, 1)]

-- keys / values, ascending by key — the projections of toList, without building the pairs
#guard (NatMap.ofList [(3, 30), (1, 10), (2, 20)]).keys = [1, 2, 3]
#guard (NatMap.ofList [(3, 30), (1, 10), (2, 20)]).values = [10, 20, 30]
#guard (NatMap.ofList [(1, 10), (5000, 3)]).keys = [1, 5000]                      -- mixed heights
#guard (NatMap.empty : NatMap Nat).keys = []
#guard (NatMap.ofList [(5, 50), (1000, 1)]).keys
        = (NatMap.ofList [(5, 50), (1000, 1)]).toList.map Prod.fst
#guard (NatMap.ofList [(5, 50), (1000, 1)]).values
        = (NatMap.ofList [(5, 50), (1000, 1)]).toList.map Prod.snd

-- domain: the NatSet of keys; both sides canonical, so structural `==` is honest equality
#guard (NatMap.ofList [(3, 30), (1, 10), (2, 20)]).domain == NatSet.ofList [1, 2, 3]
#guard (NatMap.empty : NatMap Nat).domain == NatSet.empty
#guard (NatMap.ofList [(1, 10), (5000, 3)]).domain == NatSet.ofList [1, 5000]     -- mixed heights
#guard (NatMap.ofList [(3, 30), (1, 10), (2, 20)]).domain.toList
        = (NatMap.ofList [(3, 30), (1, 10), (2, 20)]).keys                        -- agrees with keys
#guard ((NatMap.ofList [(1, 10), (5000, 3)]).erase 5000).domain == NatSet.ofList [1]

-- fold visits entries in ascending key order, regardless of insertion order or height
#guard (NatMap.ofList [(3, 30), (1, 10), (2, 20)]).fold (fun acc k v => acc + k + v) 0 = 66
#guard (NatMap.ofList [(1, 10), (2, 20)]).fold (fun acc k v => acc ++ [(k, v)]) [] = [(1, 10), (2, 20)]
#guard (NatMap.empty : NatMap Nat).fold (fun acc _ v => acc + v) 0 = 0
#guard (NatMap.ofList [(1, 10), (5000, 3)]).fold (fun acc k v => acc ++ [(k, v)]) [] = [(1, 10), (5000, 3)]  -- mixed heights

-- foldM in `Id` reproduces `fold`; in a real monad it threads effects — `Except` short-circuits at
-- the first odd value, and `StateM` records the ascending visit order (here across heights).
#guard Id.run ((NatMap.ofList [(3, 30), (1, 10), (2, 20)]).foldM (fun acc k v => pure (acc + k + v)) 0) = 66
#guard (match ((NatMap.ofList [(1, 10), (2, 7), (3, 30)]).foldM
          (fun acc _ v => if v % 2 == 1 then throw v else pure (acc + v)) 0 : Except Nat Nat) with
        | .error e => e | .ok _ => 0) = 7          -- stops at the first odd value
#guard ((NatMap.ofList [(1, 10), (5000, 3)]).foldM (mo := StateM (List (Nat × Nat)))
          (fun (_ : Unit) k v => modify (· ++ [(k, v)])) () |>.run []).2 = [(1, 10), (5000, 3)]

-- all / any over entries (predicate on key and value), short-circuiting. The result is independent
-- of where the scan stops, so it must agree with the naive `fold`-based `&&` / `||`.
#guard (NatMap.ofList [(1, 10), (2, 20)]).all (fun _ v => v % 10 == 0)
#guard !(NatMap.ofList [(1, 10), (2, 25), (3, 30)]).all (fun _ v => v % 10 == 0)   -- 25 fails mid-scan
#guard (NatMap.ofList [(1, 10), (2, 20)]).any (fun k _ => k % 2 == 0)              -- key 2 holds
#guard !(NatMap.ofList [(1, 10), (3, 30)]).any (fun k _ => k % 2 == 0)             -- keys 1, 3 odd
#guard (NatMap.empty : NatMap Nat).all (fun _ _ => false)                          -- vacuously true
#guard !(NatMap.empty : NatMap Nat).any (fun _ _ => true)                          -- vacuously false
#guard (NatMap.ofList [(1, 10), (5000, 20)]).all (fun _ v => v % 10 == 0)          -- mixed heights
-- headline: short-circuit `all`/`any` agree in value with the naive `fold` computations
#guard (NatMap.ofList [(1, 10), (2, 25), (3, 30)]).all (fun _ v => v % 10 == 0)
        = (NatMap.ofList [(1, 10), (2, 25), (3, 30)]).fold (fun acc _ v => acc && (v % 10 == 0)) true
#guard (NatMap.ofList [(1, 10), (2, 20)]).any (fun k _ => k % 2 == 0)
        = (NatMap.ofList [(1, 10), (2, 20)]).fold (fun acc k _ => acc || (k % 2 == 0)) false
#guard (NatMap.ofList [(1, 10), (5000, 20)]).all (fun _ v => v % 10 == 0)
        = (NatMap.ofList [(1, 10), (5000, 20)]).fold (fun acc _ v => acc && (v % 10 == 0)) true

-- filter keeps exactly the entries satisfying the predicate. The result is canonical, so it is
-- *equal* (not merely same-entries) to the map built directly from the survivors.
#guard ((NatMap.ofList [(1, 10), (2, 20), (3, 30), (4, 40)]).filter (fun _ v => v % 20 == 0)).toList
        = [(2, 20), (4, 40)]
#guard (NatMap.ofList [(1, 10), (2, 20)]).filter (fun k _ => k % 2 == 1) = NatMap.ofList [(1, 10)]
#guard (NatMap.ofList [(1, 10), (2, 20)]).filter (fun _ _ => true) = NatMap.ofList [(1, 10), (2, 20)]
#guard (NatMap.ofList [(1, 10), (2, 20)]).filter (fun _ _ => false) = (NatMap.empty : NatMap Nat)
#guard (NatMap.empty : NatMap Nat).filter (fun _ _ => true) = NatMap.empty
-- the predicate sees both key and value
#guard ((NatMap.ofList [(1, 10), (2, 20), (3, 30)]).filter (fun k v => 25 ≤ k + v)).toList
        = [(3, 30)]
-- filtering away the deep keys shrinks the height back to canonical (mixed-height input)
#guard (NatMap.ofList [(1, 10), (2, 20), (5000, 3)]).filter (fun k _ => k ≤ 99)
        = NatMap.ofList [(1, 10), (2, 20)]
-- filter agrees with `List.filter` through `toList` (order preserved, mixed heights)
#guard ((NatMap.ofList [(1, 10), (40, 40), (5000, 3)]).filter (fun _ v => v % 2 == 0)).toList
        = ((NatMap.ofList [(1, 10), (40, 40), (5000, 3)]).toList.filter (fun (_, v) => v % 2 == 0))

-- monadic allM / anyM / filterM: in `Id` they reproduce the pure ops; in a real monad they thread
-- effects in ascending key order. `StateM` records the visit order, which also exposes short-circuiting.
#guard Id.run ((NatMap.ofList [(1, 10), (2, 20)]).allM (fun _ v => pure (v % 10 == 0)))
#guard !Id.run ((NatMap.ofList [(1, 10), (2, 20)]).anyM (fun k _ => pure (k > 100)))
#guard Id.run ((NatMap.ofList [(1, 10), (2, 20)]).filterM (fun k _ => pure (k % 2 == 1)))
        = NatMap.ofList [(1, 10)]
-- allM stops at the first failing entry (value 25), so (3, 30) is never visited
#guard Id.run (((NatMap.ofList [(1, 10), (2, 25), (3, 30)]).allM (mo := StateM (List Nat))
          (fun _ v => do modify (· ++ [v]); pure (v % 10 == 0))).run []) = (false, [10, 25])
-- anyM stops at the first holding entry (key 2 even), so (3, 30) is never visited
#guard Id.run (((NatMap.ofList [(1, 10), (2, 20), (3, 30)]).anyM (mo := StateM (List Nat))
          (fun k _ => do modify (· ++ [k]); pure (k % 2 == 0))).run []) = (true, [1, 2])
-- allM / anyM agree in value with the pure all / any
#guard Id.run ((NatMap.ofList [(1, 10), (2, 25), (3, 30)]).allM (fun _ v => pure (v % 10 == 0)))
        = (NatMap.ofList [(1, 10), (2, 25), (3, 30)]).all (fun _ v => v % 10 == 0)
-- filterM in `Id` agrees with the pure filter; it visits every entry in ascending key order; and in
-- `Except` a throwing predicate short-circuits at the first offending entry (key 300 is never seen).
#guard Id.run ((NatMap.ofList [(1, 10), (2, 20), (3, 30), (4, 40)]).filterM (fun _ v => pure (v % 20 == 0)))
        = (NatMap.ofList [(1, 10), (2, 20), (3, 30), (4, 40)]).filter (fun _ v => v % 20 == 0)
#guard (((NatMap.ofList [(1, 10), (5000, 3)]).filterM (mo := StateM (List (Nat × Nat)))
          (fun k v => do modify (· ++ [(k, v)]); pure true)).run []).2 = [(1, 10), (5000, 3)]
#guard (match ((NatMap.ofList [(1, 10), (200, 1), (5, 50), (300, 2)]).filterM
          (fun k _ => if k ≥ 100 then throw k else pure true) : Except Nat (NatMap Nat)) with
        | .error e => e | .ok _ => 0) = 200

-- map: applies the function to every value, preserving keys and structure (including across heights)
#guard ((NatMap.ofList [(1, 10), (2, 20), (5000, 3)]).map (· + 1)).toList = [(1, 11), (2, 21), (5000, 4)]
#guard (NatMap.empty.map (· + 1) : NatMap Nat) = NatMap.empty
#guard ((NatMap.ofList [(1, 5), (2, 7)]).map (· * 2)).get? 2 = some 14
#guard ((NatMap.ofList [(1, 5), (2, 7)]).map (fun _ => true)).toList = [(1, true), (2, true)]  -- changes value type
-- the `Functor` instance: `<$>` is `NatMap.map`
#guard ((· * 2) <$> NatMap.ofList [(1, 5), (2, 7)]).get? 1 = some 10
#guard (id <$> NatMap.ofList [(1, 5), (2, 7)] : NatMap Nat) = NatMap.ofList [(1, 5), (2, 7)]

-- join: collisions combined (sum), others copied through
#guard ((NatMap.ofList [(1, 10), (2, 20)]).join (· + ·) (NatMap.ofList [(2, 2), (3, 3)])).toList
        = [(1, 10), (2, 22), (3, 3)]
#guard m1.join (· + ·) NatMap.empty = m1                              -- right identity
#guard (NatMap.empty : NatMap Nat).join (· + ·) m1 = m1              -- left identity
#guard m1.join (fun a _ => a) m1 = m1                                 -- idempotent (left-biased)

-- meet: only shared keys survive, combined
#guard ((NatMap.ofList [(1, 10), (2, 20)]).meet (· + ·) (NatMap.ofList [(2, 2), (3, 3)])).toList
        = [(2, 22)]
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
        = [(1, 11), (2, 20), (5000, 500)]                                              -- rhs taller
#guard ((NatMap.ofList [(1, 1), (5000, 500)]).join (· + ·) (NatMap.ofList [(1, 10), (2, 20)])).toList
        = [(1, 11), (2, 20), (5000, 500)]                                              -- lhs taller
-- left-biased combine pins down argument order across heights (left value must win both ways)
#guard ((NatMap.ofList [(1, 10)]).join (fun x _ => x) (NatMap.ofList [(1, 99), (5000, 500)])).toList
        = [(1, 10), (5000, 500)]                                                       -- rhs taller
#guard ((NatMap.ofList [(1, 10), (5000, 500)]).join (fun x _ => x) (NatMap.ofList [(1, 99)])).toList
        = [(1, 10), (5000, 500)]                                                       -- lhs taller (flipped)
-- `join_comm` flip law: swapping operands and flipping the (non-symmetric) combine is the identity
#guard (NatMap.ofList [(1, 10), (2, 20)]).join (fun x _ => x) (NatMap.ofList [(1, 99), (5000, 5)])
     = (NatMap.ofList [(1, 99), (5000, 5)]).join (fun _ y => y) (NatMap.ofList [(1, 10), (2, 20)])

-- meet: only shared keys survive at the smaller height, taller operand on either side
#guard ((NatMap.ofList [(1, 10), (2, 20), (5000, 500)]).meet (· + ·) (NatMap.ofList [(1, 1), (3, 3)])).toList
        = [(1, 11)]                                                                    -- lhs taller
#guard ((NatMap.ofList [(1, 1), (3, 3)]).meet (· + ·) (NatMap.ofList [(1, 10), (2, 20), (5000, 500)])).toList
        = [(1, 11)]                                                                    -- rhs taller
#guard ((NatMap.ofList [(1, 10), (5000, 5)]).meet (fun x _ => x) (NatMap.ofList [(1, 99)])).toList
        = [(1, 10)]                                                                    -- lhs taller (flipped)
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
#guard (p.meet (· + ·) q).toList = [(2, 22), (40, 440)]
-- domain of join = union of domains; domain of meet = intersection
#guard (p.join (· + ·) q).size = 5
#guard (p.meet (· + ·) q).size = 2
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
#guard hash (NatMap.ofList [(1, 10), (2, 20)]) = hash (NatMap.ofList [(2, 20), (1, 10)])

-- printing: `toString` braces `k ↦ v` entries ascending; `repr` is valid Lean rebuilding the map
#guard toString (NatMap.ofList [(2, 20), (1, 10)]) = "{1 ↦ 10, 2 ↦ 20}"
#guard toString (NatMap.empty : NatMap Nat) = "{}"
#guard reprStr (NatMap.ofList [(2, 20), (1, 10)]) = "NatMap.ofList [(1, 10), (2, 20)]"

end Tests

----------------------------------------------------------------------------------------------------
-- Theorems
----------------------------------------------------------------------------------------------------

/-! ### `NatMap.map` is functorial

`NatMap.map f = PTree.map (Node.map f)`, so the functor laws lift the `PTree.map` laws
(`map_eq_id`/`map_comp`/`get?_map`) with `Node`'s leaf-level laws (`Node.map_id`/`map_comp`/`get?_map`)
supplying the per-leaf obligations. Two maps are equal once their trees are (`NatCollection.ext_tree`). -/

namespace NatMap

variable {α : Type u}

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

/-- `join` is associative when its combine is associative. (Values at coinciding keys are resolved
`combine left right`, so associativity of the result needs associativity of `combine`.) -/
theorem join_assoc (combine : α → α → α)
    (hassoc : ∀ x y z, combine (combine x y) z = combine x (combine y z))
    (m₁ m₂ m₃ : NatMap α) :
    (m₁.join combine m₂).join combine m₃ = m₁.join combine (m₂.join combine m₃) :=
  NatCollection.join_assoc combine hassoc m₁ m₂ m₃

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

/-- `meet` is associative when its combine is associative. (Values at coinciding keys are resolved
`combine left right`, so associativity of the result needs associativity of `combine`.) -/
theorem meet_assoc (combine : α → α → α)
    (hassoc : ∀ x y z, combine (combine x y) z = combine x (combine y z))
    (m₁ m₂ m₃ : NatMap α) :
    (m₁.meet combine m₂).meet combine m₃ = m₁.meet combine (m₂.meet combine m₃) :=
  NatCollection.meet_assoc combine hassoc m₁ m₂ m₃

/-- The empty map restricts every map (its domain is vacuously a subset). -/
@[simp, grind =]
theorem restricts_empty_left (rel : α → α → Bool) (m : NatMap α) :
    NatMap.empty.restricts rel m = true := NatCollection.restricts_empty_left rel m

/-- `restricts` is reflexive: a map restricts itself whenever `rel` holds on equal values
(`∀ x, rel x x = true`). Plain (not `@[simp]`): the `rel`-reflexivity hypothesis is a side goal
`simp` can't discharge for an arbitrary `rel`. -/
theorem restricts_refl (rel : α → α → Bool) (hrefl : ∀ x, rel x x = true)
    (m : NatMap α) : m.restricts rel m = true := NatCollection.restricts_refl rel hrefl m

/-- `restricts` is transitive when `rel` is a preorder (reflexive and transitive): a domain
inclusion with `rel`-related values composes, the values via `rel`-transitivity. Reflexivity is
inherited from the generic theorem (it is only needed there for the *set* leaf). -/
theorem restricts_trans (rel : α → α → Bool) (hrefl : ∀ x, rel x x = true)
    (htrans : ∀ x y z, rel x y = true → rel y z = true → rel x z = true)
    (m₁ m₂ m₃ : NatMap α) :
    m₁.restricts rel m₂ = true → m₂.restricts rel m₃ = true → m₁.restricts rel m₃ = true :=
  NatCollection.restricts_trans rel hrefl htrans m₁ m₂ m₃

/-- `restricts` is anti-symmetric when `rel` is reflexive and anti-symmetric: mutual restriction
means equal domains whose values are `rel`-related both ways, which `rel`-antisymmetry collapses
to value equality at every key — so the maps are equal. Reflexivity is inherited from the generic
theorem (only needed there for the *set* leaf). -/
theorem restricts_antisymm (rel : α → α → Bool) (hrefl : ∀ x, rel x x = true)
    (hantisymm : ∀ x y, rel x y = true → rel y x = true → x = y)
    (m₁ m₂ : NatMap α) :
    m₁.restricts rel m₂ = true → m₂.restricts rel m₁ = true → m₁ = m₂ :=
  NatCollection.restricts_antisymm rel hrefl hantisymm m₁ m₂

/-- `meet` is a lower bound on the left: `m.meet combine n` restricts `m`, provided the combine
yields a `rel`-smaller value than its left argument (`hle`). For sets-as-maps this is just domain
shrinkage; for maps it additionally needs the combined value to refine the left value. -/
theorem meet_restricts_left (rel : α → α → Bool) (hrefl : ∀ x, rel x x = true)
    (combine : α → α → α) (hle : ∀ x y, rel (combine x y) x = true) (m n : NatMap α) :
    (m.meet combine n).restricts rel m = true :=
  NatCollection.meet_restricts_left rel hrefl combine hle m n

/-- `meet` is a lower bound on the right: `m.meet combine n` restricts `n`, provided the combine
yields a `rel`-smaller value than its right argument (`hle`). -/
theorem meet_restricts_right (rel : α → α → Bool) (hrefl : ∀ x, rel x x = true)
    (combine : α → α → α) (hle : ∀ x y, rel (combine x y) y = true) (m n : NatMap α) :
    (m.meet combine n).restricts rel n = true :=
  NatCollection.meet_restricts_right rel hrefl combine hle m n

/-- `meet` is the greatest lower bound: any `m` restricting both `a` and `b` also restricts their
`meet`, provided the combine is a greatest lower bound for `rel` (`hglb`: a value below both `x`
and `y` is below `combine x y`). Together with `meet_restricts_left`/`_right`, this says `meet` is
the infimum of `a` and `b` in the refinement order. -/
theorem restricts_meet (rel : α → α → Bool) (hrefl : ∀ x, rel x x = true) (combine : α → α → α)
    (hglb : ∀ w x y, rel w x = true → rel w y = true → rel w (combine x y) = true)
    (m a b : NatMap α)
    (hma : m.restricts rel a = true) (hmb : m.restricts rel b = true) :
    m.restricts rel (a.meet combine b) = true :=
  NatCollection.meet_glb rel hrefl combine hglb m a b hma hmb

/-- `join` is an upper bound on the left: `m` restricts `m.join combine n`, provided the combine
yields a `rel`-greater value than its left argument (`hle`). -/
theorem restricts_join_left (rel : α → α → Bool) (hrefl : ∀ x, rel x x = true)
    (combine : α → α → α) (hle : ∀ x y, rel x (combine x y) = true) (m n : NatMap α) :
    m.restricts rel (m.join combine n) = true :=
  NatCollection.restricts_join_left rel hrefl combine hle m n

/-- `join` is an upper bound on the right: `n` restricts `m.join combine n`, provided the combine
yields a `rel`-greater value than its right argument (`hre`). -/
theorem restricts_join_right (rel : α → α → Bool) (hrefl : ∀ x, rel x x = true)
    (combine : α → α → α) (hre : ∀ x y, rel y (combine x y) = true) (m n : NatMap α) :
    n.restricts rel (m.join combine n) = true :=
  NatCollection.restricts_join_right rel hrefl combine hre m n

/-- `join` is the least upper bound: any `m` that both `a` and `b` restrict is also restricted by
their `join`, provided the combine is a least upper bound for `rel` (`hlub`). Together with
`restricts_join_left`/`_right`, this says `join` is the supremum of `a` and `b`. -/
theorem join_restricts (rel : α → α → Bool) (hrefl : ∀ x, rel x x = true) (combine : α → α → α)
    (hlub : ∀ x y w, rel x w = true → rel y w = true → rel (combine x y) w = true)
    (a b m : NatMap α)
    (ham : a.restricts rel m = true) (hbm : b.restricts rel m = true) :
    (a.join combine b).restricts rel m = true :=
  NatCollection.join_lub rel hrefl combine hlub a b m ham hbm

/-- Looking up a freshly-inserted entry returns the inserted value. -/
@[simp]
theorem get?_insert_self (m : NatMap α) (k : Nat) (v : α) : (m.insert k v).get? k = some v := by
  show NatCollection.get? (NatCollection.insert m k v) k = some v
  rw [NatCollection.get?_insert m k v k, if_pos rfl]

/-- Looking up any key after an insert: the inserted key reads the new value, every other key is
read unchanged. -/
theorem get?_insert (m : NatMap α) (k : Nat) (v : α) (j : Nat) :
    (m.insert k v).get? j = if j = k then some v else m.get? j :=
  NatCollection.get?_insert m k v j

/-- Inserting an entry already present (key `k` already mapped to `v`) returns the same map. -/
theorem insert_of_get? {m : NatMap α} {k : Nat} {v : α} (h : m.get? k = some v) :
    m.insert k v = m := by
  apply NatCollection.ext_get?
  intro j
  show NatCollection.get? (NatCollection.insert m k v) j = NatCollection.get? m j
  rw [NatCollection.get?_insert m k v j]
  by_cases hj : j = k
  · rw [if_pos hj, hj]; exact h.symm
  · rw [if_neg hj]

/-- Joining a map with itself preserves its keys — *regardless* of the value-combining function:
a key survives on either side, so the set of keys is unchanged. (The values do change, to
`combine v v`; see `get?_join_self`.) -/
@[simp]
theorem mem_join_self (combine : α → α → α) (m : NatMap α) (k : Nat) :
    k ∈ m.join combine m ↔ k ∈ m := by
  show NatCollection.contains (NatCollection.join combine m m) k = true
      ↔ NatCollection.contains m k = true
  simp only [NatCollection.contains_eq]
  rw [NatCollection.get?_join combine m m k]
  cases NatCollection.get? m k <;> simp [optVjoin]

/-- Looking up a key after joining a map with itself: present keys read `combine v v`, absent keys
stay absent. The precise (combine-dependent) companion of `mem_join_self`. -/
theorem get?_join_self (combine : α → α → α) (m : NatMap α) (k : Nat) :
    (m.join combine m).get? k = (m.get? k).map (fun v => combine v v) := by
  show NatCollection.get? (NatCollection.join combine m m) k
      = (NatCollection.get? m k).map (fun v => combine v v)
  rw [NatCollection.get?_join combine m m k]
  cases NatCollection.get? m k <;> rfl

/-- When the value-combining function is idempotent (`combine v v = v`), joining a map with itself
returns the map. -/
theorem join_self_of_idem (combine : α → α → α) (hidem : ∀ v, combine v v = v) (m : NatMap α) :
    m.join combine m = m := by
  apply NatCollection.ext_get?
  intro k
  show NatCollection.get? (NatCollection.join combine m m) k = NatCollection.get? m k
  rw [NatCollection.get?_join combine m m k]
  cases NatCollection.get? m k with
  | none => rfl
  | some v => simp only [optVjoin, hidem]

/-- Meeting a map with itself preserves its keys — *regardless* of the value-combining function:
every key is shared with itself, so the set of keys is unchanged. (The values do change, to
`combine v v`; see `get?_meet_self`.) -/
@[simp]
theorem mem_meet_self (combine : α → α → α) (m : NatMap α) (k : Nat) :
    k ∈ m.meet combine m ↔ k ∈ m := by
  show NatCollection.contains (NatCollection.meet combine m m) k = true
      ↔ NatCollection.contains m k = true
  simp only [NatCollection.contains_eq]
  rw [NatCollection.get?_meet combine m m k]
  cases NatCollection.get? m k <;> simp [optVmeet]

/-- Looking up a key after meeting a map with itself: present keys read `combine v v`, absent keys
stay absent. The precise (combine-dependent) companion of `mem_meet_self`. -/
theorem get?_meet_self (combine : α → α → α) (m : NatMap α) (k : Nat) :
    (m.meet combine m).get? k = (m.get? k).map (fun v => combine v v) := by
  show NatCollection.get? (NatCollection.meet combine m m) k
      = (NatCollection.get? m k).map (fun v => combine v v)
  rw [NatCollection.get?_meet combine m m k]
  cases NatCollection.get? m k <;> rfl

/-- When the value-combining function is idempotent (`combine v v = v`), meeting a map with itself
returns the map. -/
theorem meet_self_of_idem (combine : α → α → α) (hidem : ∀ v, combine v v = v) (m : NatMap α) :
    m.meet combine m = m := by
  apply NatCollection.ext_get?
  intro k
  show NatCollection.get? (NatCollection.meet combine m m) k = NatCollection.get? m k
  rw [NatCollection.get?_meet combine m m k]
  cases NatCollection.get? m k with
  | none => rfl
  | some v => simp only [optVmeet, hidem]

/-- **`meet` distributes over `join`** (`NatMap` wrapper of `meet_join_distrib`). Needs only that the
meet combine distributes over the join combine pointwise. -/
theorem meet_join_distrib (combineMeet combineJoin : α → α → α)
    (hdist : ∀ x y z,
      combineMeet x (combineJoin y z) = combineJoin (combineMeet x y) (combineMeet x z))
    (a b e : NatMap α) :
    a.meet combineMeet (b.join combineJoin e)
      = (a.meet combineMeet b).join combineJoin (a.meet combineMeet e) :=
  NatCollection.meet_join_distrib combineMeet combineJoin hdist a b e

/-- **`join` distributes over `meet`** (`NatMap` wrapper of `join_meet_distrib`). Needs the meet
combine to be idempotent (`hidem`) and to absorb the join combine (`habs1`/`habs2`), and the join
combine to distribute over the meet combine (`hdist`) — i.e. the combines form a distributive
lattice on values. -/
theorem join_meet_distrib (combineJoin combineMeet : α → α → α)
    (hidem : ∀ x, combineMeet x x = x)
    (habs1 : ∀ x y, combineMeet (combineJoin x y) x = x)
    (habs2 : ∀ x y, combineMeet x (combineJoin x y) = x)
    (hdist : ∀ x y z,
      combineJoin x (combineMeet y z) = combineMeet (combineJoin x y) (combineJoin x z))
    (a b e : NatMap α) :
    a.join combineJoin (b.meet combineMeet e)
      = (a.join combineJoin b).meet combineMeet (a.join combineJoin e) :=
  NatCollection.join_meet_distrib combineJoin combineMeet hidem habs1 habs2 hdist a b e

/-- **Functor identity law**: mapping `id` returns the map unchanged. -/
@[simp, grind =]
theorem map_id {α : Type u} (m : NatMap α) : NatMap.map id m = m := by
  apply NatCollection.ext_tree
  exact PTree.map_eq_id (Node.map id) (fun l => Node.map_id l) m.tree

/-- **Functor composition law**: mapping a composition is the composition of maps. -/
theorem map_comp {α β γ : Type u} (f : α → β) (g : β → γ) (m : NatMap α) :
    NatMap.map (g ∘ f) m = NatMap.map g (NatMap.map f m) := by
  apply NatCollection.ext_tree
  show PTree.map (Node.map (g ∘ f)) m.tree
      = PTree.map (Node.map g) (PTree.map (Node.map f) m.tree)
  rw [PTree.map_congr (Node.map (g ∘ f)) (fun l => Node.map g (Node.map f l))
        (fun n => Node.map_comp f g n) m.tree]
  exact PTree.map_comp (Node.map f) (Node.map g) m.tree

/-- Looking up a key in a mapped map applies `f` to the value (the `get?` spec of `map`). -/
theorem get?_map {α β : Type u} (f : α → β) (m : NatMap α) (k : Nat) :
    (m.map f).get? k = (m.get? k).map f := by
  show PTree.get? k (PTree.map (Node.map f) m.tree) = (PTree.get? k m.tree).map f
  exact PTree.get?_map (Node.map f) f (fun l i => Node.get?_map f l i) k m.tree

/-- `domain` preserves the size: the key set has exactly as many elements as the map has entries.
Immediate from `PTree.size_map`, since a map leaf and its mask have the same population count. -/
@[simp]
theorem size_domain (m : NatMap α) : m.domain.size = m.size := by
  show PTree.size (PTree.map (fun l => l.positionsMask) m.tree) = PTree.size m.tree
  exact PTree.size_map (fun l => l.positionsMask) (fun _ => rfl) m.tree

/-- A key is in the domain exactly when it is in the map (`Bool` form): both sides test the same
mask bit, on tries of the same shape. -/
theorem contains_domain (m : NatMap α) (k : Nat) : m.domain.contains k = m.contains k := by
  show PTree.contains k (PTree.map (fun l => l.positionsMask) m.tree) = PTree.contains k m.tree
  exact PTree.contains_map (fun l => l.positionsMask) (fun _ _ => rfl) k m.tree

/-- A key is in the domain exactly when it is in the map. -/
@[simp]
theorem mem_domain (m : NatMap α) (k : Nat) : k ∈ m.domain ↔ k ∈ m := by
  show m.domain.contains k = true ↔ m.contains k = true
  rw [contains_domain]

/-- The entry `minEntry?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_minEntry? {m : NatMap α} {k : Nat} {v : α} (h : m.minEntry? = some (k, v)) :
    m.get? k = some v :=
  NatCollection.get?_of_minEntry? m k v h

/-- The entry `maxEntry?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_maxEntry? {m : NatMap α} {k : Nat} {v : α} (h : m.maxEntry? = some (k, v)) :
    m.get? k = some v :=
  NatCollection.get?_of_maxEntry? m k v h

/-- The least key is present: a `minKey? = some k` answer is a key of the map. -/
theorem minKey?_mem {m : NatMap α} {k : Nat} (h : m.minKey? = some k) : k ∈ m :=
  NatCollection.contains_of_minKey? m k h

/-- The least key is a lower bound: no key of the map is below `minKey?`'s answer. -/
theorem minKey?_le {m : NatMap α} {k j : Nat} (h : m.minKey? = some k) (hj : j ∈ m) : k ≤ j :=
  NatCollection.minKey?_le m k j h hj

/-- The greatest key is present: a `maxKey? = some k` answer is a key of the map. -/
theorem maxKey?_mem {m : NatMap α} {k : Nat} (h : m.maxKey? = some k) : k ∈ m :=
  NatCollection.contains_of_maxKey? m k h

/-- The greatest key is an upper bound: no key of the map is above `maxKey?`'s answer. -/
theorem le_maxKey? {m : NatMap α} {k j : Nat} (h : m.maxKey? = some k) (hj : j ∈ m) : j ≤ k :=
  NatCollection.le_maxKey? m k j h hj

/-- The entry `entryGT?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_entryGT? {m : NatMap α} {k j : Nat} {v : α} (h : m.entryGT? k = some (j, v)) :
    m.get? j = some v :=
  NatCollection.get?_of_entryGT? m k j v h

/-- `entryGT?`'s key is strictly greater than the query key. -/
theorem entryGT?_gt {m : NatMap α} {k j : Nat} {v : α} (h : m.entryGT? k = some (j, v)) :
    k < j :=
  NatCollection.entryGT?_gt m k j v h

/-- `entryGT?` returns the *least* key beyond the query key. -/
theorem entryGT?_le {m : NatMap α} {k j' j : Nat} {v : α} (h : m.entryGT? k = some (j', v))
    (hj : j ∈ m) (hk : k < j) : j' ≤ j :=
  NatCollection.entryGT?_le m k j' v j h hj hk

/-- A `none` from `entryGT?` is complete: no key of the map lies strictly above the query key. -/
theorem le_of_entryGT?_eq_none {m : NatMap α} {k j : Nat} (h : m.entryGT? k = none)
    (hj : j ∈ m) : j ≤ k :=
  NatCollection.le_of_entryGT?_eq_none m k h j hj

/-- The entry `entryLT?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_entryLT? {m : NatMap α} {k j : Nat} {v : α} (h : m.entryLT? k = some (j, v)) :
    m.get? j = some v :=
  NatCollection.get?_of_entryLT? m k j v h

/-- `entryLT?`'s key is strictly less than the query key. -/
theorem entryLT?_lt {m : NatMap α} {k j : Nat} {v : α} (h : m.entryLT? k = some (j, v)) :
    j < k :=
  NatCollection.entryLT?_lt m k j v h

/-- `entryLT?` returns the *greatest* key below the query key. -/
theorem le_entryLT? {m : NatMap α} {k j' j : Nat} {v : α} (h : m.entryLT? k = some (j', v))
    (hj : j ∈ m) (hk : j < k) : j ≤ j' :=
  NatCollection.le_entryLT? m k j' v j h hj hk

/-- A `none` from `entryLT?` is complete: no key of the map lies strictly below the query key. -/
theorem ge_of_entryLT?_eq_none {m : NatMap α} {k j : Nat} (h : m.entryLT? k = none)
    (hj : j ∈ m) : k ≤ j :=
  NatCollection.ge_of_entryLT?_eq_none m k h j hj

/-- The entry `entryGE?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_entryGE? {m : NatMap α} {k j : Nat} {v : α} (h : m.entryGE? k = some (j, v)) :
    m.get? j = some v :=
  NatCollection.get?_of_entryGE? m k j v h

/-- `entryGE?`'s key is at or above the query key (it is `k` itself exactly when `k` is
present). -/
theorem entryGE?_ge {m : NatMap α} {k j : Nat} {v : α} (h : m.entryGE? k = some (j, v)) :
    k ≤ j :=
  NatCollection.entryGE?_ge m k j v h

/-- `entryGE?` returns the *least* key at or beyond the query key. -/
theorem entryGE?_le {m : NatMap α} {k j' j : Nat} {v : α} (h : m.entryGE? k = some (j', v))
    (hj : j ∈ m) (hk : k ≤ j) : j' ≤ j :=
  NatCollection.entryGE?_le m k j' v j h hj hk

/-- A `none` from `entryGE?` is complete: every key of the map lies strictly below the query
key. -/
theorem lt_of_entryGE?_eq_none {m : NatMap α} {k j : Nat} (h : m.entryGE? k = none)
    (hj : j ∈ m) : j < k :=
  NatCollection.lt_of_entryGE?_eq_none m k h j hj

/-- The entry `entryLE?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_entryLE? {m : NatMap α} {k j : Nat} {v : α} (h : m.entryLE? k = some (j, v)) :
    m.get? j = some v :=
  NatCollection.get?_of_entryLE? m k j v h

/-- `entryLE?`'s key is at or below the query key (it is `k` itself exactly when `k` is
present). -/
theorem entryLE?_le {m : NatMap α} {k j : Nat} {v : α} (h : m.entryLE? k = some (j, v)) :
    j ≤ k :=
  NatCollection.entryLE?_le m k j v h

/-- `entryLE?` returns the *greatest* key at or below the query key. -/
theorem le_entryLE? {m : NatMap α} {k j' j : Nat} {v : α} (h : m.entryLE? k = some (j', v))
    (hj : j ∈ m) (hk : j ≤ k) : j ≤ j' :=
  NatCollection.le_entryLE? m k j' v j h hj hk

/-- A `none` from `entryLE?` is complete: every key of the map lies strictly above the query
key. -/
theorem gt_of_entryLE?_eq_none {m : NatMap α} {k j : Nat} (h : m.entryLE? k = none)
    (hj : j ∈ m) : k < j :=
  NatCollection.gt_of_entryLE?_eq_none m k h j hj

/-- `popMinEntry?` pops the least entry: its entry is `minEntry?`'s answer (so
`get?_of_minEntry?` and `minEntry?_le` apply to it). -/
theorem minEntry?_of_popMinEntry? {m : NatMap α} {e : Nat × α} {m' : NatMap α}
    (h : m.popMinEntry? = some (e, m')) : m.minEntry? = some e :=
  NatCollection.minEntry?_of_popMinEntry? m e m' h

/-- `popMinEntry?`'s rest is the map with the popped key erased. -/
theorem popMinEntry?_erase {m : NatMap α} {e : Nat × α} {m' : NatMap α}
    (h : m.popMinEntry? = some (e, m')) : m' = m.erase e.1 :=
  NatCollection.popMinEntry?_erase m e m' h

/-- `popMinEntry?` answers `none` exactly on the empty map (totality: a non-empty map always
pops). -/
theorem popMinEntry?_eq_none {m : NatMap α} : m.popMinEntry? = none ↔ m = NatMap.empty :=
  NatCollection.popMinEntry?_eq_none m

/-- `popMaxEntry?` pops the greatest entry: its entry is `maxEntry?`'s answer (so
`get?_of_maxEntry?` and `le_maxEntry?` apply to it). -/
theorem maxEntry?_of_popMaxEntry? {m : NatMap α} {e : Nat × α} {m' : NatMap α}
    (h : m.popMaxEntry? = some (e, m')) : m.maxEntry? = some e :=
  NatCollection.maxEntry?_of_popMaxEntry? m e m' h

/-- `popMaxEntry?`'s rest is the map with the popped key erased. -/
theorem popMaxEntry?_erase {m : NatMap α} {e : Nat × α} {m' : NatMap α}
    (h : m.popMaxEntry? = some (e, m')) : m' = m.erase e.1 :=
  NatCollection.popMaxEntry?_erase m e m' h

/-- `popMaxEntry?` answers `none` exactly on the empty map. -/
theorem popMaxEntry?_eq_none {m : NatMap α} : m.popMaxEntry? = none ↔ m = NatMap.empty :=
  NatCollection.popMaxEntry?_eq_none m

/-- Lookup after `erase`: the erased key reads `none`, every other key is unchanged. -/
theorem get?_erase (m : NatMap α) (k j : Nat) :
    (m.erase k).get? j = if j = k then none else m.get? j :=
  NatCollection.get?_erase m k j

/-- Lookup in `split`'s left part: exactly the entries with key strictly below the split key. -/
theorem get?_split_left (m : NatMap α) (k j : Nat) :
    (m.split k).1.get? j = if j < k then m.get? j else none :=
  NatCollection.get?_filterLt m k j

/-- `split`'s middle component is the value at the split key itself. -/
theorem split_at (m : NatMap α) (k : Nat) : (m.split k).2.1 = m.get? k := rfl

/-- Lookup in `split`'s right part: exactly the entries with key strictly above the split key. -/
theorem get?_split_right (m : NatMap α) (k j : Nat) :
    (m.split k).2.2.get? j = if k < j then m.get? j else none :=
  NatCollection.get?_filterGE m (k + 1) j

/-- Lookup in `range`: a key reads through exactly when it lies in the inclusive window
`[lo, hi]`. -/
theorem get?_range (m : NatMap α) (lo hi j : Nat) :
    (m.range lo hi).get? j = if lo ≤ j ∧ j ≤ hi then m.get? j else none :=
  NatCollection.get?_range m lo hi j

/-- Membership in `split`'s left part: exactly the keys strictly below the split key. -/
theorem mem_split_left {m : NatMap α} {k j : Nat} : j ∈ (m.split k).1 ↔ j ∈ m ∧ j < k := by
  show NatCollection.contains (NatCollection.filterLt m k) j = true ↔ _
  rw [NatCollection.contains_eq, NatCollection.get?_filterLt]
  constructor
  · intro h
    by_cases hjk : j < k
    · rw [if_pos hjk] at h
      refine ⟨?_, hjk⟩
      show NatCollection.contains m j = true
      rw [NatCollection.contains_eq]
      exact h
    · rw [if_neg hjk] at h
      simp at h
  · intro h
    obtain ⟨hm, hjk⟩ := h
    rw [if_pos hjk]
    replace hm : NatCollection.contains m j = true := hm
    rw [NatCollection.contains_eq] at hm
    exact hm

/-- Membership in `split`'s right part: exactly the keys strictly above the split key. -/
theorem mem_split_right {m : NatMap α} {k j : Nat} : j ∈ (m.split k).2.2 ↔ j ∈ m ∧ k < j := by
  show NatCollection.contains (NatCollection.filterGE m (k + 1)) j = true ↔ _
  rw [NatCollection.contains_eq, NatCollection.get?_filterGE]
  constructor
  · intro h
    by_cases hjk : k + 1 ≤ j
    · rw [if_pos hjk] at h
      refine ⟨?_, hjk⟩
      show NatCollection.contains m j = true
      rw [NatCollection.contains_eq]
      exact h
    · rw [if_neg hjk] at h
      simp at h
  · intro h
    obtain ⟨hm, hjk⟩ := h
    rw [if_pos (show k + 1 ≤ j from hjk)]
    replace hm : NatCollection.contains m j = true := hm
    rw [NatCollection.contains_eq] at hm
    exact hm

/-- Every key of `split`'s left part lies strictly below the split key. -/
theorem lt_of_mem_split_left {m : NatMap α} {k j : Nat} (h : j ∈ (m.split k).1) : j < k :=
  (mem_split_left.mp h).2

/-- Every key of `split`'s right part lies strictly above the split key. -/
theorem lt_of_mem_split_right {m : NatMap α} {k j : Nat} (h : j ∈ (m.split k).2.2) : k < j :=
  (mem_split_right.mp h).2

/-- Membership in `range`: exactly the keys within the inclusive window `[lo, hi]`. -/
theorem mem_range {m : NatMap α} {lo hi j : Nat} :
    j ∈ m.range lo hi ↔ j ∈ m ∧ lo ≤ j ∧ j ≤ hi := by
  show NatCollection.contains (NatCollection.range m lo hi) j = true ↔ _
  rw [NatCollection.contains_eq, NatCollection.get?_range]
  constructor
  · intro h
    by_cases hin : lo ≤ j ∧ j ≤ hi
    · rw [if_pos hin] at h
      refine ⟨?_, hin.1, hin.2⟩
      show NatCollection.contains m j = true
      rw [NatCollection.contains_eq]
      exact h
    · rw [if_neg hin] at h
      simp at h
  · intro h
    obtain ⟨hm, h1, h2⟩ := h
    rw [if_pos ⟨h1, h2⟩]
    replace hm : NatCollection.contains m j = true := hm
    rw [NatCollection.contains_eq] at hm
    exact hm

/-- Membership after `erase`: `j` survives exactly when it was present and is not the erased
key. -/
theorem mem_erase {m : NatMap α} {k j : Nat} : j ∈ m.erase k ↔ j ∈ m ∧ j ≠ k := by
  show NatCollection.contains (NatCollection.erase m k) j = true ↔ _
  rw [NatCollection.contains_erase, Bool.and_eq_true]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, ?_⟩
    intro he
    rw [he] at h2
    simp at h2
  · intro h
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, by simp [h2]⟩

/-- Disjointness characterization: `m.isDisjoint m'` holds exactly when the two maps share no key
(values are irrelevant). -/
theorem isDisjoint_iff {m m' : NatMap α} : m.isDisjoint m' = true ↔ ∀ k, k ∈ m → k ∉ m' := by
  show NatCollection.isDisjoint m m' = true ↔ _
  rw [NatCollection.isDisjoint_iff]
  constructor
  · intro h k hks hkt
    have hpair := h k
    replace hks : NatCollection.contains m k = true := hks
    replace hkt : NatCollection.contains m' k = true := hkt
    rw [hks, hkt] at hpair
    exact absurd hpair (by decide)
  · intro h k
    cases hks : NatCollection.contains m k with
    | false => rw [Bool.false_and]
    | true => cases hkt : NatCollection.contains m' k with
      | false => rw [Bool.and_false]
      | true => exact absurd (show k ∈ m' from hkt) (h k hks)

/-- Disjointness is symmetric: if `m` is disjoint from `m'`, then `m'` is disjoint from `m`. -/
theorem isDisjoint_symm {m m' : NatMap α} (h : m.isDisjoint m' = true) :
    m'.isDisjoint m = true :=
  NatCollection.isDisjoint_symm h

/-- No key of `m` lies in `m'` when the two maps are disjoint. -/
theorem not_mem_of_isDisjoint {m m' : NatMap α} {k : Nat} (h : m.isDisjoint m' = true)
    (hk : k ∈ m) : k ∉ m' :=
  isDisjoint_iff.mp h k hk

/-- The empty map is a right identity of `diff`. -/
theorem diff_empty (m : NatMap α) : m.diff ∅ = m :=
  NatCollection.diff_empty m

/-- Subtracting a map from itself leaves the empty map. -/
theorem diff_self (m : NatMap α) : m.diff m = ∅ :=
  NatCollection.diff_self m

end NatMap

/-- `NatMap` is a lawful functor: `map` satisfies the identity and composition laws (and the
default `mapConst` agrees with `map ∘ const`). The proofs come straight from the structural
`NatMap.map_id`/`map_comp`, since `map` only rewrites values and preserves the trie shape. -/
instance : LawfulFunctor NatMap where
  map_const := rfl
  id_map := NatMap.map_id
  comp_map := NatMap.map_comp

end NatCol
