import NatCol.Map
import NatCol.IndexedSet

/-!
# `IndexedMap`: a map keyed by `Countable` values

An `IndexedMap κ V` is a bare `NatMap V` keyed by the `Countable` encoding of `κ`, bundled with
the invariant (`wf`) that every raw key decodes. Values are stored directly; keys live only as
trie positions and are decoded (`Countable.ofNat?`) on the way out — the map companion of
`IndexedSet`, and a win over hash maps whenever `toNat` is cheaper than hashing.

Ordered queries (`minEntry?`/`entryGT?`/`split`/`range`…) and the ordered theorems below speak
the **encoding order** (`Countable.toNat`); the bundled instances are all order-preserving, so
for them this is the natural order of the key type.
-/

namespace NatCol
----------------------------------------------------------------------------------------------------
-- Implementation
----------------------------------------------------------------------------------------------------

/-- A map from `κ` to `V` keyed by `κ`'s `Countable` encoding: a bare `NatMap V` together with
the invariant that every raw key is the encoding of some `κ` value. -/
structure IndexedMap (κ : Type u) [Countable κ] (V : Type v) where
  /-- The underlying `NatMap` from encodings to values. -/
  raw : NatMap V
  /-- Every raw key is the encoding of some `κ` value. -/
  wf : ∀ n, n ∈ raw → ∃ k : κ, Countable.toNat k = n

namespace IndexedMap

open Countable

variable {κ : Type u} [Countable κ] {V : Type v} {W : Type v}

/-- Two indexed maps with equal raw maps are equal — the `wf` proof is irrelevant (a `Prop`).
Every raw-level equation lifts through this. -/
theorem ext {m t : IndexedMap κ V} (h : m.raw = t.raw) : m = t := by
  obtain ⟨mr, mw⟩ := m
  obtain ⟨tr, tw⟩ := t
  subst h
  rfl

/-- The decode of a present raw key succeeds and is faithful — `wf` composed with the class
law. The workhorse behind every theorem that converts a raw answer back to `κ`. -/
theorem ofNat?_of_mem_raw {m : IndexedMap κ V} {n : Nat} (h : n ∈ m.raw) :
    ∃ k : κ, ofNat? n = some k ∧ toNat k = n := by
  obtain ⟨k, hk⟩ := m.wf n h
  exact ⟨k, ofNat?_eq_some_iff.mpr hk, hk⟩

/-- A key holding a value is present (the `get?` → membership bridge at the raw layer). -/
private theorem mem_of_get?_eq_some {m : NatMap V} {n : Nat} {v : V}
    (h : m.get? n = some v) : n ∈ m := by
  show NatCollection.contains m n = true
  rw [NatCollection.contains_eq, show NatCollection.get? m n = some v from h]
  rfl

/-- Transfer `wf` across an op whose result keys come from the input (the one-input case). -/
private theorem wf_of_subset (m : IndexedMap κ V) {t : NatMap V} (h : ∀ n, n ∈ t → n ∈ m.raw) :
    ∀ n, n ∈ t → ∃ k : κ, toNat k = n :=
  fun n hn => m.wf n (h n hn)

/-- Transfer `wf` across an op whose result keys come from either input (the two-input case). -/
private theorem wf_of_subset₂ (m t : IndexedMap κ V) {u : NatMap V}
    (h : ∀ n, n ∈ u → n ∈ m.raw ∨ n ∈ t.raw) : ∀ n, n ∈ u → ∃ k : κ, toNat k = n :=
  fun n hn => (h n hn).elim (m.wf n) (t.wf n)

instance [BEq V] : BEq (IndexedMap κ V) := ⟨fun m t => m.raw == t.raw⟩
instance [BEq V] [LawfulBEq V] : LawfulBEq (IndexedMap κ V) where
  eq_of_beq {m t} h := ext (eq_of_beq (show (m.raw == t.raw) = true from h))
  rfl {m} := beq_self_eq_true m.raw
instance [BEq V] [LawfulBEq V] : DecidableEq (IndexedMap κ V) := fun m t =>
  decidable_of_iff (m.raw = t.raw) ⟨ext, fun h => by rw [h]⟩
instance [Hashable V] : Hashable (IndexedMap κ V) := ⟨fun m => hash m.raw⟩
instance [BEq V] [LawfulBEq V] [Hashable V] : LawfulHashable (IndexedMap κ V) where
  hash_eq _ _ h := by rw [eq_of_beq h]
instance : EmptyCollection (IndexedMap κ V) :=
  ⟨⟨∅, fun n hn => by
      replace hn : NatCollection.contains NatCollection.empty n = true := hn
      rw [NatCollection.contains_eq, NatCollection.get?_empty] at hn
      exact absurd hn (by simp)⟩⟩

/-- The empty map. -/
def empty : IndexedMap κ V := ∅
def isEmpty (m : IndexedMap κ V) : Bool := m.raw.isEmpty
def size (m : IndexedMap κ V) : Nat := m.raw.size
def contains (m : IndexedMap κ V) (k : κ) : Bool := m.raw.contains (toNat k)
def get? (m : IndexedMap κ V) (k : κ) : Option V := m.raw.get? (toNat k)
def getD (m : IndexedMap κ V) (k : κ) (fallback : V) : V := (m.get? k).getD fallback
def insert (m : IndexedMap κ V) (k : κ) (v : V) : IndexedMap κ V :=
  ⟨m.raw.insert (toNat k) v, fun n hn =>
    (NatMap.mem_insert.mp hn).elim (m.wf n) fun hk => ⟨k, hk.symm⟩⟩
def erase (m : IndexedMap κ V) (k : κ) : IndexedMap κ V :=
  ⟨m.raw.erase (toNat k), m.wf_of_subset fun _ hn => (NatMap.mem_erase.mp hn).1⟩
/-- Rewrite the value at `k` through `f` when present; a no-op when absent. -/
def modify (m : IndexedMap κ V) (k : κ) (f : V → V) : IndexedMap κ V :=
  ⟨m.raw.modify (toNat k) f, m.wf_of_subset fun _ hn => NatMap.mem_modify.mp hn⟩
/-- Rewrite the entry at `k` through `f`: `f` receives the current value (`some v` if present,
`none` if absent) and returns the value to store, or `none` to leave the key absent. Generalizes
`insert`, `erase`, and `modify`. -/
def alter (m : IndexedMap κ V) (k : κ) (f : Option V → Option V) : IndexedMap κ V :=
  ⟨m.raw.alter (toNat k) f, fun n hn =>
    (NatMap.mem_of_mem_alter hn).elim (m.wf n) fun hk => ⟨k, hk.symm⟩⟩

/-- The least key in encoding order, `none` on the empty map. O(depth). The decode never fails
on a well-formed map (`wf`). -/
def minKey? (m : IndexedMap κ V) : Option κ := m.raw.minKey?.bind ofNat?
/-- The greatest key in encoding order, `none` on the empty map. O(depth). -/
def maxKey? (m : IndexedMap κ V) : Option κ := m.raw.maxKey?.bind ofNat?
/-- The entry with the least key in encoding order, `none` on the empty map. O(depth). -/
def minEntry? (m : IndexedMap κ V) : Option (κ × V) :=
  m.raw.minEntry?.bind fun e => (ofNat? e.1).map fun k => (k, e.2)
/-- The entry with the greatest key in encoding order, `none` on the empty map. O(depth). -/
def maxEntry? (m : IndexedMap κ V) : Option (κ × V) :=
  m.raw.maxEntry?.bind fun e => (ofNat? e.1).map fun k => (k, e.2)
/-- The entry with the least key strictly above `k` in encoding order (successor), `none` if
there is none. O(depth). -/
def entryGT? (m : IndexedMap κ V) (k : κ) : Option (κ × V) :=
  (m.raw.entryGT? (toNat k)).bind fun e => (ofNat? e.1).map fun k' => (k', e.2)
/-- The entry with the greatest key strictly below `k` in encoding order (predecessor), `none`
if there is none. O(depth). -/
def entryLT? (m : IndexedMap κ V) (k : κ) : Option (κ × V) :=
  (m.raw.entryLT? (toNat k)).bind fun e => (ofNat? e.1).map fun k' => (k', e.2)
/-- The entry with the least key at or above `k` in encoding order: the entry at `k` itself when
present, else the successor's. -/
def entryGE? (m : IndexedMap κ V) (k : κ) : Option (κ × V) :=
  (m.raw.entryGE? (toNat k)).bind fun e => (ofNat? e.1).map fun k' => (k', e.2)
/-- The entry with the greatest key at or below `k` in encoding order: the entry at `k` itself
when present, else the predecessor's. -/
def entryLE? (m : IndexedMap κ V) (k : κ) : Option (κ × V) :=
  (m.raw.entryLE? (toNat k)).bind fun e => (ofNat? e.1).map fun k' => (k', e.2)

/-- The least entry together with the map without it, `none` on the empty map (the
priority-queue step). `minEntry?` then `erase` — the same two walks the raw pop performs. -/
def popMinEntry? (m : IndexedMap κ V) : Option ((κ × V) × IndexedMap κ V) :=
  match m.minEntry? with
  | none => none
  | some e => some (e, m.erase e.1)
/-- The greatest entry together with the map without it, `none` on the empty map. -/
def popMaxEntry? (m : IndexedMap κ V) : Option ((κ × V) × IndexedMap κ V) :=
  match m.maxEntry? with
  | none => none
  | some e => some (e, m.erase e.1)

/-- Union; `combine` resolves values at coinciding keys. -/
def join (combine : V → V → V) (m₁ m₂ : IndexedMap κ V) : IndexedMap κ V :=
  ⟨NatMap.join combine m₁.raw m₂.raw,
   wf_of_subset₂ m₁ m₂ fun _ hn => (NatMap.mem_join combine m₁.raw m₂.raw _).mp hn⟩
/-- Intersection; `combine` resolves values at coinciding keys. -/
def meet (combine : V → V → V) (m₁ m₂ : IndexedMap κ V) : IndexedMap κ V :=
  ⟨NatMap.meet combine m₁.raw m₂.raw,
   m₁.wf_of_subset fun _ hn => ((NatMap.mem_meet combine m₁.raw m₂.raw _).mp hn).1⟩
/-- `m₁` restricts `m₂`: `m₁`'s domain ⊆ `m₂`'s, and `rel` holds on values at coinciding keys. -/
def restricts (rel : V → V → Bool) (m₁ m₂ : IndexedMap κ V) : Bool :=
  NatMap.restricts rel m₁.raw m₂.raw
/-- Whether `m₁` and `m₂` share no key (domain disjointness — values are irrelevant). -/
def isDisjoint (m₁ m₂ : IndexedMap κ V) : Bool := m₁.raw.isDisjoint m₂.raw
/-- Difference: the entries of `m₁` whose key is absent from `m₂` (`m₂`'s values are irrelevant;
surviving values are untouched). A structural merge walk. -/
def diff (m₁ m₂ : IndexedMap κ V) : IndexedMap κ V :=
  ⟨m₁.raw.diff m₂.raw, m₁.wf_of_subset fun _ hn => (NatMap.mem_diff.mp hn).1⟩
/-- Symmetric difference: the entries whose key is in exactly one of `m₁`, `m₂` (entries at
shared keys are dropped, whatever their values). A structural merge walk. -/
def symmDiff (m₁ m₂ : IndexedMap κ V) : IndexedMap κ V :=
  ⟨m₁.raw.symmDiff m₂.raw, wf_of_subset₂ m₁ m₂ fun _ hn =>
      (NatMap.mem_symmDiff.mp hn).elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)⟩
/-- Split at `k`: the entries with key below `k` (in encoding order), the value at `k` (if any),
and the entries with key above `k` — structural prunes along the routed path. -/
def split (m : IndexedMap κ V) (k : κ) : IndexedMap κ V × Option V × IndexedMap κ V :=
  (⟨(m.raw.split (toNat k)).1, m.wf_of_subset fun _ hn => (NatMap.mem_split_left.mp hn).1⟩,
   (m.raw.split (toNat k)).2.1,
   ⟨(m.raw.split (toNat k)).2.2, m.wf_of_subset fun _ hn => (NatMap.mem_split_right.mp hn).1⟩)
/-- The entries with key in the inclusive encoding-order range `[lo, hi]` — a double structural
prune. -/
def range (m : IndexedMap κ V) (lo hi : κ) : IndexedMap κ V :=
  ⟨m.raw.range (toNat lo) (toNat hi), m.wf_of_subset fun _ hn => (NatMap.mem_range.mp hn).1⟩

/-- All `(key, value)` pairs, ascending by key encoding. The decode never fails on a well-formed
map (`wf`), so the `filterMap` drops nothing. -/
def toList (m : IndexedMap κ V) : List (κ × V) :=
  m.raw.toList.filterMap fun e => (ofNat? e.1).map fun k => (k, e.2)
/-- Build a map from `(key, value)` pairs (later pairs win on duplicate keys). -/
def ofList (l : List (κ × V)) : IndexedMap κ V := l.foldl (fun m e => m.insert e.1 e.2) ∅

/-- All keys, ascending in encoding order. -/
def keys (m : IndexedMap κ V) : List κ := m.toList.map Prod.fst
/-- All values, in ascending key-encoding order. -/
def values (m : IndexedMap κ V) : List V := m.raw.values

/-- The set of keys, as an `IndexedSet` — `NatMap.domain`'s one structural pass, with `wf`
carried over (the domain holds exactly the map's keys). -/
def domain (m : IndexedMap κ V) : IndexedSet κ :=
  ⟨m.raw.domain, fun n hn => m.wf n (by
      replace hn : m.raw.domain.contains n = true := hn
      rw [NatMap.contains_domain] at hn
      exact hn)⟩

/-- `repr` renders the `ofList` of the ascending `(key, value)` list — valid Lean that rebuilds
the map. -/
instance [Repr κ] [Repr V] : Repr (IndexedMap κ V) where
  reprPrec m prec := Repr.addAppParen ("IndexedMap.ofList " ++ repr m.toList) prec

/-- `toString` displays the entries in ascending key-encoding order as `{k₁ ↦ v₁, …}`. -/
instance [ToString κ] [ToString V] : ToString (IndexedMap κ V) where
  toString m :=
    "{" ++ String.intercalate ", " (m.toList.map (fun (k, v) => s!"{k} ↦ {v}")) ++ "}"

/-- Fold `f` over `(key, value)` entries in ascending key-encoding order, starting from `init`.
Raw keys are decoded on the way out; a decode can only fail off a well-formed map (`wf`), in
which case the entry is skipped — the same benign-skip convention as `toList` and the other
walks below. -/
def fold {β : Type w} (f : β → κ → V → β) (init : β) (m : IndexedMap κ V) : β :=
  m.raw.fold (fun acc n v => match ofNat? n with | some k => f acc k v | none => acc) init

/-- Monadic fold over `(key, value)` entries in ascending key-encoding order. The monadic
companion of `fold` (recovered by instantiating `mo := Id`). -/
def foldM {β : Type w} {mo : Type w → Type w'} [Monad mo] (f : β → κ → V → mo β) (init : β)
    (m : IndexedMap κ V) : mo β :=
  m.raw.foldM (fun acc n v => match ofNat? n with | some k => f acc k v | none => pure acc) init

/-- Whether every entry satisfies `p` (a predicate on key and value), short-circuiting at the
first that fails (vacuously true on the empty map). -/
def all (p : κ → V → Bool) (m : IndexedMap κ V) : Bool :=
  m.raw.all fun n v => match ofNat? n with | some k => p k v | none => true

/-- Whether some entry satisfies `p`, short-circuiting at the first that holds (vacuously false
on the empty map). -/
def any (p : κ → V → Bool) (m : IndexedMap κ V) : Bool :=
  m.raw.any fun n v => match ofNat? n with | some k => p k v | none => false

/-- Keep only the entries `(key, value)` satisfying `p`. The result is canonical, so it equals
the map built directly from the surviving entries. -/
def filter (p : κ → V → Bool) (m : IndexedMap κ V) : IndexedMap κ V :=
  ⟨m.raw.filter (fun n v => match ofNat? n with | some k => p k v | none => false),
   m.wf_of_subset fun n hn => by
     obtain ⟨v, hv, _⟩ := NatMap.mem_filter.mp hn
     exact mem_of_get?_eq_some hv⟩

/-- Split `m` by `p`: the first component keeps the entries satisfying `p`, the second the rest.
Two structural `filter` passes, so both parts are canonical. -/
def partition (p : κ → V → Bool) (m : IndexedMap κ V) : IndexedMap κ V × IndexedMap κ V :=
  (m.filter p, m.filter fun k v => !p k v)

/-- Monadic `all` over entries, threading effects in ascending key-encoding order and
short-circuiting at the first failure. -/
def allM {mo : Type → Type w} [Monad mo] (p : κ → V → mo Bool) (m : IndexedMap κ V) : mo Bool :=
  m.raw.allM fun n v => match ofNat? n with | some k => p k v | none => pure true

/-- Monadic `any` over entries, short-circuiting at the first success. -/
def anyM {mo : Type → Type w} [Monad mo] (p : κ → V → mo Bool) (m : IndexedMap κ V) : mo Bool :=
  m.raw.anyM fun n v => match ofNat? n with | some k => p k v | none => pure false

/-- Monadic `filter`: keep the entries for which `p` returns `true`, running `p` on every entry
in ascending key-encoding order and threading its effects through `mo`. The result is rebuilt
from the survivors, so it is canonical and equals the pure `filter` when `p` is effect-free.
Restricted to `Type`-valued keys and values, as `List.filterM` is. -/
def filterM {κ : Type} [Countable κ] {V : Type} {mo : Type → Type w} [Monad mo]
    (p : κ → V → mo Bool) (m : IndexedMap κ V) : mo (IndexedMap κ V) := do
  let survivors ← m.toList.filterM fun e => p e.1 e.2
  pure (ofList survivors)

-- Membership is on keys: `k ∈ m` reduces to the `Bool` `contains`, so it stays decidable.
instance : Membership κ (IndexedMap κ V) := ⟨fun m k => m.contains k = true⟩
instance (k : κ) (m : IndexedMap κ V) : Decidable (k ∈ m) :=
  inferInstanceAs (Decidable (m.contains k = true))

end IndexedMap

/-- Map a function over every value of an `IndexedMap`, keeping keys and structure. This is the
functorial action `f <$> m` (see the `Functor`/`LawfulFunctor` instances). -/
def IndexedMap.map {κ : Type u} [Countable κ] {V W : Type v} (f : V → W) (m : IndexedMap κ V) :
    IndexedMap κ W :=
  ⟨NatMap.map f m.raw, fun n hn => m.wf n (by
      replace hn : NatCollection.contains (NatMap.map f m.raw) n = true := hn
      rw [NatCollection.contains_eq,
          show NatCollection.get? (NatMap.map f m.raw) n = (m.raw.get? n).map f
            from NatMap.get?_map f m.raw n] at hn
      show NatCollection.contains m.raw n = true
      rw [NatCollection.contains_eq]
      cases hv : NatCollection.get? m.raw n with
      | none =>
        rw [show NatMap.get? m.raw n = none from hv] at hn
        simp at hn
      | some v => rfl)⟩

instance {κ : Type u} [Countable κ] : Functor (IndexedMap κ) where
  map := IndexedMap.map

/-! ## Tests -/

section Tests

private def cm : IndexedMap Char Nat :=
  IndexedMap.empty.insert 'a' 10 |>.insert 'b' 20 |>.insert 'c' 30

-- membership / lookup / size
#guard (∅ : IndexedMap Char Nat).isEmpty
#guard (∅ : IndexedMap Char Nat).size = 0
#guard cm.size = 3
#guard 'a' ∈ cm
#guard 'z' ∉ cm
#guard cm.get? 'b' = some 20
#guard cm.get? 'z' = none
#guard cm.getD 'b' 0 = 20
#guard cm.getD 'z' 0 = 0
#guard cm.contains 'c'

-- insert overwrites; erase removes; modify/alter rewrite in place
#guard (cm.insert 'b' 99).get? 'b' = some 99
#guard (cm.insert 'b' 99).size = 3
#guard (cm.erase 'b').get? 'b' = none
#guard (cm.erase 'b').size = 2
#guard (cm.erase 'z') = cm
#guard (cm.modify 'b' (· + 1)).get? 'b' = some 21
#guard (cm.modify 'z' (· + 1)) = cm
#guard (cm.alter 'b' (fun _ => some 99)).get? 'b' = some 99
#guard (cm.alter 'b' (fun _ => none)).get? 'b' = none
#guard (cm.alter 'z' (fun _ => some 1)).get? 'z' = some 1

-- toList / ofList / keys / values: ascending by key encoding
#guard cm.toList = [('a', 10), ('b', 20), ('c', 30)]
#guard IndexedMap.ofList [('c', 30), ('a', 10), ('b', 20)] = cm
#guard IndexedMap.ofList [('a', 1), ('a', 10)] = (∅ : IndexedMap Char Nat).insert 'a' 10
#guard cm.keys = ['a', 'b', 'c']
#guard cm.values = [10, 20, 30]

-- domain: the key set as an IndexedSet
#guard cm.domain = IndexedSet.ofList ['a', 'b', 'c']
#guard cm.domain.size = cm.size

-- ordered queries speak the encoding order — for `Char`, code-point order
#guard cm.minKey? = some 'a'
#guard cm.maxKey? = some 'c'
#guard cm.minEntry? = some ('a', 10)
#guard cm.maxEntry? = some ('c', 30)
#guard (∅ : IndexedMap Char Nat).minEntry? = none
#guard cm.entryGT? 'a' = some ('b', 20)
#guard cm.entryGT? 'c' = none
#guard cm.entryLT? 'b' = some ('a', 10)
#guard cm.entryLT? 'a' = none
#guard cm.entryGE? 'b' = some ('b', 20)
#guard cm.entryGE? 'd' = none
#guard cm.entryLE? 'b' = some ('b', 20)
#guard cm.entryLE? '`' = none  -- '`' = 0x60, just below 'a'
#guard cm.popMinEntry? = some (('a', 10), IndexedMap.ofList [('b', 20), ('c', 30)])
#guard cm.popMaxEntry? = some (('c', 30), IndexedMap.ofList [('a', 10), ('b', 20)])
#guard (∅ : IndexedMap Char Nat).popMinEntry? = none

-- split / range: structural prunes at encoding-order bounds
#guard (cm.split 'b').1 = IndexedMap.ofList [('a', 10)]
#guard (cm.split 'b').2.1 = some 20
#guard (cm.split 'b').2.2 = IndexedMap.ofList [('c', 30)]
#guard cm.range 'b' 'c' = IndexedMap.ofList [('b', 20), ('c', 30)]

-- join / meet / diff / symmDiff / restricts / isDisjoint
private def cm2 : IndexedMap Char Nat := IndexedMap.ofList [('b', 200), ('d', 400)]
#guard IndexedMap.join (· + ·) cm cm2
        = IndexedMap.ofList [('a', 10), ('b', 220), ('c', 30), ('d', 400)]
#guard IndexedMap.meet (· + ·) cm cm2 = IndexedMap.ofList [('b', 220)]
#guard cm.diff cm2 = IndexedMap.ofList [('a', 10), ('c', 30)]
#guard cm.symmDiff cm2 = IndexedMap.ofList [('a', 10), ('c', 30), ('d', 400)]
#guard IndexedMap.restricts (fun _ _ => true) (IndexedMap.ofList [('b', 1)]) cm
#guard !IndexedMap.restricts (fun _ _ => true) cm (IndexedMap.ofList [('b', 1)])
#guard cm.isDisjoint (IndexedMap.ofList [('x', 1), ('y', 2)])
#guard !cm.isDisjoint cm2

-- fold / all / any / filter / partition over decoded keys
#guard cm.fold (fun acc k v => acc ++ s!"{k}{v}") "" = "a10b20c30"
#guard cm.all (fun _ v => v ≥ 10)
#guard !cm.all (fun k _ => k == 'a')
#guard cm.any (fun k _ => k == 'b')
#guard cm.filter (fun _ v => v ≥ 20) = IndexedMap.ofList [('b', 20), ('c', 30)]
#guard cm.partition (fun _ v => v ≥ 20)
        = (IndexedMap.ofList [('b', 20), ('c', 30)], IndexedMap.ofList [('a', 10)])

-- monadic walks in `Id` reproduce the pure ops
#guard Id.run (cm.allM (fun _ v => pure (v ≥ 10)))
#guard !Id.run (cm.anyM (fun _ v => pure (v > 100)))
#guard Id.run (cm.foldM (fun acc _ v => pure (acc + v)) 0) = 60
#guard Id.run (cm.filterM (fun _ v => pure (v ≥ 20))) = cm.filter (fun _ v => v ≥ 20)

-- the value functor rewrites values in place, keeping keys
#guard ((· * 2) <$> cm) = IndexedMap.ofList [('a', 20), ('b', 40), ('c', 60)]
#guard (cm.map toString).get? 'b' = some "20"
#guard (id <$> cm) = cm

-- UInt64 keys: deep / sparse encodings exercise tall tries
private def deepM : IndexedMap UInt64 String :=
  IndexedMap.ofList [(1, "one"), (5000000000, "big"), (18446744073709551615, "max")]
#guard deepM.size = 3
#guard deepM.get? 5000000000 = some "big"
#guard deepM.minEntry? = some (1, "one")
#guard deepM.maxEntry? = some (18446744073709551615, "max")
#guard (deepM.erase 5000000000).keys = [1, 18446744073709551615]

-- `IndexedMap Nat` coincides with `NatMap` (the identity encoding)
#guard (IndexedMap.ofList [(3, "c"), (1, "a")] : IndexedMap Nat String).raw
        = NatMap.ofList [(3, "c"), (1, "a")]
#guard (IndexedMap.ofList [(3, "c"), (1, "a")] : IndexedMap Nat String).keys = [1, 3]

-- lawful structural equality, decidable propositional equality, hash respecting both
example : LawfulBEq (IndexedMap Char Nat) := inferInstance
example : LawfulHashable (IndexedMap Char Nat) := inferInstance
example : DecidableEq (IndexedMap Char Nat) := inferInstance
#guard (IndexedMap.ofList [('a', 1), ('b', 2)] == IndexedMap.ofList [('b', 2), ('a', 1)]) = true
#guard hash (IndexedMap.ofList [('a', 1), ('b', 2)])
        = hash (IndexedMap.ofList [('b', 2), ('a', 1)])

-- printing
#guard toString cm = "{a ↦ 10, b ↦ 20, c ↦ 30}"
#guard toString (∅ : IndexedMap Char Nat) = "{}"
#guard reprStr (IndexedMap.ofList [('b', 2), ('a', 1)])
        = "IndexedMap.ofList [('a', 1), ('b', 2)]"

end Tests

----------------------------------------------------------------------------------------------------
-- Theorems
----------------------------------------------------------------------------------------------------

namespace IndexedMap

open Countable

variable {κ : Type u} [Countable κ] {V : Type v}

/-- The empty map is a left identity of `join`. -/
@[simp, grind =]
theorem join_empty_left (combine : V → V → V) (m : IndexedMap κ V) :
    IndexedMap.join combine empty m = m :=
  ext (NatMap.join_empty_left combine m.raw)

/-- The empty map is a right identity of `join`. -/
@[simp, grind =]
theorem join_empty_right (combine : V → V → V) (m : IndexedMap κ V) :
    IndexedMap.join combine m empty = m :=
  ext (NatMap.join_empty_right combine m.raw)

/-- `join` commutes when the combine is flipped: swapping the operands swaps the `combine`
arguments (see `join_comm_of_comm` for symmetric combines). -/
theorem join_comm (combine : V → V → V) (m₁ m₂ : IndexedMap κ V) :
    IndexedMap.join combine m₁ m₂ = IndexedMap.join (fun x y => combine y x) m₂ m₁ :=
  ext (NatMap.join_comm combine m₁.raw m₂.raw)

/-- `join` is commutative when its combine is symmetric. -/
theorem join_comm_of_comm (combine : V → V → V) (hcomm : ∀ x y, combine x y = combine y x)
    (m₁ m₂ : IndexedMap κ V) : IndexedMap.join combine m₁ m₂ = IndexedMap.join combine m₂ m₁ :=
  ext (NatMap.join_comm_of_comm combine hcomm m₁.raw m₂.raw)

/-- `join` is associative when its combine is associative. -/
theorem join_assoc (combine : V → V → V)
    (hassoc : ∀ x y z, combine (combine x y) z = combine x (combine y z))
    (m₁ m₂ m₃ : IndexedMap κ V) :
    IndexedMap.join combine (IndexedMap.join combine m₁ m₂) m₃
      = IndexedMap.join combine m₁ (IndexedMap.join combine m₂ m₃) :=
  ext (NatMap.join_assoc combine hassoc m₁.raw m₂.raw m₃.raw)

/-- The empty map is a left annihilator of `meet`. -/
@[simp, grind =]
theorem meet_empty_left (combine : V → V → V) (m : IndexedMap κ V) :
    IndexedMap.meet combine empty m = empty :=
  ext (NatMap.meet_empty_left combine m.raw)

/-- The empty map is a right annihilator of `meet`. -/
@[simp, grind =]
theorem meet_empty_right (combine : V → V → V) (m : IndexedMap κ V) :
    IndexedMap.meet combine m empty = empty :=
  ext (NatMap.meet_empty_right combine m.raw)

/-- `meet` commutes when the combine is flipped (see `meet_comm_of_comm` for symmetric
combines). -/
theorem meet_comm (combine : V → V → V) (m₁ m₂ : IndexedMap κ V) :
    IndexedMap.meet combine m₁ m₂ = IndexedMap.meet (fun x y => combine y x) m₂ m₁ :=
  ext (NatMap.meet_comm combine m₁.raw m₂.raw)

/-- `meet` is commutative when its combine is symmetric. -/
theorem meet_comm_of_comm (combine : V → V → V) (hcomm : ∀ x y, combine x y = combine y x)
    (m₁ m₂ : IndexedMap κ V) : IndexedMap.meet combine m₁ m₂ = IndexedMap.meet combine m₂ m₁ :=
  ext (NatMap.meet_comm_of_comm combine hcomm m₁.raw m₂.raw)

/-- `meet` is associative when its combine is associative. -/
theorem meet_assoc (combine : V → V → V)
    (hassoc : ∀ x y z, combine (combine x y) z = combine x (combine y z))
    (m₁ m₂ m₃ : IndexedMap κ V) :
    IndexedMap.meet combine (IndexedMap.meet combine m₁ m₂) m₃
      = IndexedMap.meet combine m₁ (IndexedMap.meet combine m₂ m₃) :=
  ext (NatMap.meet_assoc combine hassoc m₁.raw m₂.raw m₃.raw)

/-- The empty map restricts every map (its domain is vacuously a subset). -/
@[simp, grind =]
theorem restricts_empty_left (rel : V → V → Bool) (m : IndexedMap κ V) :
    IndexedMap.restricts rel empty m = true :=
  NatMap.restricts_empty_left rel m.raw

/-- `restricts` is reflexive: a map restricts itself whenever `rel` holds on equal values. -/
theorem restricts_refl (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (m : IndexedMap κ V) : IndexedMap.restricts rel m m = true :=
  NatMap.restricts_refl rel hrefl m.raw

/-- `restricts` is transitive when `rel` is a preorder (reflexive and transitive). -/
theorem restricts_trans (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (htrans : ∀ x y z, rel x y = true → rel y z = true → rel x z = true)
    (m₁ m₂ m₃ : IndexedMap κ V) :
    IndexedMap.restricts rel m₁ m₂ = true → IndexedMap.restricts rel m₂ m₃ = true →
    IndexedMap.restricts rel m₁ m₃ = true :=
  NatMap.restricts_trans rel hrefl htrans m₁.raw m₂.raw m₃.raw

/-- `restricts` is anti-symmetric when `rel` is reflexive and anti-symmetric. -/
theorem restricts_antisymm (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (hantisymm : ∀ x y, rel x y = true → rel y x = true → x = y)
    (m₁ m₂ : IndexedMap κ V) :
    IndexedMap.restricts rel m₁ m₂ = true → IndexedMap.restricts rel m₂ m₁ = true → m₁ = m₂ :=
  fun h₁ h₂ => ext (NatMap.restricts_antisymm rel hrefl hantisymm m₁.raw m₂.raw h₁ h₂)

/-- `meet` is a lower bound on the left, provided the combine yields a `rel`-smaller value than
its left argument. -/
theorem meet_restricts_left (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (combine : V → V → V) (hle : ∀ x y, rel (combine x y) x = true) (m n : IndexedMap κ V) :
    IndexedMap.restricts rel (IndexedMap.meet combine m n) m = true :=
  NatMap.meet_restricts_left rel hrefl combine hle m.raw n.raw

/-- `meet` is a lower bound on the right, provided the combine yields a `rel`-smaller value than
its right argument. -/
theorem meet_restricts_right (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (combine : V → V → V) (hle : ∀ x y, rel (combine x y) y = true) (m n : IndexedMap κ V) :
    IndexedMap.restricts rel (IndexedMap.meet combine m n) n = true :=
  NatMap.meet_restricts_right rel hrefl combine hle m.raw n.raw

/-- `meet` is the greatest lower bound, provided the combine is a greatest lower bound for
`rel`. -/
theorem restricts_meet (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (combine : V → V → V)
    (hglb : ∀ w x y, rel w x = true → rel w y = true → rel w (combine x y) = true)
    (m a b : IndexedMap κ V)
    (hma : IndexedMap.restricts rel m a = true) (hmb : IndexedMap.restricts rel m b = true) :
    IndexedMap.restricts rel m (IndexedMap.meet combine a b) = true :=
  NatMap.restricts_meet rel hrefl combine hglb m.raw a.raw b.raw hma hmb

/-- `join` is an upper bound on the left, provided the combine yields a `rel`-greater value than
its left argument. -/
theorem restricts_join_left (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (combine : V → V → V) (hle : ∀ x y, rel x (combine x y) = true) (m n : IndexedMap κ V) :
    IndexedMap.restricts rel m (IndexedMap.join combine m n) = true :=
  NatMap.restricts_join_left rel hrefl combine hle m.raw n.raw

/-- `join` is an upper bound on the right, provided the combine yields a `rel`-greater value
than its right argument. -/
theorem restricts_join_right (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (combine : V → V → V) (hre : ∀ x y, rel y (combine x y) = true) (m n : IndexedMap κ V) :
    IndexedMap.restricts rel n (IndexedMap.join combine m n) = true :=
  NatMap.restricts_join_right rel hrefl combine hre m.raw n.raw

/-- `join` is the least upper bound, provided the combine is a least upper bound for `rel`. -/
theorem join_restricts (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (combine : V → V → V)
    (hlub : ∀ x y w, rel x w = true → rel y w = true → rel (combine x y) w = true)
    (a b m : IndexedMap κ V)
    (ham : IndexedMap.restricts rel a m = true) (hbm : IndexedMap.restricts rel b m = true) :
    IndexedMap.restricts rel (IndexedMap.join combine a b) m = true :=
  NatMap.join_restricts rel hrefl combine hlub a.raw b.raw m.raw ham hbm

/-- Looking up a freshly-inserted entry returns the inserted value. -/
@[simp]
theorem get?_insert_self (m : IndexedMap κ V) (k : κ) (v : V) :
    (m.insert k v).get? k = some v :=
  NatMap.get?_insert_self m.raw (toNat k) v

/-- Looking up any other key after an insert reads through unchanged (the `_ne` companion of
`get?_insert_self`; together they pin `insert`'s lookups without needing `DecidableEq κ`). -/
theorem get?_insert_ne {m : IndexedMap κ V} {b : κ} {v : V} {a : κ} (h : a ≠ b) :
    (m.insert b v).get? a = m.get? a := by
  show (m.raw.insert (toNat b) v).get? (toNat a) = m.raw.get? (toNat a)
  rw [NatMap.get?_insert, if_neg (fun hn => h (toNat_inj hn))]

/-- Inserting an entry already present (key `k` already mapped to `v`) returns the same map. -/
theorem insert_of_get? {m : IndexedMap κ V} {k : κ} {v : V} (h : m.get? k = some v) :
    m.insert k v = m :=
  ext (NatMap.insert_of_get? h)

/-- Membership after `insert`: `a` is present exactly when it was already present or is the
inserted key. -/
theorem mem_insert {m : IndexedMap κ V} {b a : κ} {v : V} :
    a ∈ m.insert b v ↔ a ∈ m ∨ a = b := by
  show toNat a ∈ m.raw.insert (toNat b) v ↔ toNat a ∈ m.raw ∨ a = b
  rw [NatMap.mem_insert]
  constructor
  · intro h
    exact h.imp id fun hn => toNat_inj hn
  · intro h
    exact h.imp id fun hn => by rw [hn]

/-- `modify` never changes the key set. -/
theorem mem_modify {m : IndexedMap κ V} {b a : κ} {f : V → V} :
    a ∈ m.modify b f ↔ a ∈ m := by
  show toNat a ∈ m.raw.modify (toNat b) f ↔ toNat a ∈ m.raw
  exact NatMap.mem_modify

/-- `alter` adds no key other than the altered one. -/
theorem mem_of_mem_alter {m : IndexedMap κ V} {b a : κ} {f : Option V → Option V}
    (h : a ∈ m.alter b f) : a ∈ m ∨ a = b := by
  replace h : toNat a ∈ m.raw.alter (toNat b) f := h
  exact (NatMap.mem_of_mem_alter h).imp id fun hn => toNat_inj hn

/-- Membership in a `join`: a key is present exactly when present in either operand (`combine`
only affects values). -/
theorem mem_join (combine : V → V → V) (m₁ m₂ : IndexedMap κ V) (a : κ) :
    a ∈ IndexedMap.join combine m₁ m₂ ↔ a ∈ m₁ ∨ a ∈ m₂ := by
  show toNat a ∈ NatMap.join combine m₁.raw m₂.raw ↔ toNat a ∈ m₁.raw ∨ toNat a ∈ m₂.raw
  exact NatMap.mem_join combine m₁.raw m₂.raw (toNat a)

/-- Membership in a `meet`: a key is present exactly when present in both operands. -/
theorem mem_meet (combine : V → V → V) (m₁ m₂ : IndexedMap κ V) (a : κ) :
    a ∈ IndexedMap.meet combine m₁ m₂ ↔ a ∈ m₁ ∧ a ∈ m₂ := by
  show toNat a ∈ NatMap.meet combine m₁.raw m₂.raw ↔ toNat a ∈ m₁.raw ∧ toNat a ∈ m₂.raw
  exact NatMap.mem_meet combine m₁.raw m₂.raw (toNat a)

/-- Joining a map with itself preserves its keys — regardless of the value-combining function. -/
@[simp]
theorem mem_join_self (combine : V → V → V) (m : IndexedMap κ V) (k : κ) :
    k ∈ IndexedMap.join combine m m ↔ k ∈ m := by
  show toNat k ∈ NatMap.join combine m.raw m.raw ↔ toNat k ∈ m.raw
  exact NatMap.mem_join_self combine m.raw (toNat k)

/-- Looking up a key after joining a map with itself: present keys read `combine v v`. -/
theorem get?_join_self (combine : V → V → V) (m : IndexedMap κ V) (k : κ) :
    (IndexedMap.join combine m m).get? k = (m.get? k).map (fun v => combine v v) :=
  NatMap.get?_join_self combine m.raw (toNat k)

/-- When the value-combining function is idempotent, joining a map with itself returns the
map. -/
theorem join_self_of_idem (combine : V → V → V) (hidem : ∀ v, combine v v = v)
    (m : IndexedMap κ V) : IndexedMap.join combine m m = m :=
  ext (NatMap.join_self_of_idem combine hidem m.raw)

/-- Meeting a map with itself preserves its keys — regardless of the value-combining function. -/
@[simp]
theorem mem_meet_self (combine : V → V → V) (m : IndexedMap κ V) (k : κ) :
    k ∈ IndexedMap.meet combine m m ↔ k ∈ m := by
  show toNat k ∈ NatMap.meet combine m.raw m.raw ↔ toNat k ∈ m.raw
  exact NatMap.mem_meet_self combine m.raw (toNat k)

/-- Looking up a key after meeting a map with itself: present keys read `combine v v`. -/
theorem get?_meet_self (combine : V → V → V) (m : IndexedMap κ V) (k : κ) :
    (IndexedMap.meet combine m m).get? k = (m.get? k).map (fun v => combine v v) :=
  NatMap.get?_meet_self combine m.raw (toNat k)

/-- When the value-combining function is idempotent, meeting a map with itself returns the
map. -/
theorem meet_self_of_idem (combine : V → V → V) (hidem : ∀ v, combine v v = v)
    (m : IndexedMap κ V) : IndexedMap.meet combine m m = m :=
  ext (NatMap.meet_self_of_idem combine hidem m.raw)

/-- `meet` distributes over `join`, provided the meet combine distributes over the join combine
pointwise. -/
theorem meet_join_distrib (combineMeet combineJoin : V → V → V)
    (hdist : ∀ x y z,
      combineMeet x (combineJoin y z) = combineJoin (combineMeet x y) (combineMeet x z))
    (a b e : IndexedMap κ V) :
    IndexedMap.meet combineMeet a (IndexedMap.join combineJoin b e)
      = IndexedMap.join combineJoin (IndexedMap.meet combineMeet a b)
          (IndexedMap.meet combineMeet a e) :=
  ext (NatMap.meet_join_distrib combineMeet combineJoin hdist a.raw b.raw e.raw)

/-- `join` distributes over `meet`, provided the combines form a distributive lattice on
values. -/
theorem join_meet_distrib (combineJoin combineMeet : V → V → V)
    (hidem : ∀ x, combineMeet x x = x)
    (habs1 : ∀ x y, combineMeet (combineJoin x y) x = x)
    (habs2 : ∀ x y, combineMeet x (combineJoin x y) = x)
    (hdist : ∀ x y z,
      combineJoin x (combineMeet y z) = combineMeet (combineJoin x y) (combineJoin x z))
    (a b e : IndexedMap κ V) :
    IndexedMap.join combineJoin a (IndexedMap.meet combineMeet b e)
      = IndexedMap.meet combineMeet (IndexedMap.join combineJoin a b)
          (IndexedMap.join combineJoin a e) :=
  ext (NatMap.join_meet_distrib combineJoin combineMeet hidem habs1 habs2 hdist a.raw b.raw e.raw)

/-- **Functor identity law**: mapping `id` returns the map unchanged. -/
@[simp, grind =]
theorem map_id (m : IndexedMap κ V) : IndexedMap.map id m = m :=
  ext (NatMap.map_id m.raw)

/-- **Functor composition law**: mapping a composition is the composition of maps. -/
theorem map_comp {V W X : Type v} (f : V → W) (g : W → X) (m : IndexedMap κ V) :
    IndexedMap.map (g ∘ f) m = IndexedMap.map g (IndexedMap.map f m) :=
  ext (NatMap.map_comp f g m.raw)

/-- Looking up a key in a mapped map applies `f` to the value (the `get?` spec of `map`). -/
theorem get?_map {V W : Type v} (f : V → W) (m : IndexedMap κ V) (k : κ) :
    (m.map f).get? k = (m.get? k).map f :=
  NatMap.get?_map f m.raw (toNat k)

/-- `domain` preserves the size: the key set has exactly as many elements as the map has
entries. -/
@[simp]
theorem size_domain (m : IndexedMap κ V) : m.domain.size = m.size :=
  NatMap.size_domain m.raw

/-- A key is in the domain exactly when it is in the map (`Bool` form). -/
theorem contains_domain (m : IndexedMap κ V) (k : κ) : m.domain.contains k = m.contains k :=
  NatMap.contains_domain m.raw (toNat k)

/-- A key is in the domain exactly when it is in the map. -/
@[simp]
theorem mem_domain (m : IndexedMap κ V) (k : κ) : k ∈ m.domain ↔ k ∈ m := by
  show m.domain.contains k = true ↔ m.contains k = true
  rw [contains_domain]

/-- The entry `minEntry?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_minEntry? {m : IndexedMap κ V} {k : κ} {v : V}
    (h : m.minEntry? = some (k, v)) : m.get? k = some v := by
  replace h : m.raw.minEntry?.bind (fun e => (ofNat? e.1).map fun k => (k, e.2)) = some (k, v) := h
  cases hm : m.raw.minEntry? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = some (k, v) := h
    obtain ⟨k', hd, hpair⟩ := Option.map_eq_some_iff.mp h
    replace hpair : (k', e.2) = (k, v) := hpair
    injection hpair with h1 h2
    subst h1
    subst h2
    show m.raw.get? (toNat k') = some e.2
    rw [toNat_ofNat? hd]
    exact NatMap.get?_of_minEntry? hm

/-- The entry `maxEntry?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_maxEntry? {m : IndexedMap κ V} {k : κ} {v : V}
    (h : m.maxEntry? = some (k, v)) : m.get? k = some v := by
  replace h : m.raw.maxEntry?.bind (fun e => (ofNat? e.1).map fun k => (k, e.2)) = some (k, v) := h
  cases hm : m.raw.maxEntry? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = some (k, v) := h
    obtain ⟨k', hd, hpair⟩ := Option.map_eq_some_iff.mp h
    replace hpair : (k', e.2) = (k, v) := hpair
    injection hpair with h1 h2
    subst h1
    subst h2
    show m.raw.get? (toNat k') = some e.2
    rw [toNat_ofNat? hd]
    exact NatMap.get?_of_maxEntry? hm

/-- The least key (in encoding order) is present. -/
theorem minKey?_mem {m : IndexedMap κ V} {k : κ} (h : m.minKey? = some k) : k ∈ m := by
  replace h : m.raw.minKey?.bind ofNat? = some k := h
  cases hm : m.raw.minKey? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some n =>
    rw [hm] at h
    replace h : ofNat? n = some k := h
    show toNat k ∈ m.raw
    rw [toNat_ofNat? h]
    exact NatMap.minKey?_mem hm

/-- The least key is a lower bound in encoding order. -/
theorem minKey?_le {m : IndexedMap κ V} {k j : κ} (h : m.minKey? = some k) (hj : j ∈ m) :
    toNat k ≤ toNat j := by
  replace h : m.raw.minKey?.bind ofNat? = some k := h
  cases hm : m.raw.minKey? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some n =>
    rw [hm] at h
    replace h : ofNat? n = some k := h
    rw [toNat_ofNat? h]
    exact NatMap.minKey?_le hm hj

/-- The greatest key (in encoding order) is present. -/
theorem maxKey?_mem {m : IndexedMap κ V} {k : κ} (h : m.maxKey? = some k) : k ∈ m := by
  replace h : m.raw.maxKey?.bind ofNat? = some k := h
  cases hm : m.raw.maxKey? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some n =>
    rw [hm] at h
    replace h : ofNat? n = some k := h
    show toNat k ∈ m.raw
    rw [toNat_ofNat? h]
    exact NatMap.maxKey?_mem hm

/-- The greatest key is an upper bound in encoding order. -/
theorem le_maxKey? {m : IndexedMap κ V} {k j : κ} (h : m.maxKey? = some k) (hj : j ∈ m) :
    toNat j ≤ toNat k := by
  replace h : m.raw.maxKey?.bind ofNat? = some k := h
  cases hm : m.raw.maxKey? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some n =>
    rw [hm] at h
    replace h : ofNat? n = some k := h
    rw [toNat_ofNat? h]
    exact NatMap.le_maxKey? hm hj

/-- `minKey?` answers `none` exactly on the empty map (totality: decoding the least key of a
well-formed map never fails). -/
theorem minKey?_eq_none {m : IndexedMap κ V} : m.minKey? = none ↔ m = empty := by
  constructor
  · intro h
    replace h : m.raw.minKey?.bind ofNat? = none := h
    cases hm : m.raw.minKey? with
    | none => exact ext (NatMap.minKey?_eq_none.mp hm)
    | some n =>
      rw [hm] at h
      replace h : ofNat? n = none := h
      obtain ⟨k, hk, _⟩ := ofNat?_of_mem_raw (NatMap.minKey?_mem hm)
      rw [hk] at h
      exact absurd h (by simp)
  · intro h
    subst h
    show ((empty : IndexedMap κ V).raw.minKey?).bind ofNat? = none
    rw [show (empty : IndexedMap κ V).raw.minKey? = none from NatMap.minKey?_eq_none.mpr rfl]
    rfl

/-- `maxKey?` answers `none` exactly on the empty map. -/
theorem maxKey?_eq_none {m : IndexedMap κ V} : m.maxKey? = none ↔ m = empty := by
  constructor
  · intro h
    replace h : m.raw.maxKey?.bind ofNat? = none := h
    cases hm : m.raw.maxKey? with
    | none => exact ext (NatMap.maxKey?_eq_none.mp hm)
    | some n =>
      rw [hm] at h
      replace h : ofNat? n = none := h
      obtain ⟨k, hk, _⟩ := ofNat?_of_mem_raw (NatMap.maxKey?_mem hm)
      rw [hk] at h
      exact absurd h (by simp)
  · intro h
    subst h
    show ((empty : IndexedMap κ V).raw.maxKey?).bind ofNat? = none
    rw [show (empty : IndexedMap κ V).raw.maxKey? = none from NatMap.maxKey?_eq_none.mpr rfl]
    rfl

/-- `minEntry?` answers `none` exactly on the empty map. -/
theorem minEntry?_eq_none {m : IndexedMap κ V} : m.minEntry? = none ↔ m = empty := by
  constructor
  · intro h
    replace h : m.raw.minEntry?.bind (fun e => (ofNat? e.1).map fun k => (k, e.2)) = none := h
    cases hm : m.raw.minEntry? with
    | none =>
      refine ext (NatMap.minKey?_eq_none.mp ?_)
      show (NatCollection.minEntry? m.raw).map Prod.fst = none
      rw [show NatCollection.minEntry? m.raw = none from hm]
      rfl
    | some e =>
      rw [hm] at h
      replace h : (ofNat? e.1).map (fun k => (k, e.2)) = none := h
      obtain ⟨k, hk, _⟩ :=
        ofNat?_of_mem_raw (mem_of_get?_eq_some (NatMap.get?_of_minEntry? hm))
      rw [hk] at h
      exact absurd h (by simp)
  · intro h
    subst h
    show (NatCollection.minEntry? (empty : IndexedMap κ V).raw).bind
        (fun e => (ofNat? e.1).map fun k => (k, e.2)) = none
    have hk : (NatCollection.minEntry? (empty : IndexedMap κ V).raw).map Prod.fst = none :=
      NatMap.minKey?_eq_none.mpr rfl
    cases hm : NatCollection.minEntry? (empty : IndexedMap κ V).raw with
    | none => rfl
    | some e => rw [hm] at hk; exact absurd hk (by simp)

/-- `maxEntry?` answers `none` exactly on the empty map. -/
theorem maxEntry?_eq_none {m : IndexedMap κ V} : m.maxEntry? = none ↔ m = empty := by
  constructor
  · intro h
    replace h : m.raw.maxEntry?.bind (fun e => (ofNat? e.1).map fun k => (k, e.2)) = none := h
    cases hm : m.raw.maxEntry? with
    | none =>
      refine ext (NatMap.maxKey?_eq_none.mp ?_)
      show (NatCollection.maxEntry? m.raw).map Prod.fst = none
      rw [show NatCollection.maxEntry? m.raw = none from hm]
      rfl
    | some e =>
      rw [hm] at h
      replace h : (ofNat? e.1).map (fun k => (k, e.2)) = none := h
      obtain ⟨k, hk, _⟩ :=
        ofNat?_of_mem_raw (mem_of_get?_eq_some (NatMap.get?_of_maxEntry? hm))
      rw [hk] at h
      exact absurd h (by simp)
  · intro h
    subst h
    show (NatCollection.maxEntry? (empty : IndexedMap κ V).raw).bind
        (fun e => (ofNat? e.1).map fun k => (k, e.2)) = none
    have hk : (NatCollection.maxEntry? (empty : IndexedMap κ V).raw).map Prod.fst = none :=
      NatMap.maxKey?_eq_none.mpr rfl
    cases hm : NatCollection.maxEntry? (empty : IndexedMap κ V).raw with
    | none => rfl
    | some e => rw [hm] at hk; exact absurd hk (by simp)

/-- The entry `entryGT?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_entryGT? {m : IndexedMap κ V} {k j : κ} {v : V}
    (h : m.entryGT? k = some (j, v)) : m.get? j = some v := by
  replace h : (m.raw.entryGT? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = some (j, v) := h
  cases hm : m.raw.entryGT? (toNat k) with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = some (j, v) := h
    obtain ⟨j', hd, hpair⟩ := Option.map_eq_some_iff.mp h
    replace hpair : (j', e.2) = (j, v) := hpair
    injection hpair with h1 h2
    subst h1
    subst h2
    show m.raw.get? (toNat j') = some e.2
    rw [toNat_ofNat? hd]
    exact NatMap.get?_of_entryGT? hm

/-- `entryGT?`'s key is strictly greater (in encoding order) than the query key. -/
theorem entryGT?_gt {m : IndexedMap κ V} {k j : κ} {v : V} (h : m.entryGT? k = some (j, v)) :
    toNat k < toNat j := by
  replace h : (m.raw.entryGT? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = some (j, v) := h
  cases hm : m.raw.entryGT? (toNat k) with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = some (j, v) := h
    obtain ⟨j', hd, hpair⟩ := Option.map_eq_some_iff.mp h
    replace hpair : (j', e.2) = (j, v) := hpair
    injection hpair with h1 h2
    subst h1
    rw [toNat_ofNat? hd]
    exact NatMap.entryGT?_gt hm

/-- `entryGT?` returns the *least* key beyond the query key (in encoding order). -/
theorem entryGT?_le {m : IndexedMap κ V} {k j' j : κ} {v : V}
    (h : m.entryGT? k = some (j', v)) (hj : j ∈ m) (hk : toNat k < toNat j) :
    toNat j' ≤ toNat j := by
  replace h : (m.raw.entryGT? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = some (j', v) := h
  cases hm : m.raw.entryGT? (toNat k) with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = some (j', v) := h
    obtain ⟨j'', hd, hpair⟩ := Option.map_eq_some_iff.mp h
    replace hpair : (j'', e.2) = (j', v) := hpair
    injection hpair with h1 h2
    subst h1
    rw [toNat_ofNat? hd]
    exact NatMap.entryGT?_le hm hj hk

/-- A `none` from `entryGT?` is complete: no key of the map lies strictly above the query key
(in encoding order). -/
theorem le_of_entryGT?_eq_none {m : IndexedMap κ V} {k j : κ} (h : m.entryGT? k = none)
    (hj : j ∈ m) : toNat j ≤ toNat k := by
  replace h : (m.raw.entryGT? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = none := h
  cases hm : m.raw.entryGT? (toNat k) with
  | none => exact NatMap.le_of_entryGT?_eq_none hm hj
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = none := h
    obtain ⟨k', hk', _⟩ :=
      ofNat?_of_mem_raw (mem_of_get?_eq_some (NatMap.get?_of_entryGT? hm))
    rw [hk'] at h
    exact absurd h (by simp)

/-- The entry `entryLT?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_entryLT? {m : IndexedMap κ V} {k j : κ} {v : V}
    (h : m.entryLT? k = some (j, v)) : m.get? j = some v := by
  replace h : (m.raw.entryLT? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = some (j, v) := h
  cases hm : m.raw.entryLT? (toNat k) with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = some (j, v) := h
    obtain ⟨j', hd, hpair⟩ := Option.map_eq_some_iff.mp h
    replace hpair : (j', e.2) = (j, v) := hpair
    injection hpair with h1 h2
    subst h1
    subst h2
    show m.raw.get? (toNat j') = some e.2
    rw [toNat_ofNat? hd]
    exact NatMap.get?_of_entryLT? hm

/-- `entryLT?`'s key is strictly less (in encoding order) than the query key. -/
theorem entryLT?_lt {m : IndexedMap κ V} {k j : κ} {v : V} (h : m.entryLT? k = some (j, v)) :
    toNat j < toNat k := by
  replace h : (m.raw.entryLT? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = some (j, v) := h
  cases hm : m.raw.entryLT? (toNat k) with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = some (j, v) := h
    obtain ⟨j', hd, hpair⟩ := Option.map_eq_some_iff.mp h
    replace hpair : (j', e.2) = (j, v) := hpair
    injection hpair with h1 h2
    subst h1
    rw [toNat_ofNat? hd]
    exact NatMap.entryLT?_lt hm

/-- `entryLT?` returns the *greatest* key below the query key (in encoding order). -/
theorem le_entryLT? {m : IndexedMap κ V} {k j' j : κ} {v : V}
    (h : m.entryLT? k = some (j', v)) (hj : j ∈ m) (hk : toNat j < toNat k) :
    toNat j ≤ toNat j' := by
  replace h : (m.raw.entryLT? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = some (j', v) := h
  cases hm : m.raw.entryLT? (toNat k) with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = some (j', v) := h
    obtain ⟨j'', hd, hpair⟩ := Option.map_eq_some_iff.mp h
    replace hpair : (j'', e.2) = (j', v) := hpair
    injection hpair with h1 h2
    subst h1
    rw [toNat_ofNat? hd]
    exact NatMap.le_entryLT? hm hj hk

/-- A `none` from `entryLT?` is complete: no key of the map lies strictly below the query key
(in encoding order). -/
theorem ge_of_entryLT?_eq_none {m : IndexedMap κ V} {k j : κ} (h : m.entryLT? k = none)
    (hj : j ∈ m) : toNat k ≤ toNat j := by
  replace h : (m.raw.entryLT? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = none := h
  cases hm : m.raw.entryLT? (toNat k) with
  | none => exact NatMap.ge_of_entryLT?_eq_none hm hj
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = none := h
    obtain ⟨k', hk', _⟩ :=
      ofNat?_of_mem_raw (mem_of_get?_eq_some (NatMap.get?_of_entryLT? hm))
    rw [hk'] at h
    exact absurd h (by simp)

/-- The entry `entryGE?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_entryGE? {m : IndexedMap κ V} {k j : κ} {v : V}
    (h : m.entryGE? k = some (j, v)) : m.get? j = some v := by
  replace h : (m.raw.entryGE? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = some (j, v) := h
  cases hm : m.raw.entryGE? (toNat k) with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = some (j, v) := h
    obtain ⟨j', hd, hpair⟩ := Option.map_eq_some_iff.mp h
    replace hpair : (j', e.2) = (j, v) := hpair
    injection hpair with h1 h2
    subst h1
    subst h2
    show m.raw.get? (toNat j') = some e.2
    rw [toNat_ofNat? hd]
    exact NatMap.get?_of_entryGE? hm

/-- `entryGE?`'s key is at or above the query key (in encoding order). -/
theorem entryGE?_ge {m : IndexedMap κ V} {k j : κ} {v : V} (h : m.entryGE? k = some (j, v)) :
    toNat k ≤ toNat j := by
  replace h : (m.raw.entryGE? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = some (j, v) := h
  cases hm : m.raw.entryGE? (toNat k) with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = some (j, v) := h
    obtain ⟨j', hd, hpair⟩ := Option.map_eq_some_iff.mp h
    replace hpair : (j', e.2) = (j, v) := hpair
    injection hpair with h1 h2
    subst h1
    rw [toNat_ofNat? hd]
    exact NatMap.entryGE?_ge hm

/-- `entryGE?` returns the *least* key at or beyond the query key (in encoding order). -/
theorem entryGE?_le {m : IndexedMap κ V} {k j' j : κ} {v : V}
    (h : m.entryGE? k = some (j', v)) (hj : j ∈ m) (hk : toNat k ≤ toNat j) :
    toNat j' ≤ toNat j := by
  replace h : (m.raw.entryGE? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = some (j', v) := h
  cases hm : m.raw.entryGE? (toNat k) with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = some (j', v) := h
    obtain ⟨j'', hd, hpair⟩ := Option.map_eq_some_iff.mp h
    replace hpair : (j'', e.2) = (j', v) := hpair
    injection hpair with h1 h2
    subst h1
    rw [toNat_ofNat? hd]
    exact NatMap.entryGE?_le hm hj hk

/-- A `none` from `entryGE?` is complete: every key of the map lies strictly below the query key
(in encoding order). -/
theorem lt_of_entryGE?_eq_none {m : IndexedMap κ V} {k j : κ} (h : m.entryGE? k = none)
    (hj : j ∈ m) : toNat j < toNat k := by
  replace h : (m.raw.entryGE? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = none := h
  cases hm : m.raw.entryGE? (toNat k) with
  | none => exact NatMap.lt_of_entryGE?_eq_none hm hj
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = none := h
    obtain ⟨k', hk', _⟩ :=
      ofNat?_of_mem_raw (mem_of_get?_eq_some (NatMap.get?_of_entryGE? hm))
    rw [hk'] at h
    exact absurd h (by simp)

/-- The entry `entryLE?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_entryLE? {m : IndexedMap κ V} {k j : κ} {v : V}
    (h : m.entryLE? k = some (j, v)) : m.get? j = some v := by
  replace h : (m.raw.entryLE? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = some (j, v) := h
  cases hm : m.raw.entryLE? (toNat k) with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = some (j, v) := h
    obtain ⟨j', hd, hpair⟩ := Option.map_eq_some_iff.mp h
    replace hpair : (j', e.2) = (j, v) := hpair
    injection hpair with h1 h2
    subst h1
    subst h2
    show m.raw.get? (toNat j') = some e.2
    rw [toNat_ofNat? hd]
    exact NatMap.get?_of_entryLE? hm

/-- `entryLE?`'s key is at or below the query key (in encoding order). -/
theorem entryLE?_le {m : IndexedMap κ V} {k j : κ} {v : V} (h : m.entryLE? k = some (j, v)) :
    toNat j ≤ toNat k := by
  replace h : (m.raw.entryLE? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = some (j, v) := h
  cases hm : m.raw.entryLE? (toNat k) with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = some (j, v) := h
    obtain ⟨j', hd, hpair⟩ := Option.map_eq_some_iff.mp h
    replace hpair : (j', e.2) = (j, v) := hpair
    injection hpair with h1 h2
    subst h1
    rw [toNat_ofNat? hd]
    exact NatMap.entryLE?_le hm

/-- `entryLE?` returns the *greatest* key at or below the query key (in encoding order). -/
theorem le_entryLE? {m : IndexedMap κ V} {k j' j : κ} {v : V}
    (h : m.entryLE? k = some (j', v)) (hj : j ∈ m) (hk : toNat j ≤ toNat k) :
    toNat j ≤ toNat j' := by
  replace h : (m.raw.entryLE? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = some (j', v) := h
  cases hm : m.raw.entryLE? (toNat k) with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = some (j', v) := h
    obtain ⟨j'', hd, hpair⟩ := Option.map_eq_some_iff.mp h
    replace hpair : (j'', e.2) = (j', v) := hpair
    injection hpair with h1 h2
    subst h1
    rw [toNat_ofNat? hd]
    exact NatMap.le_entryLE? hm hj hk

/-- A `none` from `entryLE?` is complete: every key of the map lies strictly above the query key
(in encoding order). -/
theorem gt_of_entryLE?_eq_none {m : IndexedMap κ V} {k j : κ} (h : m.entryLE? k = none)
    (hj : j ∈ m) : toNat k < toNat j := by
  replace h : (m.raw.entryLE? (toNat k)).bind
      (fun e => (ofNat? e.1).map fun k' => (k', e.2)) = none := h
  cases hm : m.raw.entryLE? (toNat k) with
  | none => exact NatMap.gt_of_entryLE?_eq_none hm hj
  | some e =>
    rw [hm] at h
    replace h : (ofNat? e.1).map (fun k' => (k', e.2)) = none := h
    obtain ⟨k', hk', _⟩ :=
      ofNat?_of_mem_raw (mem_of_get?_eq_some (NatMap.get?_of_entryLE? hm))
    rw [hk'] at h
    exact absurd h (by simp)

/-- `popMinEntry?` pops the least entry: its entry is `minEntry?`'s answer. -/
theorem minEntry?_of_popMinEntry? {m : IndexedMap κ V} {e : κ × V} {m' : IndexedMap κ V}
    (h : m.popMinEntry? = some (e, m')) : m.minEntry? = some e := by
  unfold popMinEntry? at h
  cases hm : m.minEntry? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e' =>
    rw [hm] at h
    replace h : some (e', m.erase e'.1) = some (e, m') := h
    injection h with h
    injection h with h1 h2
    rw [h1]

/-- `popMinEntry?`'s rest is the map with the popped key erased. -/
theorem popMinEntry?_erase {m : IndexedMap κ V} {e : κ × V} {m' : IndexedMap κ V}
    (h : m.popMinEntry? = some (e, m')) : m' = m.erase e.1 := by
  unfold popMinEntry? at h
  cases hm : m.minEntry? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e' =>
    rw [hm] at h
    replace h : some (e', m.erase e'.1) = some (e, m') := h
    injection h with h
    injection h with h1 h2
    rw [← h2, h1]

/-- `popMinEntry?` answers `none` exactly on the empty map (totality: a non-empty map always
pops). -/
theorem popMinEntry?_eq_none {m : IndexedMap κ V} : m.popMinEntry? = none ↔ m = empty := by
  constructor
  · intro h
    unfold popMinEntry? at h
    cases hm : m.minEntry? with
    | none => exact minEntry?_eq_none.mp hm
    | some e => rw [hm] at h; exact absurd h (by simp)
  · intro h
    unfold popMinEntry?
    rw [minEntry?_eq_none.mpr h]

/-- `popMaxEntry?` pops the greatest entry: its entry is `maxEntry?`'s answer. -/
theorem maxEntry?_of_popMaxEntry? {m : IndexedMap κ V} {e : κ × V} {m' : IndexedMap κ V}
    (h : m.popMaxEntry? = some (e, m')) : m.maxEntry? = some e := by
  unfold popMaxEntry? at h
  cases hm : m.maxEntry? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e' =>
    rw [hm] at h
    replace h : some (e', m.erase e'.1) = some (e, m') := h
    injection h with h
    injection h with h1 h2
    rw [h1]

/-- `popMaxEntry?`'s rest is the map with the popped key erased. -/
theorem popMaxEntry?_erase {m : IndexedMap κ V} {e : κ × V} {m' : IndexedMap κ V}
    (h : m.popMaxEntry? = some (e, m')) : m' = m.erase e.1 := by
  unfold popMaxEntry? at h
  cases hm : m.maxEntry? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some e' =>
    rw [hm] at h
    replace h : some (e', m.erase e'.1) = some (e, m') := h
    injection h with h
    injection h with h1 h2
    rw [← h2, h1]

/-- `popMaxEntry?` answers `none` exactly on the empty map. -/
theorem popMaxEntry?_eq_none {m : IndexedMap κ V} : m.popMaxEntry? = none ↔ m = empty := by
  constructor
  · intro h
    unfold popMaxEntry? at h
    cases hm : m.maxEntry? with
    | none => exact maxEntry?_eq_none.mp hm
    | some e => rw [hm] at h; exact absurd h (by simp)
  · intro h
    unfold popMaxEntry?
    rw [maxEntry?_eq_none.mpr h]

/-- Looking up the erased key reads `none`. -/
@[simp]
theorem get?_erase_self (m : IndexedMap κ V) (k : κ) : (m.erase k).get? k = none := by
  show (m.raw.erase (toNat k)).get? (toNat k) = none
  rw [NatMap.get?_erase, if_pos rfl]

/-- Looking up any other key after an erase reads through unchanged (the `_ne` companion of
`get?_erase_self`; together they pin `erase`'s lookups without needing `DecidableEq κ`). -/
theorem get?_erase_ne {m : IndexedMap κ V} {b a : κ} (h : a ≠ b) :
    (m.erase b).get? a = m.get? a := by
  show (m.raw.erase (toNat b)).get? (toNat a) = m.raw.get? (toNat a)
  rw [NatMap.get?_erase, if_neg (fun hn => h (toNat_inj hn))]

/-- Lookup after `filter`: a key reads through exactly when its entry is accepted by `p`. -/
theorem get?_filter (p : κ → V → Bool) (m : IndexedMap κ V) (k : κ) :
    (m.filter p).get? k
      = match m.get? k with
        | some v => if p k v then some v else none
        | none => none := by
  show (m.raw.filter (fun n v => match ofNat? n with | some k => p k v | none => false)).get?
        (toNat k)
      = match m.raw.get? (toNat k) with
        | some v => if p k v then some v else none
        | none => none
  rw [NatMap.get?_filter]
  cases hg : m.raw.get? (toNat k) with
  | none => rfl
  | some v => simp only [ofNat?_toNat]

/-- Lookup in `split`'s left part: exactly the entries with key strictly below the split key in
encoding order. -/
theorem get?_split_left (m : IndexedMap κ V) (b a : κ) :
    (m.split b).1.get? a = if toNat a < toNat b then m.get? a else none :=
  NatMap.get?_split_left m.raw (toNat b) (toNat a)

/-- `split`'s middle component is the value at the split key itself. -/
theorem split_at (m : IndexedMap κ V) (k : κ) : (m.split k).2.1 = m.get? k := rfl

/-- Lookup in `split`'s right part: exactly the entries with key strictly above the split key in
encoding order. -/
theorem get?_split_right (m : IndexedMap κ V) (b a : κ) :
    (m.split b).2.2.get? a = if toNat b < toNat a then m.get? a else none :=
  NatMap.get?_split_right m.raw (toNat b) (toNat a)

/-- Lookup in `range`: a key reads through exactly when it lies in the inclusive encoding-order
window `[lo, hi]`. -/
theorem get?_range (m : IndexedMap κ V) (lo hi a : κ) :
    (m.range lo hi).get? a
      = if toNat lo ≤ toNat a ∧ toNat a ≤ toNat hi then m.get? a else none :=
  NatMap.get?_range m.raw (toNat lo) (toNat hi) (toNat a)

/-- Membership in `split`'s left part: exactly the keys strictly below the split key in encoding
order. -/
theorem mem_split_left {m : IndexedMap κ V} {b a : κ} :
    a ∈ (m.split b).1 ↔ a ∈ m ∧ toNat a < toNat b := by
  show toNat a ∈ (m.raw.split (toNat b)).1 ↔ toNat a ∈ m.raw ∧ toNat a < toNat b
  exact NatMap.mem_split_left

/-- Membership in `split`'s right part: exactly the keys strictly above the split key in
encoding order. -/
theorem mem_split_right {m : IndexedMap κ V} {b a : κ} :
    a ∈ (m.split b).2.2 ↔ a ∈ m ∧ toNat b < toNat a := by
  show toNat a ∈ (m.raw.split (toNat b)).2.2 ↔ toNat a ∈ m.raw ∧ toNat b < toNat a
  exact NatMap.mem_split_right

/-- Every key of `split`'s left part lies strictly below the split key in encoding order. -/
theorem lt_of_mem_split_left {m : IndexedMap κ V} {b a : κ} (h : a ∈ (m.split b).1) :
    toNat a < toNat b :=
  (mem_split_left.mp h).2

/-- Every key of `split`'s right part lies strictly above the split key in encoding order. -/
theorem lt_of_mem_split_right {m : IndexedMap κ V} {b a : κ} (h : a ∈ (m.split b).2.2) :
    toNat b < toNat a :=
  (mem_split_right.mp h).2

/-- Membership in `range`: exactly the keys within the inclusive encoding-order window
`[lo, hi]`. -/
theorem mem_range {m : IndexedMap κ V} {lo hi a : κ} :
    a ∈ m.range lo hi ↔ a ∈ m ∧ toNat lo ≤ toNat a ∧ toNat a ≤ toNat hi := by
  show toNat a ∈ m.raw.range (toNat lo) (toNat hi)
      ↔ toNat a ∈ m.raw ∧ toNat lo ≤ toNat a ∧ toNat a ≤ toNat hi
  exact NatMap.mem_range

/-- Membership after `erase`: `a` survives exactly when it was present and is not the erased
key. -/
theorem mem_erase {m : IndexedMap κ V} {b a : κ} : a ∈ m.erase b ↔ a ∈ m ∧ a ≠ b := by
  show toNat a ∈ m.raw.erase (toNat b) ↔ toNat a ∈ m.raw ∧ a ≠ b
  rw [NatMap.mem_erase]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨h1, fun he => h2 (by rw [he])⟩
  · intro ⟨h1, h2⟩
    exact ⟨h1, fun hn => h2 (toNat_inj hn)⟩

/-- Membership after `filter`: `a` survives exactly when it held a value the predicate
accepts. -/
theorem mem_filter {m : IndexedMap κ V} {p : κ → V → Bool} {a : κ} :
    a ∈ m.filter p ↔ ∃ v, m.get? a = some v ∧ p a v = true := by
  show toNat a ∈ m.raw.filter (fun n v => match ofNat? n with | some k => p k v | none => false)
      ↔ ∃ v, m.raw.get? (toNat a) = some v ∧ p a v = true
  rw [NatMap.mem_filter]
  constructor
  · intro ⟨v, hv, hp⟩
    refine ⟨v, hv, ?_⟩
    simp only [ofNat?_toNat] at hp
    exact hp
  · intro ⟨v, hv, hp⟩
    refine ⟨v, hv, ?_⟩
    simp only [ofNat?_toNat]
    exact hp

/-- Disjointness characterization: `m.isDisjoint t` holds exactly when the two maps share no key
(values are irrelevant). (The ← direction uses `wf`.) -/
theorem isDisjoint_iff {m t : IndexedMap κ V} :
    m.isDisjoint t = true ↔ ∀ k : κ, k ∈ m → k ∉ t := by
  show m.raw.isDisjoint t.raw = true ↔ _
  rw [NatMap.isDisjoint_iff]
  constructor
  · intro h k hk
    exact h (toNat k) hk
  · intro h n hns hnt
    obtain ⟨k, hk⟩ := m.wf n hns
    subst hk
    exact h k hns hnt

/-- Disjointness is symmetric. -/
theorem isDisjoint_symm {m t : IndexedMap κ V} (h : m.isDisjoint t = true) :
    t.isDisjoint m = true :=
  NatMap.isDisjoint_symm h

/-- No key of `m` lies in `t` when the two maps are disjoint. -/
theorem not_mem_of_isDisjoint {m t : IndexedMap κ V} {k : κ} (h : m.isDisjoint t = true)
    (hk : k ∈ m) : k ∉ t :=
  isDisjoint_iff.mp h k hk

/-- The empty map is a right identity of `diff`. -/
theorem diff_empty (m : IndexedMap κ V) : m.diff ∅ = m :=
  ext (NatMap.diff_empty m.raw)

/-- Subtracting a map from itself leaves the empty map. -/
theorem diff_self (m : IndexedMap κ V) : m.diff m = ∅ :=
  ext (NatMap.diff_self m.raw)

/-- `get?` after `diff`: a key of `m` reads its original value exactly when absent from `t`
(`t`'s values are irrelevant). -/
theorem get?_diff (m t : IndexedMap κ V) (k : κ) :
    (m.diff t).get? k = if t.contains k = true then none else m.get? k :=
  NatMap.get?_diff m.raw t.raw (toNat k)

/-- Membership in a difference: `a ∈ m.diff t` exactly when `a ∈ m` and `a ∉ t`. -/
theorem mem_diff {m t : IndexedMap κ V} {a : κ} : a ∈ m.diff t ↔ a ∈ m ∧ a ∉ t := by
  show toNat a ∈ m.raw.diff t.raw ↔ toNat a ∈ m.raw ∧ ¬(toNat a ∈ t.raw)
  exact NatMap.mem_diff

/-- **`diff` collapses exactly on the domain-subset order**: subtracting `t` leaves the empty
map iff every key of `m` is a key of `t` (values are irrelevant). (The ← direction uses `wf`.) -/
theorem diff_eq_empty_iff {m t : IndexedMap κ V} : m.diff t = ∅ ↔ ∀ k : κ, k ∈ m → k ∈ t := by
  constructor
  · intro h k hk
    have hr : m.raw.diff t.raw = ∅ := congrArg IndexedMap.raw h
    exact (NatMap.diff_eq_empty_iff.mp hr) (toNat k) hk
  · intro h
    refine ext (NatMap.diff_eq_empty_iff.mpr ?_)
    intro n hn
    obtain ⟨k, hk⟩ := m.wf n hn
    subst hk
    exact h k hn

/-- **Restriction collapses `diff`** (for reflexive `rel`): if `m` restricts `t`, subtracting
`t` leaves the empty map. -/
theorem diff_eq_empty_of_restricts (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    {m t : IndexedMap κ V} (h : IndexedMap.restricts rel m t = true) : m.diff t = ∅ :=
  ext (NatMap.diff_eq_empty_of_restricts rel hrefl h)

/-- The empty map is a right identity of `symmDiff`. -/
theorem symmDiff_empty (m : IndexedMap κ V) : m.symmDiff ∅ = m :=
  ext (NatMap.symmDiff_empty m.raw)

/-- The empty map is a left identity of `symmDiff`. -/
theorem empty_symmDiff (m : IndexedMap κ V) : (∅ : IndexedMap κ V).symmDiff m = m :=
  ext (NatMap.empty_symmDiff m.raw)

/-- A map cancels against itself: every key is shared, so everything drops. -/
theorem symmDiff_self (m : IndexedMap κ V) : m.symmDiff m = ∅ :=
  ext (NatMap.symmDiff_self m.raw)

/-- `symmDiff` is commutative — there is no combine to order: the surviving value always comes
from whichever map holds the key alone. -/
theorem symmDiff_comm (m t : IndexedMap κ V) : m.symmDiff t = t.symmDiff m :=
  ext (NatMap.symmDiff_comm m.raw t.raw)

/-- `get?` after `symmDiff`: a key reads its value from whichever map holds it alone, and reads
nothing where the two key sets overlap. -/
theorem get?_symmDiff (m t : IndexedMap κ V) (k : κ) :
    (m.symmDiff t).get? k =
      if m.contains k = true then (if t.contains k = true then none else m.get? k)
      else t.get? k :=
  NatMap.get?_symmDiff m.raw t.raw (toNat k)

/-- Membership in a `symmDiff`: `a ∈ m.symmDiff t` exactly when `a` is a key of exactly one of
the two maps. -/
theorem mem_symmDiff {m t : IndexedMap κ V} {a : κ} :
    a ∈ m.symmDiff t ↔ (a ∈ m ∧ a ∉ t) ∨ (a ∉ m ∧ a ∈ t) := by
  show toNat a ∈ m.raw.symmDiff t.raw
      ↔ (toNat a ∈ m.raw ∧ ¬(toNat a ∈ t.raw)) ∨ (¬(toNat a ∈ m.raw) ∧ toNat a ∈ t.raw)
  exact NatMap.mem_symmDiff

/-- **`symmDiff` collapses exactly on domain equality**: the symmetric difference is empty iff
the two maps hold the same keys — the values are irrelevant. (The ← direction uses both `wf`s.) -/
theorem symmDiff_eq_empty_iff {m t : IndexedMap κ V} :
    m.symmDiff t = ∅ ↔ ∀ k : κ, (k ∈ m ↔ k ∈ t) := by
  constructor
  · intro h k
    have hr : m.raw.symmDiff t.raw = ∅ := congrArg IndexedMap.raw h
    exact NatMap.symmDiff_eq_empty_iff.mp hr (toNat k)
  · intro h
    refine ext (NatMap.symmDiff_eq_empty_iff.mpr ?_)
    intro n
    constructor
    · intro hn
      obtain ⟨k, hk⟩ := m.wf n hn
      subst hk
      exact (h k).mp hn
    · intro hn
      obtain ⟨k, hk⟩ := t.wf n hn
      subst hk
      exact (h k).mpr hn

/-- **`symmDiff` decomposes as the `join` of the two one-sided differences** — for any combine:
the differences hold disjoint keys, so the combine never fires. -/
theorem symmDiff_eq_join_diff (combine : V → V → V) (m t : IndexedMap κ V) :
    m.symmDiff t = IndexedMap.join combine (m.diff t) (t.diff m) :=
  ext (NatMap.symmDiff_eq_join_diff combine m.raw t.raw)

/-- **Restriction turns `symmDiff` into the reverse difference** (for reflexive `rel`): if `m`
restricts `t`, every key of `m` is shared (and cancels), leaving exactly `t`'s entries outside
`m`. -/
theorem symmDiff_eq_diff_of_restricts (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    {m t : IndexedMap κ V} (h : IndexedMap.restricts rel m t = true) :
    m.symmDiff t = t.diff m :=
  ext (NatMap.symmDiff_eq_diff_of_restricts rel hrefl h)

end IndexedMap

/-- `IndexedMap κ` is a lawful functor: `map` satisfies the identity and composition laws. The
proofs come straight from the raw `NatMap.map_id`/`map_comp`, since `map` only rewrites values
and preserves keys. -/
instance {κ : Type u} [Countable κ] : LawfulFunctor (IndexedMap κ) where
  map_const := rfl
  id_map := IndexedMap.map_id
  comp_map := IndexedMap.map_comp

end NatCol
