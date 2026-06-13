import NatCol.Set
import NatCol.Countable

/-!
# `IndexedSet`: a set of `Countable` values

An `IndexedSet α` is a bare `NatSet` keyed by the `Countable` encoding of `α`, bundled with the
invariant (`wf`) that every raw key decodes. Elements live only as trie positions — zero
per-element storage, the leaves stay plain `UInt32` bitsets — and are decoded (`Countable.ofNat?`)
on the way out. A win over hash sets whenever `toNat` is cheaper than hashing.

Ordered queries (`min?`/`max?`/`succ?`/`split`/`range`…) and the ordered theorems below speak the
**encoding order** (`Countable.toNat`); the bundled instances are all order-preserving, so for
them this is the natural order of the key type.

The `wf` invariant is what turns the raw answers total: decoding a key that is *in* the set never
fails, so the `none`-completeness theorems (`le_of_succ?_eq_none`, `popMin?_eq_none`, …) carry
over from `NatSet` undiluted.
-/

namespace NatCol
----------------------------------------------------------------------------------------------------
-- Implementation
----------------------------------------------------------------------------------------------------

/-- A set of `α` values keyed by their `Countable` encoding: a bare `NatSet` of encodings
together with the invariant that every raw key is the encoding of some `α` value. -/
structure IndexedSet (α : Type u) [Countable α] where
  /-- The underlying `NatSet` of encodings. -/
  raw : NatSet
  /-- Every raw key is the encoding of some `α` value. -/
  wf : ∀ n, n ∈ raw → ∃ a : α, Countable.toNat a = n

namespace IndexedSet

open Countable

variable {α : Type u} [Countable α]

/-- Two indexed sets with equal raw sets are equal — the `wf` proof is irrelevant (a `Prop`).
Every raw-level equation lifts through this. -/
theorem ext {s t : IndexedSet α} (h : s.raw = t.raw) : s = t := by
  obtain ⟨sr, sw⟩ := s
  obtain ⟨tr, tw⟩ := t
  subst h
  rfl

/-- The decode of a present raw key succeeds and is faithful — `wf` composed with the class
law. The workhorse behind every theorem that converts a raw answer back to `α`. -/
theorem ofNat?_of_mem_raw {s : IndexedSet α} {n : Nat} (h : n ∈ s.raw) :
    ∃ a : α, ofNat? n = some a ∧ toNat a = n := by
  obtain ⟨a, ha⟩ := s.wf n h
  exact ⟨a, ofNat?_eq_some_iff.mpr ha, ha⟩

/-- Transfer `wf` across an op whose result keys come from the input (the one-input case). -/
private theorem wf_of_subset (s : IndexedSet α) {t : NatSet} (h : ∀ n, n ∈ t → n ∈ s.raw) :
    ∀ n, n ∈ t → ∃ a : α, toNat a = n :=
  fun n hn => s.wf n (h n hn)

/-- Transfer `wf` across an op whose result keys come from either input (the two-input case). -/
private theorem wf_of_subset₂ (s t : IndexedSet α) {u : NatSet}
    (h : ∀ n, n ∈ u → n ∈ s.raw ∨ n ∈ t.raw) : ∀ n, n ∈ u → ∃ a : α, toNat a = n :=
  fun n hn => (h n hn).elim (s.wf n) (t.wf n)

instance : BEq (IndexedSet α) := ⟨fun s t => s.raw == t.raw⟩
instance : LawfulBEq (IndexedSet α) where
  eq_of_beq {s t} h := ext (eq_of_beq (show (s.raw == t.raw) = true from h))
  rfl {s} := beq_self_eq_true s.raw
instance : DecidableEq (IndexedSet α) := fun s t =>
  decidable_of_iff (s.raw = t.raw) ⟨ext, fun h => by rw [h]⟩
instance : Hashable (IndexedSet α) := ⟨fun s => hash s.raw⟩
instance : LawfulHashable (IndexedSet α) where
  hash_eq _ _ h := by rw [eq_of_beq h]
instance : EmptyCollection (IndexedSet α) :=
  ⟨⟨∅, fun n hn => by
      replace hn : NatCollection.contains NatCollection.empty n = true := hn
      rw [NatCollection.contains_eq, NatCollection.get?_empty] at hn
      exact absurd hn (by decide)⟩⟩

/-- The empty set. -/
def empty : IndexedSet α := ∅
def isEmpty (s : IndexedSet α) : Bool := s.raw.isEmpty
def size (s : IndexedSet α) : Nat := s.raw.size
def contains (s : IndexedSet α) (a : α) : Bool := s.raw.contains (toNat a)
def insert (s : IndexedSet α) (a : α) : IndexedSet α :=
  ⟨s.raw.insert (toNat a), fun n hn => (NatSet.mem_insert.mp hn).elim (s.wf n) fun hk => ⟨a, hk.symm⟩⟩
def erase (s : IndexedSet α) (a : α) : IndexedSet α :=
  ⟨s.raw.erase (toNat a), s.wf_of_subset fun _ hn => (NatSet.mem_erase.mp hn).1⟩

/-- The least element in encoding order, `none` on the empty set. O(depth). The decode never
fails on a well-formed set (`wf`). -/
def min? (s : IndexedSet α) : Option α := s.raw.min?.bind ofNat?
/-- The greatest element in encoding order, `none` on the empty set. O(depth). -/
def max? (s : IndexedSet α) : Option α := s.raw.max?.bind ofNat?
/-- The least element strictly above `a` in encoding order (successor), `none` if there is
none. O(depth). -/
def succ? (s : IndexedSet α) (a : α) : Option α := (s.raw.succ? (toNat a)).bind ofNat?
/-- The greatest element strictly below `a` in encoding order (predecessor), `none` if there is
none. O(depth). -/
def pred? (s : IndexedSet α) (a : α) : Option α := (s.raw.pred? (toNat a)).bind ofNat?
/-- The least element at or above `a` in encoding order: `a` itself when present, else the
successor. -/
def succEq? (s : IndexedSet α) (a : α) : Option α := (s.raw.succEq? (toNat a)).bind ofNat?
/-- The greatest element at or below `a` in encoding order: `a` itself when present, else the
predecessor. -/
def predEq? (s : IndexedSet α) (a : α) : Option α := (s.raw.predEq? (toNat a)).bind ofNat?

/-- The least element together with the set without it, `none` on the empty set (the
priority-queue step). `min?` then `erase` — the same two walks the raw pop performs. -/
def popMin? (s : IndexedSet α) : Option (α × IndexedSet α) :=
  match s.min? with
  | none => none
  | some a => some (a, s.erase a)
/-- The greatest element together with the set without it, `none` on the empty set. -/
def popMax? (s : IndexedSet α) : Option (α × IndexedSet α) :=
  match s.max? with
  | none => none
  | some a => some (a, s.erase a)

/-- Union. -/
def union (s t : IndexedSet α) : IndexedSet α :=
  ⟨s.raw ∪ t.raw, wf_of_subset₂ s t fun _ hn => NatSet.mem_union.mp hn⟩
/-- Intersection. -/
def inter (s t : IndexedSet α) : IndexedSet α :=
  ⟨s.raw ∩ t.raw, s.wf_of_subset fun _ hn => (NatSet.mem_inter.mp hn).1⟩
/-- Difference: the elements of `s` not in `t` — `NatSet`'s structural merge walk. -/
def diff (s t : IndexedSet α) : IndexedSet α :=
  ⟨s.raw \ t.raw, s.wf_of_subset fun _ hn => (NatSet.mem_diff.mp hn).1⟩
/-- Symmetric difference: the elements in exactly one of `s`, `t` — `NatSet`'s one-pass
structural merge. -/
def symmDiff (s t : IndexedSet α) : IndexedSet α :=
  ⟨s.raw.symmDiff t.raw, wf_of_subset₂ s t fun _ hn =>
      (NatSet.mem_symmDiff.mp hn).elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)⟩
/-- Split at `a`: `(elements below a, elements at or above a)` in encoding order — two structural
prunes; both parts share every off-path subtree with `s`. -/
def split (s : IndexedSet α) (a : α) : IndexedSet α × IndexedSet α :=
  (⟨(s.raw.split (toNat a)).1, s.wf_of_subset fun _ hn => (NatSet.mem_split_left.mp hn).1⟩,
   ⟨(s.raw.split (toNat a)).2, s.wf_of_subset fun _ hn => (NatSet.mem_split_right.mp hn).1⟩)
/-- The elements in the inclusive encoding-order range `[lo, hi]` — a double structural prune;
everything strictly inside the window is shared, not copied. -/
def range (s : IndexedSet α) (lo hi : α) : IndexedSet α :=
  ⟨s.raw.range (toNat lo) (toNat hi), s.wf_of_subset fun _ hn => (NatSet.mem_range.mp hn).1⟩
/-- Subset test. -/
def subset (s t : IndexedSet α) : Bool := s.raw.subset t.raw
/-- Whether `s` and `t` share no element — the intersection's structural walk without building
the intersection. -/
def isDisjoint (s t : IndexedSet α) : Bool := s.raw.isDisjoint t.raw

instance : Union (IndexedSet α) := ⟨union⟩
instance : Inter (IndexedSet α) := ⟨inter⟩
instance : SDiff (IndexedSet α) := ⟨diff⟩

-- `subset` is `Bool`-valued, so phrase `s ⊆ t` as `subset … = true` and make it
-- decidable, keeping it usable in `#guard` / `decide`.
instance : HasSubset (IndexedSet α) := ⟨fun s t => s.subset t = true⟩
instance (s t : IndexedSet α) : Decidable (s ⊆ t) := inferInstanceAs (Decidable (s.subset t = true))

-- `a ∈ s` reduces to the `Bool` `contains`, so it stays decidable (usable in `#guard` / `decide`).
instance : Membership α (IndexedSet α) := ⟨fun s a => s.contains a = true⟩
instance (a : α) (s : IndexedSet α) : Decidable (a ∈ s) :=
  inferInstanceAs (Decidable (s.contains a = true))

/-- Elements in ascending encoding order. The decode never fails on a well-formed set (`wf`), so
the `filterMap` drops nothing. -/
def toList (s : IndexedSet α) : List α := s.raw.toList.filterMap ofNat?
/-- Build a set from a list of elements. -/
def ofList (l : List α) : IndexedSet α := l.foldl (fun s a => s.insert a) ∅

/-- `repr` renders the `ofList` of the ascending element list — valid Lean that rebuilds the
set. -/
instance [Repr α] : Repr (IndexedSet α) where
  reprPrec s prec := Repr.addAppParen ("IndexedSet.ofList " ++ repr s.toList) prec

/-- `toString` displays the elements in ascending encoding order as `{e₁, e₂, …}`. -/
instance [ToString α] : ToString (IndexedSet α) where
  toString s := "{" ++ String.intercalate ", " (s.toList.map toString) ++ "}"

/-- Fold `f` over elements in ascending encoding order, starting from `init`. Raw keys are
decoded on the way out; a decode can only fail off a well-formed set (`wf`), in which case the
key is skipped — the same benign-skip convention as `toList` and the other walks below. -/
def fold {β : Type w} (f : β → α → β) (init : β) (s : IndexedSet α) : β :=
  s.raw.fold (fun acc n => match ofNat? n with | some a => f acc a | none => acc) init

/-- Monadic fold over elements in ascending encoding order, threading the accumulator through
`m`. The monadic companion of `fold` (recovered by instantiating `m := Id`). -/
def foldM {β : Type w} {m : Type w → Type w'} [Monad m] (f : β → α → m β) (init : β)
    (s : IndexedSet α) : m β :=
  s.raw.foldM (fun acc n => match ofNat? n with | some a => f acc a | none => pure acc) init

/-- Whether every element satisfies `p`, short-circuiting at the first that fails (vacuously true
on the empty set). -/
def all (p : α → Bool) (s : IndexedSet α) : Bool :=
  s.raw.all fun n => match ofNat? n with | some a => p a | none => true

/-- Whether some element satisfies `p`, short-circuiting at the first that holds (vacuously false
on the empty set). -/
def any (p : α → Bool) (s : IndexedSet α) : Bool :=
  s.raw.any fun n => match ofNat? n with | some a => p a | none => false

/-- Keep only the elements satisfying `p`. The result is canonical, so it equals the set built
directly from the surviving elements. -/
def filter (p : α → Bool) (s : IndexedSet α) : IndexedSet α :=
  ⟨s.raw.filter (fun n => match ofNat? n with | some a => p a | none => false),
   s.wf_of_subset fun _ hn => (NatSet.mem_filter.mp hn).1⟩

/-- Split `s` by `p`: the first component keeps the elements satisfying `p`, the second the rest.
Two structural `filter` passes, so both parts are canonical. -/
def partition (p : α → Bool) (s : IndexedSet α) : IndexedSet α × IndexedSet α :=
  (s.filter p, s.filter fun a => !p a)

/-- Monadic `all`: whether every element satisfies the monadic predicate `p`, threading effects
in ascending encoding order and short-circuiting at the first failure. -/
def allM {m : Type → Type w} [Monad m] (p : α → m Bool) (s : IndexedSet α) : m Bool :=
  s.raw.allM fun n => match ofNat? n with | some a => p a | none => pure true

/-- Monadic `any`: whether some element satisfies `p`, short-circuiting at the first success. -/
def anyM {m : Type → Type w} [Monad m] (p : α → m Bool) (s : IndexedSet α) : m Bool :=
  s.raw.anyM fun n => match ofNat? n with | some a => p a | none => pure false

/-- Monadic `filter`: keep the elements for which `p` returns `true`, running `p` on every
element in ascending encoding order and threading its effects through `m`. The result is rebuilt
from the survivors, so it is canonical and equals the pure `filter` when `p` is effect-free.
Restricted to `Type`-valued elements, as `List.filterM` is. -/
def filterM {α : Type} [Countable α] {m : Type → Type w} [Monad m] (p : α → m Bool)
    (s : IndexedSet α) : m (IndexedSet α) := do
  let survivors ← s.toList.filterM p
  pure (ofList survivors)

end IndexedSet

/-! ## Tests -/

section Tests

-- membership / size / idempotent insert on `Char` keys (code-point encoding)
#guard (∅ : IndexedSet Char).isEmpty
#guard (∅ : IndexedSet Char).size = 0
#guard 'x' ∉ (∅ : IndexedSet Char)
#guard ((∅ : IndexedSet Char).insert 'x').size = 1
#guard 'x' ∈ ((∅ : IndexedSet Char).insert 'x')
#guard 'y' ∉ ((∅ : IndexedSet Char).insert 'x')
#guard ((∅ : IndexedSet Char).insert 'x' |>.insert 'x') = (∅ : IndexedSet Char).insert 'x'

-- ofList / toList round trip: deduplicated, ascending code points ('B' = 66 < 'a' = 97)
#guard (IndexedSet.ofList ['c', 'a', 'b', 'a']).toList = ['a', 'b', 'c']
#guard (IndexedSet.ofList ['a', 'B']).toList = ['B', 'a']
#guard (IndexedSet.ofList ['c', 'a', 'b']).size = 3

-- erase undoes insert; erasing an absent element is a no-op
#guard ((IndexedSet.ofList ['a', 'b']).erase 'a').toList = ['b']
#guard (IndexedSet.ofList ['a', 'b']).erase 'z' = IndexedSet.ofList ['a', 'b']
#guard ((∅ : IndexedSet Char).insert 'x' |>.erase 'x') = (∅ : IndexedSet Char)

-- lattice ops via the notation instances
#guard ((IndexedSet.ofList ['a', 'b']) ∪ (IndexedSet.ofList ['b', 'c'])).toList = ['a', 'b', 'c']
#guard ((IndexedSet.ofList ['a', 'b', 'c']) ∩ (IndexedSet.ofList ['b', 'c', 'd'])).toList = ['b', 'c']
#guard ((IndexedSet.ofList ['a', 'b', 'c']) \ (IndexedSet.ofList ['b'])).toList = ['a', 'c']
#guard ((IndexedSet.ofList ['a', 'b']).symmDiff (IndexedSet.ofList ['b', 'c'])).toList = ['a', 'c']
#guard (IndexedSet.ofList ['a', 'b']) ⊆ (IndexedSet.ofList ['a', 'b', 'c'])
#guard ¬ ((IndexedSet.ofList ['a', 'z']) ⊆ (IndexedSet.ofList ['a', 'b']))
#guard (IndexedSet.ofList ['a', 'b']).isDisjoint (IndexedSet.ofList ['c', 'd'])
#guard !(IndexedSet.ofList ['a', 'b']).isDisjoint (IndexedSet.ofList ['b'])

-- ordered queries speak the encoding order — for `Char`, code-point order
#guard (IndexedSet.ofList ['m', 'a', 'z']).min? = some 'a'
#guard (IndexedSet.ofList ['m', 'a', 'z']).max? = some 'z'
#guard (∅ : IndexedSet Char).min? = none
#guard (∅ : IndexedSet Char).max? = none
#guard (IndexedSet.ofList ['a', 'm', 'z']).succ? 'a' = some 'm'
#guard (IndexedSet.ofList ['a', 'm', 'z']).succ? 'b' = some 'm'
#guard (IndexedSet.ofList ['a', 'm', 'z']).succ? 'z' = none
#guard (IndexedSet.ofList ['a', 'm', 'z']).pred? 'm' = some 'a'
#guard (IndexedSet.ofList ['a', 'm', 'z']).pred? 'a' = none
#guard (IndexedSet.ofList ['a', 'm', 'z']).succEq? 'm' = some 'm'
#guard (IndexedSet.ofList ['a', 'm', 'z']).succEq? 'n' = some 'z'
#guard (IndexedSet.ofList ['a', 'm', 'z']).predEq? 'm' = some 'm'
#guard (IndexedSet.ofList ['a', 'm', 'z']).predEq? 'l' = some 'a'

-- pop: the priority-queue step
#guard (IndexedSet.ofList ['b', 'a', 'c']).popMin? = some ('a', IndexedSet.ofList ['b', 'c'])
#guard (IndexedSet.ofList ['b', 'a', 'c']).popMax? = some ('c', IndexedSet.ofList ['a', 'b'])
#guard (∅ : IndexedSet Char).popMin? = none

-- popMin? drains in ascending order: collecting the popped elements recovers `toList`
private def drainMinI : Nat → IndexedSet Char → List Char
  | 0, _ => []
  | fuel + 1, s =>
    match s.popMin? with
    | none => []
    | some (a, rest) => a :: drainMinI fuel rest
#guard drainMinI 10 (IndexedSet.ofList ['c', 'a', 'b']) = ['a', 'b', 'c']
#guard drainMinI 10 (IndexedSet.ofList ['c', 'a', 'b']) = (IndexedSet.ofList ['c', 'a', 'b']).toList

-- split / range: structural prunes at encoding-order bounds
#guard (IndexedSet.ofList ['a', 'c', 'e']).split 'c'
        = (IndexedSet.ofList ['a'], IndexedSet.ofList ['c', 'e'])
#guard (IndexedSet.ofList ['a', 'b', 'c', 'd']).range 'b' 'c' = IndexedSet.ofList ['b', 'c']
#guard (IndexedSet.ofList ['a', 'b', 'c']).range 'a' 'z' = IndexedSet.ofList ['a', 'b', 'c']
#guard (∅ : IndexedSet Char).split 'a' = (∅, ∅)

-- fold visits elements in ascending encoding order
#guard (IndexedSet.ofList ['c', 'a', 'b']).fold (fun acc c => acc.push c) "" = "abc"
#guard (∅ : IndexedSet Char).fold (fun acc c => acc.push c) "" = ""

-- all / any / filter / partition over decoded elements
#guard (IndexedSet.ofList ['a', 'b']).all (·.isLower)
#guard !(IndexedSet.ofList ['a', 'B']).all (·.isLower)
#guard (IndexedSet.ofList ['a', 'B']).any (·.isUpper)
#guard !(IndexedSet.ofList ['a', 'b']).any (·.isUpper)
#guard ((IndexedSet.ofList ['a', 'B', 'c']).filter (·.isLower)).toList = ['a', 'c']
#guard (IndexedSet.ofList ['a', 'B', 'c']).partition (·.isLower)
        = (IndexedSet.ofList ['a', 'c'], IndexedSet.ofList ['B'])

-- monadic walks in `Id` reproduce the pure ops
#guard Id.run ((IndexedSet.ofList ['a', 'b']).allM (fun c => pure c.isLower))
#guard !Id.run ((IndexedSet.ofList ['a', 'b']).anyM (fun c => pure c.isUpper))
#guard Id.run ((IndexedSet.ofList ['c', 'a', 'b']).foldM (fun acc c => pure (acc.push c)) "") = "abc"
#guard Id.run ((IndexedSet.ofList ['a', 'B', 'c']).filterM (fun c => pure c.isLower))
        = IndexedSet.ofList ['a', 'c']

-- UInt64 keys: deep / sparse encodings exercise tall tries
private def deep : IndexedSet UInt64 :=
  IndexedSet.ofList [1, 5000000000, 18446744073709551615]
#guard deep.size = 3
#guard (5000000000 : UInt64) ∈ deep
#guard (2 : UInt64) ∉ deep
#guard deep.min? = some 1
#guard deep.max? = some 18446744073709551615
#guard deep.succ? 1 = some 5000000000
#guard (deep.erase 5000000000).toList = [1, 18446744073709551615]
#guard (deep ∪ IndexedSet.ofList [2, 3]).toList = [1, 2, 3, 5000000000, 18446744073709551615]

-- `IndexedSet Nat` coincides with `NatSet` (the identity encoding)
#guard (IndexedSet.ofList [3, 1, 2] : IndexedSet Nat).raw = NatSet.ofList [3, 1, 2]
#guard (IndexedSet.ofList [3, 1, 2] : IndexedSet Nat).toList = [1, 2, 3]

-- Bool / Fin sanity
#guard (IndexedSet.ofList [true, false]).toList = [false, true]
#guard (IndexedSet.ofList ([1, 3] : List (Fin 5))).contains 3

-- lattice laws on concrete instances
private def ca : IndexedSet Char := IndexedSet.ofList ['a', 'b', 'x']
private def cb : IndexedSet Char := IndexedSet.ofList ['b', 'c', 'x']
#guard ca ∪ cb = cb ∪ ca
#guard ca ∩ cb = cb ∩ ca
#guard ca ∪ ca = ca
#guard ca ∪ (ca ∩ cb) = ca
#guard (ca \ cb) ∪ (ca ∩ cb) = ca
#guard (ca.symmDiff cb).symmDiff cb = ca
#guard ca ⊆ ca ∪ cb
#guard (ca ∩ cb) ⊆ ca
#guard (ca ∪ cb).size + (ca ∩ cb).size = ca.size + cb.size

-- lawful structural equality, decidable propositional equality, hash respecting both
example : LawfulBEq (IndexedSet Char) := inferInstance
example : LawfulHashable (IndexedSet Char) := inferInstance
example : DecidableEq (IndexedSet Char) := inferInstance
#guard (IndexedSet.ofList ['b', 'a'] == IndexedSet.ofList ['a', 'b', 'a']) = true
#guard hash (IndexedSet.ofList ['a', 'b']) = hash (IndexedSet.ofList ['b', 'a'])

-- printing
#guard toString (IndexedSet.ofList ['b', 'a']) = "{a, b}"
#guard toString (∅ : IndexedSet Char) = "{}"
#guard reprStr (IndexedSet.ofList ['b', 'a']) = "IndexedSet.ofList ['a', 'b']"

end Tests

----------------------------------------------------------------------------------------------------
-- Theorems
----------------------------------------------------------------------------------------------------

namespace IndexedSet

open Countable

variable {α : Type u} [Countable α]

/-- The empty set is a left identity of `∪` (union). -/
@[simp, grind =]
theorem union_empty_left (s : IndexedSet α) : empty ∪ s = s :=
  ext (NatSet.union_empty_left s.raw)

/-- The empty set is a right identity of `∪` (union). -/
@[simp, grind =]
theorem union_empty_right (s : IndexedSet α) : s ∪ empty = s :=
  ext (NatSet.union_empty_right s.raw)

/-- Union is commutative. -/
theorem union_comm (s t : IndexedSet α) : s ∪ t = t ∪ s :=
  ext (NatSet.union_comm s.raw t.raw)

/-- Union is associative. -/
theorem union_assoc (s t u : IndexedSet α) : (s ∪ t) ∪ u = s ∪ (t ∪ u) :=
  ext (NatSet.union_assoc s.raw t.raw u.raw)

/-- The empty set is a left annihilator of `∩` (intersection). -/
@[simp, grind =]
theorem inter_empty_left (s : IndexedSet α) : empty ∩ s = empty :=
  ext (NatSet.inter_empty_left s.raw)

/-- The empty set is a right annihilator of `∩` (intersection). -/
@[simp, grind =]
theorem inter_empty_right (s : IndexedSet α) : s ∩ empty = empty :=
  ext (NatSet.inter_empty_right s.raw)

/-- Intersection is commutative. -/
theorem inter_comm (s t : IndexedSet α) : s ∩ t = t ∩ s :=
  ext (NatSet.inter_comm s.raw t.raw)

/-- Intersection is associative. -/
theorem inter_assoc (s t u : IndexedSet α) : (s ∩ t) ∩ u = s ∩ (t ∩ u) :=
  ext (NatSet.inter_assoc s.raw t.raw u.raw)

/-- The empty set is a subset of every set. -/
@[simp]
theorem subset_empty_left (s : IndexedSet α) : empty ⊆ s :=
  NatSet.subset_empty_left s.raw

/-- Subset is reflexive: every set is a subset of itself. -/
@[simp]
theorem subset_refl (s : IndexedSet α) : s ⊆ s :=
  NatSet.subset_refl s.raw

/-- Intersection is a lower bound: `s ∩ t ⊆ s`. -/
theorem inter_subset_left (s t : IndexedSet α) : s ∩ t ⊆ s :=
  NatSet.inter_subset_left s.raw t.raw

/-- Intersection is a lower bound: `s ∩ t ⊆ t`. -/
theorem inter_subset_right (s t : IndexedSet α) : s ∩ t ⊆ t :=
  NatSet.inter_subset_right s.raw t.raw

/-- Intersection is the greatest lower bound: any set below both `s` and `t` is below `s ∩ t`. -/
theorem subset_inter {s t u : IndexedSet α} (h₁ : u ⊆ s) (h₂ : u ⊆ t) : u ⊆ s ∩ t :=
  NatSet.subset_inter h₁ h₂

/-- Union is an upper bound: `s ⊆ s ∪ t`. -/
theorem subset_union_left (s t : IndexedSet α) : s ⊆ s ∪ t :=
  NatSet.subset_union_left s.raw t.raw

/-- Union is an upper bound: `t ⊆ s ∪ t`. -/
theorem subset_union_right (s t : IndexedSet α) : t ⊆ s ∪ t :=
  NatSet.subset_union_right s.raw t.raw

/-- Union is the least upper bound: any set containing both `s` and `t` contains `s ∪ t`. -/
theorem union_subset {s t u : IndexedSet α} (h₁ : s ⊆ u) (h₂ : t ⊆ u) : s ∪ t ⊆ u :=
  NatSet.union_subset h₁ h₂

/-- Subset is transitive. -/
theorem subset_trans {s t u : IndexedSet α} (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u :=
  NatSet.subset_trans hst htu

/-- Subset is anti-symmetric: `s ⊆ t` and `t ⊆ s` force `s = t`. -/
theorem subset_antisymm {s t : IndexedSet α} (hst : s ⊆ t) (hts : t ⊆ s) : s = t :=
  ext (NatSet.subset_antisymm hst hts)

/-- A freshly-inserted element is a member: `a ∈ s.insert a`. -/
@[simp]
theorem mem_insert_self (s : IndexedSet α) (a : α) : a ∈ s.insert a :=
  NatSet.mem_insert_self s.raw (toNat a)

/-- Inserting an element already in the set returns the same set. -/
theorem insert_of_mem {s : IndexedSet α} {a : α} (h : a ∈ s) : s.insert a = s :=
  ext (NatSet.insert_of_mem h)

/-- Membership after `insert`: `a` is present exactly when it was already present or is the
inserted element. -/
theorem mem_insert {s : IndexedSet α} {b a : α} : a ∈ s.insert b ↔ a ∈ s ∨ a = b := by
  show toNat a ∈ s.raw.insert (toNat b) ↔ toNat a ∈ s.raw ∨ a = b
  rw [NatSet.mem_insert]
  constructor
  · intro h
    exact h.imp id fun hn => toNat_inj hn
  · intro h
    exact h.imp id fun hn => by rw [hn]

/-- The union of a set with itself is the set. -/
@[simp]
theorem union_self (s : IndexedSet α) : s ∪ s = s :=
  ext (NatSet.union_self s.raw)

/-- The intersection of a set with itself is the set. -/
@[simp]
theorem inter_self (s : IndexedSet α) : s ∩ s = s :=
  ext (NatSet.inter_self s.raw)

/-- Membership in a union: `a ∈ s ∪ t` exactly when `a` is in either operand. -/
theorem mem_union {s t : IndexedSet α} {a : α} : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t := by
  show toNat a ∈ s.raw ∪ t.raw ↔ toNat a ∈ s.raw ∨ toNat a ∈ t.raw
  exact NatSet.mem_union

/-- Membership in an intersection: `a ∈ s ∩ t` exactly when `a` is in both operands. -/
theorem mem_inter {s t : IndexedSet α} {a : α} : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t := by
  show toNat a ∈ s.raw ∩ t.raw ↔ toNat a ∈ s.raw ∧ toNat a ∈ t.raw
  exact NatSet.mem_inter

/-- Intersection distributes over union. -/
theorem inter_union_distrib (s t u : IndexedSet α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
  ext (NatSet.inter_union_distrib s.raw t.raw u.raw)

/-- Union distributes over intersection. -/
theorem union_inter_distrib (s t u : IndexedSet α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
  ext (NatSet.union_inter_distrib s.raw t.raw u.raw)

/-- The minimum (in encoding order) is a member. -/
theorem min?_mem {s : IndexedSet α} {a : α} (h : s.min? = some a) : a ∈ s := by
  replace h : s.raw.min?.bind ofNat? = some a := h
  show toNat a ∈ s.raw
  exact NatSet.min?_mem (bind_ofNat?_eq_some h)

/-- The minimum is a lower bound in encoding order. -/
theorem min?_le {s : IndexedSet α} {a b : α} (h : s.min? = some a) (hb : b ∈ s) :
    toNat a ≤ toNat b := by
  replace h : s.raw.min?.bind ofNat? = some a := h
  exact NatSet.min?_le (bind_ofNat?_eq_some h) hb

/-- The maximum (in encoding order) is a member. -/
theorem max?_mem {s : IndexedSet α} {a : α} (h : s.max? = some a) : a ∈ s := by
  replace h : s.raw.max?.bind ofNat? = some a := h
  show toNat a ∈ s.raw
  exact NatSet.max?_mem (bind_ofNat?_eq_some h)

/-- The maximum is an upper bound in encoding order. -/
theorem le_max? {s : IndexedSet α} {a b : α} (h : s.max? = some a) (hb : b ∈ s) :
    toNat b ≤ toNat a := by
  replace h : s.raw.max?.bind ofNat? = some a := h
  exact NatSet.le_max? (bind_ofNat?_eq_some h) hb

/-- `min?` answers `none` exactly on the empty set (totality: decoding the minimum of a
well-formed set never fails). -/
theorem min?_eq_none {s : IndexedSet α} : s.min? = none ↔ s = ∅ := by
  constructor
  · intro h
    replace h : s.raw.min?.bind ofNat? = none := h
    exact ext (NatSet.min?_eq_none.mp
      (bind_ofNat?_eq_none h fun n hm => s.wf n (NatSet.min?_mem hm)))
  · intro h
    subst h
    show ((∅ : IndexedSet α).raw.min?).bind ofNat? = none
    rw [show (∅ : IndexedSet α).raw.min? = none from NatSet.min?_eq_none.mpr rfl]
    rfl

/-- `max?` answers `none` exactly on the empty set. -/
theorem max?_eq_none {s : IndexedSet α} : s.max? = none ↔ s = ∅ := by
  constructor
  · intro h
    replace h : s.raw.max?.bind ofNat? = none := h
    exact ext (NatSet.max?_eq_none.mp
      (bind_ofNat?_eq_none h fun n hm => s.wf n (NatSet.max?_mem hm)))
  · intro h
    subst h
    show ((∅ : IndexedSet α).raw.max?).bind ofNat? = none
    rw [show (∅ : IndexedSet α).raw.max? = none from NatSet.max?_eq_none.mpr rfl]
    rfl

/-- The successor is a member: a `succ? a = some b` answer is an element of the set. -/
theorem succ?_mem {s : IndexedSet α} {a b : α} (h : s.succ? a = some b) : b ∈ s := by
  replace h : (s.raw.succ? (toNat a)).bind ofNat? = some b := h
  show toNat b ∈ s.raw
  exact NatSet.succ?_mem (bind_ofNat?_eq_some h)

/-- The successor is strictly greater in encoding order. -/
theorem succ?_gt {s : IndexedSet α} {a b : α} (h : s.succ? a = some b) :
    toNat a < toNat b := by
  replace h : (s.raw.succ? (toNat a)).bind ofNat? = some b := h
  exact NatSet.succ?_gt (bind_ofNat?_eq_some h)

/-- The successor is the *least* element above `a` in encoding order. -/
theorem succ?_le {s : IndexedSet α} {a b' b : α} (h : s.succ? a = some b') (hb : b ∈ s)
    (ha : toNat a < toNat b) : toNat b' ≤ toNat b := by
  replace h : (s.raw.succ? (toNat a)).bind ofNat? = some b' := h
  exact NatSet.succ?_le (bind_ofNat?_eq_some h) hb ha

/-- A `none` from `succ?` is complete: no element of the set lies strictly above `a` in encoding
order. (Uses `wf`: the raw answer, were there one, would decode.) -/
theorem le_of_succ?_eq_none {s : IndexedSet α} {a b : α} (h : s.succ? a = none) (hb : b ∈ s) :
    toNat b ≤ toNat a := by
  replace h : (s.raw.succ? (toNat a)).bind ofNat? = none := h
  exact NatSet.le_of_succ?_eq_none
    (bind_ofNat?_eq_none h fun n hm => s.wf n (NatSet.succ?_mem hm)) hb

/-- The predecessor is a member: a `pred? a = some b` answer is an element of the set. -/
theorem pred?_mem {s : IndexedSet α} {a b : α} (h : s.pred? a = some b) : b ∈ s := by
  replace h : (s.raw.pred? (toNat a)).bind ofNat? = some b := h
  show toNat b ∈ s.raw
  exact NatSet.pred?_mem (bind_ofNat?_eq_some h)

/-- The predecessor is strictly less in encoding order. -/
theorem pred?_lt {s : IndexedSet α} {a b : α} (h : s.pred? a = some b) :
    toNat b < toNat a := by
  replace h : (s.raw.pred? (toNat a)).bind ofNat? = some b := h
  exact NatSet.pred?_lt (bind_ofNat?_eq_some h)

/-- The predecessor is the *greatest* element below `a` in encoding order. -/
theorem le_pred? {s : IndexedSet α} {a b' b : α} (h : s.pred? a = some b') (hb : b ∈ s)
    (ha : toNat b < toNat a) : toNat b ≤ toNat b' := by
  replace h : (s.raw.pred? (toNat a)).bind ofNat? = some b' := h
  exact NatSet.le_pred? (bind_ofNat?_eq_some h) hb ha

/-- A `none` from `pred?` is complete: no element of the set lies strictly below `a` in encoding
order. -/
theorem ge_of_pred?_eq_none {s : IndexedSet α} {a b : α} (h : s.pred? a = none) (hb : b ∈ s) :
    toNat a ≤ toNat b := by
  replace h : (s.raw.pred? (toNat a)).bind ofNat? = none := h
  exact NatSet.ge_of_pred?_eq_none
    (bind_ofNat?_eq_none h fun n hm => s.wf n (NatSet.pred?_mem hm)) hb

/-- `succEq?`'s answer is a member. -/
theorem succEq?_mem {s : IndexedSet α} {a b : α} (h : s.succEq? a = some b) : b ∈ s := by
  replace h : (s.raw.succEq? (toNat a)).bind ofNat? = some b := h
  show toNat b ∈ s.raw
  exact NatSet.succEq?_mem (bind_ofNat?_eq_some h)

/-- `succEq?`'s answer is at or above `a` in encoding order. -/
theorem succEq?_ge {s : IndexedSet α} {a b : α} (h : s.succEq? a = some b) :
    toNat a ≤ toNat b := by
  replace h : (s.raw.succEq? (toNat a)).bind ofNat? = some b := h
  exact NatSet.succEq?_ge (bind_ofNat?_eq_some h)

/-- `succEq?` returns the *least* element at or above `a` in encoding order. -/
theorem succEq?_le {s : IndexedSet α} {a b' b : α} (h : s.succEq? a = some b') (hb : b ∈ s)
    (ha : toNat a ≤ toNat b) : toNat b' ≤ toNat b := by
  replace h : (s.raw.succEq? (toNat a)).bind ofNat? = some b' := h
  exact NatSet.succEq?_le (bind_ofNat?_eq_some h) hb ha

/-- A `none` from `succEq?` is complete: every element of the set lies strictly below `a` in
encoding order. -/
theorem lt_of_succEq?_eq_none {s : IndexedSet α} {a b : α} (h : s.succEq? a = none)
    (hb : b ∈ s) : toNat b < toNat a := by
  replace h : (s.raw.succEq? (toNat a)).bind ofNat? = none := h
  exact NatSet.lt_of_succEq?_eq_none
    (bind_ofNat?_eq_none h fun n hm => s.wf n (NatSet.succEq?_mem hm)) hb

/-- `predEq?`'s answer is a member. -/
theorem predEq?_mem {s : IndexedSet α} {a b : α} (h : s.predEq? a = some b) : b ∈ s := by
  replace h : (s.raw.predEq? (toNat a)).bind ofNat? = some b := h
  show toNat b ∈ s.raw
  exact NatSet.predEq?_mem (bind_ofNat?_eq_some h)

/-- `predEq?`'s answer is at or below `a` in encoding order. -/
theorem predEq?_le {s : IndexedSet α} {a b : α} (h : s.predEq? a = some b) :
    toNat b ≤ toNat a := by
  replace h : (s.raw.predEq? (toNat a)).bind ofNat? = some b := h
  exact NatSet.predEq?_le (bind_ofNat?_eq_some h)

/-- `predEq?` returns the *greatest* element at or below `a` in encoding order. -/
theorem le_predEq? {s : IndexedSet α} {a b' b : α} (h : s.predEq? a = some b') (hb : b ∈ s)
    (ha : toNat b ≤ toNat a) : toNat b ≤ toNat b' := by
  replace h : (s.raw.predEq? (toNat a)).bind ofNat? = some b' := h
  exact NatSet.le_predEq? (bind_ofNat?_eq_some h) hb ha

/-- A `none` from `predEq?` is complete: every element of the set lies strictly above `a` in
encoding order. -/
theorem gt_of_predEq?_eq_none {s : IndexedSet α} {a b : α} (h : s.predEq? a = none)
    (hb : b ∈ s) : toNat a < toNat b := by
  replace h : (s.raw.predEq? (toNat a)).bind ofNat? = none := h
  exact NatSet.gt_of_predEq?_eq_none
    (bind_ofNat?_eq_none h fun n hm => s.wf n (NatSet.predEq?_mem hm)) hb

/-- Membership in `split`'s left part: exactly the members strictly below the split element in
encoding order. -/
theorem mem_split_left {s : IndexedSet α} {b a : α} :
    a ∈ (s.split b).1 ↔ a ∈ s ∧ toNat a < toNat b := by
  show toNat a ∈ (s.raw.split (toNat b)).1 ↔ toNat a ∈ s.raw ∧ toNat a < toNat b
  exact NatSet.mem_split_left

/-- Membership in `split`'s right part: exactly the members at or above the split element in
encoding order. -/
theorem mem_split_right {s : IndexedSet α} {b a : α} :
    a ∈ (s.split b).2 ↔ a ∈ s ∧ toNat b ≤ toNat a := by
  show toNat a ∈ (s.raw.split (toNat b)).2 ↔ toNat a ∈ s.raw ∧ toNat b ≤ toNat a
  exact NatSet.mem_split_right

/-- Every member of `split`'s left part lies strictly below the split element in encoding
order. -/
theorem lt_of_mem_split_left {s : IndexedSet α} {b a : α} (h : a ∈ (s.split b).1) :
    toNat a < toNat b :=
  (mem_split_left.mp h).2

/-- Every member of `split`'s right part lies at or above the split element in encoding
order. -/
theorem le_of_mem_split_right {s : IndexedSet α} {b a : α} (h : a ∈ (s.split b).2) :
    toNat b ≤ toNat a :=
  (mem_split_right.mp h).2

/-- Membership in `range`: exactly the members within the inclusive encoding-order window
`[lo, hi]`. -/
theorem mem_range {s : IndexedSet α} {lo hi a : α} :
    a ∈ s.range lo hi ↔ a ∈ s ∧ toNat lo ≤ toNat a ∧ toNat a ≤ toNat hi := by
  show toNat a ∈ s.raw.range (toNat lo) (toNat hi)
      ↔ toNat a ∈ s.raw ∧ toNat lo ≤ toNat a ∧ toNat a ≤ toNat hi
  exact NatSet.mem_range

/-- Membership after `erase`: `a` survives exactly when it was present and is not the erased
element. -/
theorem mem_erase {s : IndexedSet α} {b a : α} : a ∈ s.erase b ↔ a ∈ s ∧ a ≠ b := by
  show toNat a ∈ s.raw.erase (toNat b) ↔ toNat a ∈ s.raw ∧ a ≠ b
  rw [NatSet.mem_erase]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨h1, fun he => h2 (by rw [he])⟩
  · intro ⟨h1, h2⟩
    exact ⟨h1, fun hn => h2 (toNat_inj hn)⟩

/-- Membership after `filter`: `a` survives exactly when it was present and satisfies `p`. -/
theorem mem_filter {s : IndexedSet α} {p : α → Bool} {a : α} :
    a ∈ s.filter p ↔ a ∈ s ∧ p a = true := by
  show toNat a ∈ s.raw.filter (fun n => match ofNat? n with | some a => p a | none => false)
      ↔ toNat a ∈ s.raw ∧ p a = true
  simp only [NatSet.mem_filter, ofNat?_toNat]

/-- Disjointness characterization: `s.isDisjoint t` holds exactly when the two sets share no
element. (The ← direction uses `wf`: a shared raw key would decode to a shared element.) -/
theorem isDisjoint_iff {s t : IndexedSet α} :
    s.isDisjoint t = true ↔ ∀ a : α, a ∈ s → a ∉ t := by
  show s.raw.isDisjoint t.raw = true ↔ _
  rw [NatSet.isDisjoint_iff]
  constructor
  · intro h a ha
    exact h (toNat a) ha
  · intro h n hns hnt
    obtain ⟨a, ha⟩ := s.wf n hns
    subst ha
    exact h a hns hnt

/-- Disjointness is symmetric. -/
theorem isDisjoint_symm {s t : IndexedSet α} (h : s.isDisjoint t = true) :
    t.isDisjoint s = true :=
  NatSet.isDisjoint_symm h

/-- No element of `s` lies in `t` when the two sets are disjoint. -/
theorem not_mem_of_isDisjoint {s t : IndexedSet α} {a : α} (h : s.isDisjoint t = true)
    (ha : a ∈ s) : a ∉ t :=
  isDisjoint_iff.mp h a ha

/-- The empty set is a right identity of difference. -/
theorem diff_empty (s : IndexedSet α) : s \ ∅ = s :=
  ext (NatSet.diff_empty s.raw)

/-- Subtracting a set from itself leaves the empty set. -/
theorem diff_self (s : IndexedSet α) : s \ s = ∅ :=
  ext (NatSet.diff_self s.raw)

/-- Membership in a difference: `a ∈ s \ t` exactly when `a ∈ s` and `a ∉ t`. -/
theorem mem_diff {s t : IndexedSet α} {a : α} : a ∈ s \ t ↔ a ∈ s ∧ a ∉ t := by
  show toNat a ∈ s.raw \ t.raw ↔ toNat a ∈ s.raw ∧ ¬(toNat a ∈ t.raw)
  exact NatSet.mem_diff

/-- **Difference detects the subset order**: `s \ t` is empty exactly when `s ⊆ t`. -/
theorem diff_eq_empty_iff_subset {s t : IndexedSet α} : s \ t = ∅ ↔ s ⊆ t := by
  constructor
  · intro h
    have hr : s.raw \ t.raw = ∅ := congrArg IndexedSet.raw h
    exact NatSet.diff_eq_empty_iff_subset.mp hr
  · intro h
    exact ext (NatSet.diff_eq_empty_iff_subset.mpr h)

/-- Subtracting a superset leaves the empty set. -/
theorem diff_eq_empty_of_subset {s t : IndexedSet α} (h : s ⊆ t) : s \ t = ∅ :=
  diff_eq_empty_iff_subset.mpr h

/-- The empty set is a right identity of symmetric difference. -/
theorem symmDiff_empty (s : IndexedSet α) : s.symmDiff ∅ = s :=
  ext (NatSet.symmDiff_empty s.raw)

/-- The empty set is a left identity of symmetric difference. -/
theorem empty_symmDiff (s : IndexedSet α) : (∅ : IndexedSet α).symmDiff s = s :=
  ext (NatSet.empty_symmDiff s.raw)

/-- A set cancels against itself: its symmetric difference with itself is empty. -/
theorem symmDiff_self (s : IndexedSet α) : s.symmDiff s = ∅ :=
  ext (NatSet.symmDiff_self s.raw)

/-- Symmetric difference is commutative. -/
theorem symmDiff_comm (s t : IndexedSet α) : s.symmDiff t = t.symmDiff s :=
  ext (NatSet.symmDiff_comm s.raw t.raw)

/-- Membership in a symmetric difference: `a ∈ s.symmDiff t` exactly when `a` is in exactly one
of the two sets. -/
theorem mem_symmDiff {s t : IndexedSet α} {a : α} :
    a ∈ s.symmDiff t ↔ (a ∈ s ∧ a ∉ t) ∨ (a ∉ s ∧ a ∈ t) := by
  show toNat a ∈ s.raw.symmDiff t.raw
      ↔ (toNat a ∈ s.raw ∧ ¬(toNat a ∈ t.raw)) ∨ (¬(toNat a ∈ s.raw) ∧ toNat a ∈ t.raw)
  exact NatSet.mem_symmDiff

/-- **Symmetric difference detects equality**: `s.symmDiff t` is empty exactly when `s = t`. -/
theorem symmDiff_eq_empty_iff {s t : IndexedSet α} : s.symmDiff t = ∅ ↔ s = t := by
  constructor
  · intro h
    have hr : s.raw.symmDiff t.raw = ∅ := congrArg IndexedSet.raw h
    exact ext (NatSet.symmDiff_eq_empty_iff.mp hr)
  · intro h
    subst h
    exact symmDiff_self s

/-- The symmetric difference is the union of the two one-sided differences. -/
theorem symmDiff_eq_union_diff (s t : IndexedSet α) : s.symmDiff t = (s \ t) ∪ (t \ s) :=
  ext (NatSet.symmDiff_eq_union_diff s.raw t.raw)

/-- A subset's symmetric difference is the reverse difference: when `s ⊆ t`, all of `s` cancels
and exactly `t \ s` remains. -/
theorem symmDiff_eq_diff_of_subset {s t : IndexedSet α} (h : s ⊆ t) : s.symmDiff t = t \ s :=
  ext (NatSet.symmDiff_eq_diff_of_subset h)

/-- Symmetric difference is an involution in its second operand. -/
theorem symmDiff_symmDiff_cancel (s t : IndexedSet α) : (s.symmDiff t).symmDiff t = s :=
  ext (NatSet.symmDiff_symmDiff_cancel s.raw t.raw)

/-- Symmetric difference is associative. -/
theorem symmDiff_assoc (s t u : IndexedSet α) :
    (s.symmDiff t).symmDiff u = s.symmDiff (t.symmDiff u) :=
  ext (NatSet.symmDiff_assoc s.raw t.raw u.raw)

/-- `popMin?` pops the minimum: the popped element is `min?`'s answer. -/
theorem popMin?_min {s : IndexedSet α} {a : α} {s' : IndexedSet α}
    (h : s.popMin? = some (a, s')) : s.min? = some a := by
  unfold popMin? at h
  cases hm : s.min? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some b =>
    rw [hm] at h
    replace h : some (b, s.erase b) = some (a, s') := h
    injection h with h
    injection h with h1 h2
    rw [h1]

/-- `popMin?`'s rest is the set with the popped element erased. -/
theorem popMin?_erase {s : IndexedSet α} {a : α} {s' : IndexedSet α}
    (h : s.popMin? = some (a, s')) : s' = s.erase a := by
  unfold popMin? at h
  cases hm : s.min? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some b =>
    rw [hm] at h
    replace h : some (b, s.erase b) = some (a, s') := h
    injection h with h
    injection h with h1 h2
    rw [← h2, h1]

/-- The membership view of `popMin?`'s rest: the popped minimum is gone, everything else
survives. -/
theorem popMin?_mem {s : IndexedSet α} {a : α} {s' : IndexedSet α}
    (h : s.popMin? = some (a, s')) (b : α) : b ∈ s' ↔ b ∈ s ∧ b ≠ a := by
  rw [popMin?_erase h]
  exact mem_erase

/-- `popMin?` answers `none` exactly on the empty set (totality: a non-empty set always pops). -/
theorem popMin?_eq_none {s : IndexedSet α} : s.popMin? = none ↔ s = ∅ := by
  constructor
  · intro h
    unfold popMin? at h
    cases hm : s.min? with
    | none => exact min?_eq_none.mp hm
    | some a => rw [hm] at h; exact absurd h (by simp)
  · intro h
    unfold popMin?
    rw [min?_eq_none.mpr h]

/-- `popMax?` pops the maximum: the popped element is `max?`'s answer. -/
theorem popMax?_max {s : IndexedSet α} {a : α} {s' : IndexedSet α}
    (h : s.popMax? = some (a, s')) : s.max? = some a := by
  unfold popMax? at h
  cases hm : s.max? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some b =>
    rw [hm] at h
    replace h : some (b, s.erase b) = some (a, s') := h
    injection h with h
    injection h with h1 h2
    rw [h1]

/-- `popMax?`'s rest is the set with the popped element erased. -/
theorem popMax?_erase {s : IndexedSet α} {a : α} {s' : IndexedSet α}
    (h : s.popMax? = some (a, s')) : s' = s.erase a := by
  unfold popMax? at h
  cases hm : s.max? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some b =>
    rw [hm] at h
    replace h : some (b, s.erase b) = some (a, s') := h
    injection h with h
    injection h with h1 h2
    rw [← h2, h1]

/-- The membership view of `popMax?`'s rest: the popped maximum is gone, everything else
survives. -/
theorem popMax?_mem {s : IndexedSet α} {a : α} {s' : IndexedSet α}
    (h : s.popMax? = some (a, s')) (b : α) : b ∈ s' ↔ b ∈ s ∧ b ≠ a := by
  rw [popMax?_erase h]
  exact mem_erase

/-- `popMax?` answers `none` exactly on the empty set. -/
theorem popMax?_eq_none {s : IndexedSet α} : s.popMax? = none ↔ s = ∅ := by
  constructor
  · intro h
    unfold popMax? at h
    cases hm : s.max? with
    | none => exact max?_eq_none.mp hm
    | some a => rw [hm] at h; exact absurd h (by simp)
  · intro h
    unfold popMax?
    rw [max?_eq_none.mpr h]

end IndexedSet

end NatCol
