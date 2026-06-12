import NatCol.PTree

/-!
# `NatCollection`: the generic top-level API

A `NatCollection` wraps a path-compressed trie (`PTree`) together with a proof that it is
well-formed (`PTree.WF` — canonical: no `nil` children, no empty leaves, path-compression
minimal). All operations are generic over `[LeafOps L V]`; `NatMap`/`NatSet` are thin
instantiations.

## Canonical form

`PTree.WF` is exactly the canonical-shape invariant, so structural equality (`PTree.beq`)
coincides with logical equality (`PTree.eq_of_beq`/`beq_refl`). Every operation here returns a
well-formed trie, so the invariant holds throughout — which is what makes the `BEq` instance
lawful.

## Denotational seams

The whole lattice/order/functor suite routes through the `get?_*` seams (`get?_empty`,
`get?_insert`, `get?_join`, `get?_meet`, `get?_restricts`) and `ext_get?`, each a one-line lift of
its `PTree` counterpart across the `tree`/`wf` projections.
-/

namespace NatCol
----------------------------------------------------------------------------------------------------
-- Implementation
----------------------------------------------------------------------------------------------------

/-- A well-formed path-compressed trie. `PTree.WF` is the canonical-shape invariant `contains`
relies on (no `nil` children, no empty leaves, path-compression minimal); every operation below
returns a `NatCollection`, so the invariant holds throughout. That is what makes structural
equality (`PTree.beq`) coincide with logical equality. -/
structure NatCollection (L : Type u) {V : Type u} [LeafOps L V] where
  tree : PTree L
  wf : PTree.WF tree

namespace NatCollection

variable {L : Type u} {V : Type u} [LeafOps L V]

/-- Two collections with equal trees are equal — the `WF` proof is irrelevant (a `Prop`). This is
the structural counterpart of `ext_get?`, used to lift every `PTree` equation that is already
stated as a tree identity. -/
theorem ext_tree (c₁ c₂ : NatCollection L) (h : c₁.tree = c₂.tree) : c₁ = c₂ := by
  obtain ⟨t₁, w₁⟩ := c₁
  obtain ⟨t₂, w₂⟩ := c₂
  subst h; rfl

/-- The empty collection. -/
def empty : NatCollection L := ⟨.nil, PTree.WF_empty⟩

@[specialize] def isEmpty (c : NatCollection L) : Bool := PTree.isNil c.tree

@[specialize] def size (c : NatCollection L) : Nat := PTree.size c.tree

/-- Look up the value at key `k`. -/
@[specialize] def get? (c : NatCollection L) (k : Nat) : Option V := PTree.get? k c.tree

/-- Is key `k` present? Routes through the boxing-free `PTree.contains` rather than
`(get? k).isSome`; `contains_eq` proves the two agree. -/
@[specialize] def contains (c : NatCollection L) (k : Nat) : Bool := PTree.contains k c.tree

/-- Insert / overwrite key `k` ↦ `v`. -/
@[specialize] def insert (c : NatCollection L) (k : Nat) (v : V) : NatCollection L :=
  ⟨PTree.insert k v c.tree, PTree.WF_insert k v c.tree c.wf⟩

/-- Union. Leaf values at coinciding keys are combined with `combine`. -/
@[specialize] def join (combine : V → V → V) (a b : NatCollection L) : NatCollection L :=
  ⟨PTree.union combine a.tree b.tree, PTree.WF_union combine a.tree b.tree a.wf b.wf⟩

/-- Intersection. Leaf values at coinciding keys are combined with `combine`. -/
@[specialize] def meet (combine : V → V → V) (a b : NatCollection L) : NatCollection L :=
  ⟨PTree.meet combine a.tree b.tree, PTree.WF_meet combine a.tree b.tree a.wf b.wf⟩

/-- `a` restricts `b`: `a`'s keys are a subset of `b`'s, and `rel` holds on every value at a
coinciding key. -/
@[specialize] def restricts (rel : V → V → Bool) (a b : NatCollection L) : Bool :=
  PTree.subset rel a.tree b.tree

/-- Whether `a` and `b` share no key — the intersection's structural walk without the
intersection: prefix-disjoint subtrees answer in O(1), aligned leaves compare occupancy masks
with one `AND`, and the first shared key short-circuits the rest. Never allocates. -/
@[specialize] def isDisjoint (a b : NatCollection L) : Bool :=
  PTree.isDisjoint a.tree b.tree

/-- Difference: the `(key, value)` pairs of `a` whose key is absent from `b` (`b`'s values are
irrelevant; surviving values are untouched). A structural merge — subtrees of `a` that cannot
meet `b` are kept whole (and shared), never rebuilt or probed per key. -/
@[specialize] def diff (a b : NatCollection L) : NatCollection L :=
  ⟨PTree.diff a.tree b.tree, PTree.WF_diff a.tree b.tree a.wf b.wf⟩

/-- Symmetric difference: the `(key, value)` pairs whose key is in exactly one of `a`, `b`
(shared keys cancel, equal subtrees cancel entirely and the surrounding branch re-compresses).
One-sided subtrees are carried over whole (shared). -/
@[specialize] def symmDiff (a b : NatCollection L) : NatCollection L :=
  ⟨PTree.symmDiff a.tree b.tree, PTree.WF_symmDiff a.tree b.tree a.wf b.wf⟩

/-- Keep the entries with key `< k` — a structural prune: subtrees wholly below the bound are
kept whole (shared), wholly above are dropped in O(1); only the bound's routed path is rebuilt. -/
@[specialize] def filterLt (c : NatCollection L) (k : Nat) : NatCollection L :=
  ⟨PTree.filterLt k c.tree, PTree.WF_filterLt k c.tree c.wf⟩

/-- Keep the entries with key `≥ k` — the mirror prune of `filterLt`. -/
@[specialize] def filterGE (c : NatCollection L) (k : Nat) : NatCollection L :=
  ⟨PTree.filterGE k c.tree, PTree.WF_filterGE k c.tree c.wf⟩

/-- Split at `k`: `(entries with key < k, entries with key ≥ k)` — two structural prunes along
`k`'s routed path; both parts are canonical and share every off-path subtree with the input. -/
@[specialize] def split (c : NatCollection L) (k : Nat) : NatCollection L × NatCollection L :=
  (c.filterLt k, c.filterGE k)

/-- The entries with key in the inclusive range `[lo, hi]` — a double structural prune. -/
@[specialize] def range (c : NatCollection L) (lo hi : Nat) : NatCollection L :=
  (c.filterGE lo).filterLt (hi + 1)

/-- All `(key, value)` pairs, ascending by key. -/
@[specialize] def toList (c : NatCollection L) : List (Nat × V) := (PTree.toArray c.tree).toList

/-- Build a collection from `(key, value)` pairs (later pairs win on duplicate keys). -/
@[specialize] def ofList (l : List (Nat × V)) : NatCollection L :=
  ⟨PTree.ofList l, PTree.WF_ofList l⟩

/-- Fold `f` over all present `(key, value)` pairs, ascending by key, starting from `init`.
Walks the trie directly (`PTree.foldl`) — no intermediate list. -/
@[specialize] def fold {β : Type w} (f : β → Nat → V → β) (init : β) (c : NatCollection L) : β :=
  PTree.foldl f init c.tree

/-- Monadic fold over all present `(key, value)` pairs, ascending by key, starting from `init`. -/
@[specialize] def foldM {β : Type w} {m : Type w → Type w'} [Monad m] (f : β → Nat → V → m β)
    (init : β) (c : NatCollection L) : m β :=
  PTree.foldlM f init c.tree

/-- Whether every present `(key, value)` pair satisfies `p`, short-circuiting at the first
failure (the walk past the failing subtree is skipped, not just the predicate). -/
@[specialize] def all (p : Nat → V → Bool) (c : NatCollection L) : Bool :=
  PTree.all p c.tree

/-- Whether some present `(key, value)` pair satisfies `p`, short-circuiting at the first
success. -/
@[specialize] def any (p : Nat → V → Bool) (c : NatCollection L) : Bool :=
  PTree.any p c.tree

/-- Monadic `all`: whether every present `(key, value)` pair satisfies the monadic predicate `p`,
threading effects in ascending key order and skipping `p` once a failure is seen. -/
@[specialize] def allM {m : Type → Type w} [Monad m] (p : Nat → V → m Bool)
    (c : NatCollection L) : m Bool :=
  PTree.allM p c.tree

/-- Monadic `any`: whether some present `(key, value)` pair satisfies `p`, skipping `p` once a
success is seen. -/
@[specialize] def anyM {m : Type → Type w} [Monad m] (p : Nat → V → m Bool)
    (c : NatCollection L) : m Bool :=
  PTree.anyM p c.tree

/-- Keep only the `(key, value)` pairs satisfying `p` — one structural pass: each leaf is filtered
in place, emptied leaves are pruned, and thinned branches re-compressed (`PTree.WF_filter`), so the
result is canonical and equals the collection built directly from the survivors. -/
@[specialize] def filter (p : Nat → V → Bool) (c : NatCollection L) : NatCollection L :=
  ⟨PTree.filter p c.tree, PTree.WF_filter p c.tree c.wf⟩

/-- Split by `p`: the first component keeps the `(key, value)` pairs satisfying `p`, the second
the rest. Two structural `filter` passes, so both parts are canonical. -/
@[specialize] def partition (p : Nat → V → Bool) (c : NatCollection L) :
    NatCollection L × NatCollection L :=
  (c.filter p, c.filter (fun k v => !(p k v)))

/-- Erase key `k` — descends just the routed path and re-compresses the touched branch
(`PTree.WF_erase`), so the result is canonical; erasing an absent key is a no-op. -/
@[specialize] def erase (c : NatCollection L) (k : Nat) : NatCollection L :=
  ⟨PTree.erase k c.tree, PTree.WF_erase k c.tree c.wf⟩

/-- Apply `f` to the value at key `k`, if present. -/
def modify (c : NatCollection L) (k : Nat) (f : V → V) : NatCollection L :=
  match c.get? k with
  | none => c
  | some v => c.insert k (f v)

/-- Rewrite the entry at key `k` through `f`: `f` receives the current value (`some v` if present,
`none` if absent) and returns the value to store, or `none` to leave the key absent. Generalizes
`insert` (`fun _ => some v`), `erase` (`fun _ => none`), and `modify`. -/
def alter (c : NatCollection L) (k : Nat) (f : Option V → Option V) : NatCollection L :=
  match f (c.get? k) with
  | some v => c.insert k v
  | none => c.erase k

-- Ordered queries — delegations of the `PTree` descents (`Option`-returning, so no canonical-shape
-- obligations), plus the inclusive and pop variants derived at this layer.

/-- The least `(key, value)` pair, `none` on the empty collection. O(depth). -/
@[specialize] def minEntry? (c : NatCollection L) : Option (Nat × V) := PTree.minEntry? c.tree

/-- The greatest `(key, value)` pair, `none` on the empty collection. O(depth). -/
@[specialize] def maxEntry? (c : NatCollection L) : Option (Nat × V) := PTree.maxEntry? c.tree

/-- The least key, `none` on the empty collection. O(depth). -/
@[specialize] def minKey? (c : NatCollection L) : Option Nat := c.minEntry?.map Prod.fst

/-- The greatest key, `none` on the empty collection. O(depth). -/
@[specialize] def maxKey? (c : NatCollection L) : Option Nat := c.maxEntry?.map Prod.fst

/-- The least entry whose key is strictly greater than `k` (the successor query), `none` if there
is none. O(depth). -/
@[specialize] def entryGT? (c : NatCollection L) (k : Nat) : Option (Nat × V) :=
  PTree.entryGT? k c.tree

/-- The greatest entry whose key is strictly less than `k` (the predecessor query), `none` if
there is none. O(depth). -/
@[specialize] def entryLT? (c : NatCollection L) (k : Nat) : Option (Nat × V) :=
  PTree.entryLT? k c.tree

/-- The least entry with key `≥ k`: the entry at `k` itself when present, else the successor. -/
@[specialize] def entryGE? (c : NatCollection L) (k : Nat) : Option (Nat × V) :=
  match c.get? k with
  | some v => some (k, v)
  | none   => c.entryGT? k

/-- The greatest entry with key `≤ k`: the entry at `k` itself when present, else the
predecessor. -/
@[specialize] def entryLE? (c : NatCollection L) (k : Nat) : Option (Nat × V) :=
  match c.get? k with
  | some v => some (k, v)
  | none   => c.entryLT? k

/-- The least entry together with the collection without it, `none` on the empty collection. Two
O(depth) walks (`minEntry?` then `erase`), which keeps the canonical-shape proof `erase`'s. -/
@[specialize] def popMinEntry? (c : NatCollection L) : Option ((Nat × V) × NatCollection L) :=
  match c.minEntry? with
  | none   => none
  | some e => some (e, c.erase e.1)

/-- The greatest entry together with the collection without it, `none` on the empty collection. -/
@[specialize] def popMaxEntry? (c : NatCollection L) : Option ((Nat × V) × NatCollection L) :=
  match c.maxEntry? with
  | none   => none
  | some e => some (e, c.erase e.1)

/-- Monadic `filter`: keep the pairs for which `p` returns `true`, running `p` on every pair in
ascending key order and threading its effects through `m`; the result is rebuilt from the
survivors, so it is canonical and equals the pure `filter` when `p` is effect-free. Restricted to
`Type`-valued leaves, as `List.filterM` is. -/
def filterM {L V : Type} [LeafOps L V] {m : Type → Type w} [Monad m] (p : Nat → V → m Bool)
    (c : NatCollection L) : m (NatCollection L) := do
  let survivors ← c.toList.filterM (fun kv => p kv.1 kv.2)
  pure (ofList survivors)

/-- Structural equality of the underlying tries. Canonical ⇒ logical equality. -/
def beq [BEq L] (a b : NatCollection L) : Bool := PTree.beq a.tree b.tree

instance [BEq L] : BEq (NatCollection L) := ⟨beq⟩

/-- Hash a collection by its `(key, value)` list. The list is derived structurally (sorted,
canonical), so `BEq`-equal collections hash equally. -/
instance [Hashable V] : Hashable (NatCollection L) := ⟨fun c => hash c.toList⟩

/-- `beq` decides propositional equality, so the structural `BEq` is lawful. -/
instance [BEq L] [LawfulBEq L] : LawfulBEq (NatCollection L) where
  eq_of_beq {a b} hb := ext_tree a b (PTree.eq_of_beq (show PTree.beq a.tree b.tree = true from hb))
  rfl {a} := PTree.beq_refl a.tree

/-- Decidable propositional equality, built from the lawful `BEq`. -/
instance [BEq L] [LawfulBEq L] : DecidableEq (NatCollection L) := _root_.instDecidableEqOfLawfulBEq

----------------------------------------------------------------------------------------------------
-- Theorems
----------------------------------------------------------------------------------------------------

/-! ### Denotational seams

Each lifts its `PTree` counterpart across the `tree`/`wf` projections. -/

/-- `contains` agrees with `(get? k).isSome`. -/
theorem contains_eq (c : NatCollection L) (k : Nat) : c.contains k = (c.get? k).isSome :=
  PTree.contains_eq_isSome k c.tree

/-- The empty collection reads `none` everywhere. -/
@[simp] theorem get?_empty (k : Nat) : (empty : NatCollection L).get? k = none := PTree.get?_nil k

/-- The empty collection is recognized as empty. -/
@[simp, grind =]
theorem isEmpty_empty : (empty : NatCollection L).isEmpty = true := rfl

/-- An empty collection *is* `empty` — `PTree.WF` forces the only empty trie to be `nil`. -/
theorem eq_empty_of_isEmpty (c : NatCollection L) (hc : c.isEmpty = true) : c = empty := by
  apply ext_tree
  show c.tree = PTree.nil
  have h : PTree.isNil c.tree = true := hc
  cases hct : c.tree with
  | nil => rfl
  | tip _ _ => rw [hct] at h; simp [PTree.isNil] at h
  | bin _ _ _ _ => rw [hct] at h; simp [PTree.isNil] at h

/-- An empty collection reads `none` everywhere. -/
theorem get?_eq_none_of_isEmpty (c : NatCollection L) (hc : c.isEmpty = true) (k : Nat) :
    c.get? k = none := by
  rw [eq_empty_of_isEmpty c hc]; exact get?_empty k

/-- A non-empty collection has a present key. -/
theorem exists_get?_of_ne_empty (c : NatCollection L) (hc : c.isEmpty = false) :
    ∃ k, (c.get? k).isSome := by
  have hne : c.tree ≠ .nil := by
    intro h
    simp only [isEmpty] at hc
    rw [h] at hc
    simp [PTree.isNil] at hc
  obtain ⟨j, hj⟩ := PTree.exists_mem c.tree c.wf hne
  exact ⟨j, by
    show (PTree.get? j c.tree).isSome = true
    rw [← PTree.contains_eq_isSome]; exact hj⟩

/-- **`get?` of a `meet`**: the value-level intersection of the two lookups. -/
theorem get?_meet (combine : V → V → V) (a b : NatCollection L) (k : Nat) :
    (meet combine a b).get? k = optVmeet combine (a.get? k) (b.get? k) :=
  PTree.get?_meet combine k a.tree b.tree a.wf b.wf

/-- **`get?` of a `join`**: the value-level union of the two lookups. -/
theorem get?_join (combine : V → V → V) (a b : NatCollection L) (k : Nat) :
    (join combine a b).get? k = optVjoin combine (a.get? k) (b.get? k) :=
  PTree.get?_union combine k a.tree b.tree a.wf b.wf

/-- **`get?` of an `insert`**: the inserted key reads the new value; every other key is read
unchanged. -/
theorem get?_insert (c : NatCollection L) (k : Nat) (v : V) (j : Nat) :
    (c.insert k v).get? j = if j = k then some v else c.get? j := by
  show PTree.get? j (PTree.insert k v c.tree) = if j = k then some v else PTree.get? j c.tree
  rw [PTree.get?_insert k j v c.tree c.wf]
  by_cases hjk : j = k
  · rw [if_pos hjk, if_pos (show (j == k) = true by rw [hjk]; exact beq_self_eq_true k)]
  · rw [if_neg hjk, if_neg (show ¬ (j == k) = true by rw [beq_iff_eq]; exact hjk)]

/-- **Collection extensionality**: two well-formed collections agreeing on every `get?` are equal
(`PTree.ext_get?` recovers the tree; `ext_tree` drops the `WF` proof). -/
theorem ext_get? (c₁ c₂ : NatCollection L) (h : ∀ k, c₁.get? k = c₂.get? k) : c₁ = c₂ := by
  apply ext_tree
  exact PTree.ext_get? c₁.tree c₂.tree c₁.wf c₂.wf (fun j => h j)

/-! ### Lattice laws -/

/-- The empty collection is a left identity of `join`. -/
@[simp, grind =]
theorem join_empty_left (combine : V → V → V) (b : NatCollection L) :
    join combine empty b = b := by
  apply ext_tree; exact PTree.empty_union combine b.tree b.wf

/-- The empty collection is a right identity of `join`. -/
@[simp, grind =]
theorem join_empty_right (combine : V → V → V) (a : NatCollection L) :
    join combine a empty = a := by
  apply ext_tree; exact PTree.union_empty combine a.tree a.wf

/-- The empty collection is a left annihilator of `meet`. -/
@[simp, grind =]
theorem meet_empty_left (combine : V → V → V) (b : NatCollection L) :
    meet combine empty b = empty := by
  apply ext_tree; exact PTree.empty_meet combine b.tree b.wf

/-- The empty collection is a right annihilator of `meet`. -/
@[simp, grind =]
theorem meet_empty_right (combine : V → V → V) (a : NatCollection L) :
    meet combine a empty = empty := by
  apply ext_tree; exact PTree.meet_empty combine a.tree a.wf

/-- The empty collection restricts every collection. -/
@[simp, grind =]
theorem restricts_empty_left (rel : V → V → Bool) (b : NatCollection L) :
    restricts rel empty b = true := by
  show PTree.subset rel .nil b.tree = true
  simp [PTree.subset, PTree.subsetU]

/-- `restricts` is reflexive when `rel` is reflexive on values. -/
theorem restricts_refl (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (a : NatCollection L) :
    restricts rel a a = true :=
  PTree.subset_refl rel hrefl a.tree a.wf

/-- `join` commutes when the combine is flipped. Read both sides off `get?` (`get?_join`) — they
are flipped `optVjoin`s — and conclude by collection extensionality. -/
theorem join_comm (combine : V → V → V) (a b : NatCollection L) :
    join combine a b = join (fun x y => combine y x) b a := by
  apply ext_get?
  intro k
  rw [get?_join combine a b k, get?_join (fun x y => combine y x) b a k]
  exact (optVjoin_flip combine (a.get? k) (b.get? k)).symm

/-- `meet` commutes when the combine is flipped. -/
theorem meet_comm (combine : V → V → V) (a b : NatCollection L) :
    meet combine a b = meet (fun x y => combine y x) b a := by
  apply ext_get?
  intro k
  rw [get?_meet combine a b k, get?_meet (fun x y => combine y x) b a k]
  exact (optVmeet_flip combine (a.get? k) (b.get? k)).symm

/-- **Associativity of `join`** for an associative `combine`. -/
theorem join_assoc (combine : V → V → V)
    (hassoc : ∀ x y z, combine (combine x y) z = combine x (combine y z))
    (a b e : NatCollection L) :
    join combine (join combine a b) e = join combine a (join combine b e) := by
  apply ext_tree
  exact PTree.union_assoc combine hassoc a.tree b.tree e.tree a.wf b.wf e.wf

/-- **Associativity of `meet`** for an associative `combine`. -/
theorem meet_assoc (combine : V → V → V)
    (hassoc : ∀ x y z, combine (combine x y) z = combine x (combine y z))
    (a b e : NatCollection L) :
    meet combine (meet combine a b) e = meet combine a (meet combine b e) := by
  apply ext_tree
  exact PTree.meet_assoc combine hassoc a.tree b.tree e.tree a.wf b.wf e.wf

/-! ### Order laws -/

/-- **`get?` characterization of `restricts`** (for reflexive `rel`): `a` restricts `b` exactly
when `optRel rel` relates their lookups at every key. -/
theorem get?_restricts (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (a b : NatCollection L) :
    restricts rel a b = true ↔ ∀ k, optRel rel (a.get? k) (b.get? k) = true :=
  PTree.subset_iff_eq rel hrefl a.tree b.tree a.wf b.wf

/-- **`restricts` is transitive** when `rel` is a preorder. -/
theorem restricts_trans (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (htrans : ∀ x y z, rel x y = true → rel y z = true → rel x z = true)
    (a b c : NatCollection L) :
    restricts rel a b = true → restricts rel b c = true → restricts rel a c = true :=
  fun hab hbc => PTree.subset_trans rel hrefl htrans a.tree b.tree c.tree a.wf b.wf c.wf hab hbc

/-- **`restricts` is anti-symmetric** when `rel` is reflexive and anti-symmetric. -/
theorem restricts_antisymm (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (hantisymm : ∀ x y, rel x y = true → rel y x = true → x = y)
    (a b : NatCollection L) :
    restricts rel a b = true → restricts rel b a = true → a = b :=
  fun hab hba => ext_tree a b (PTree.subset_antisymm rel hrefl hantisymm a.tree b.tree a.wf b.wf hab hba)

/-- **`meet` is a lower bound on the left**: `meet combine a b` restricts `a`, provided the combine
yields a `rel`-smaller value than its left argument. -/
theorem meet_restricts_left (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (combine : V → V → V) (hle : ∀ x y, rel (combine x y) x = true) (a b : NatCollection L) :
    restricts rel (meet combine a b) a = true :=
  PTree.meet_subset_left rel hrefl combine hle a.tree b.tree a.wf b.wf

/-- **`meet` is a lower bound on the right**: symmetric to `meet_restricts_left`. -/
theorem meet_restricts_right (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (combine : V → V → V) (hle : ∀ x y, rel (combine x y) y = true) (a b : NatCollection L) :
    restricts rel (meet combine a b) b = true :=
  PTree.meet_subset_right rel hrefl combine hle a.tree b.tree a.wf b.wf

/-- **`meet` is the greatest lower bound**: any `m` that restricts both `a` and `b` also restricts
their `meet`, provided the combine is a greatest lower bound for `rel`. -/
theorem meet_glb (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (combine : V → V → V)
    (hglb : ∀ w x y, rel w x = true → rel w y = true → rel w (combine x y) = true)
    (m a b : NatCollection L)
    (hma : restricts rel m a = true) (hmb : restricts rel m b = true) :
    restricts rel m (meet combine a b) = true :=
  PTree.subset_meet rel hrefl combine hglb a.tree b.tree m.tree a.wf b.wf m.wf hma hmb

/-- **`join` is an upper bound on the left**: `a` restricts `join combine a b`, provided the combine
yields a `rel`-greater value than its left argument. -/
theorem restricts_join_left (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (combine : V → V → V) (hle : ∀ x y, rel x (combine x y) = true) (a b : NatCollection L) :
    restricts rel a (join combine a b) = true :=
  PTree.subset_union_left rel hrefl combine hle a.tree b.tree a.wf b.wf

/-- **`join` is an upper bound on the right**: symmetric to `restricts_join_left`. -/
theorem restricts_join_right (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true)
    (combine : V → V → V) (hre : ∀ x y, rel y (combine x y) = true) (a b : NatCollection L) :
    restricts rel b (join combine a b) = true :=
  PTree.subset_union_right rel hrefl combine hre a.tree b.tree a.wf b.wf

/-- **`join` is the least upper bound**: if both `a` and `b` restrict `m`, so does their `join`,
provided the combine is a least upper bound for `rel`. -/
theorem join_lub (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (combine : V → V → V)
    (hlub : ∀ x y w, rel x w = true → rel y w = true → rel (combine x y) w = true)
    (a b m : NatCollection L)
    (ham : restricts rel a m = true) (hbm : restricts rel b m = true) :
    restricts rel (join combine a b) m = true :=
  PTree.union_subset rel hrefl combine hlub a.tree b.tree m.tree a.wf b.wf m.wf ham hbm

/-- **`meet` distributes over `join`** (left distributivity). -/
theorem meet_join_distrib (combineMeet combineJoin : V → V → V)
    (hdist : ∀ x y z,
      combineMeet x (combineJoin y z) = combineJoin (combineMeet x y) (combineMeet x z))
    (a b e : NatCollection L) :
    meet combineMeet a (join combineJoin b e)
      = join combineJoin (meet combineMeet a b) (meet combineMeet a e) := by
  apply ext_tree
  exact PTree.meet_union_distrib combineMeet combineJoin hdist a.tree b.tree e.tree a.wf b.wf e.wf

/-- **`join` distributes over `meet`** (left distributivity), given the full lattice algebra on the
combines. -/
theorem join_meet_distrib (combineJoin combineMeet : V → V → V)
    (hidem : ∀ x, combineMeet x x = x)
    (habs1 : ∀ x y, combineMeet (combineJoin x y) x = x)
    (habs2 : ∀ x y, combineMeet x (combineJoin x y) = x)
    (hdist : ∀ x y z,
      combineJoin x (combineMeet y z) = combineMeet (combineJoin x y) (combineJoin x z))
    (a b e : NatCollection L) :
    join combineJoin a (meet combineMeet b e)
      = meet combineMeet (join combineJoin a b) (join combineJoin a e) := by
  apply ext_tree
  exact PTree.union_meet_distrib combineJoin combineMeet hidem habs1 habs2 hdist
    a.tree b.tree e.tree a.wf b.wf e.wf

/-! ### Ordered queries

The `minEntry?`/`maxEntry?` denotations, lifted from `PTree` (the bundled `wf` proof discharges
the well-formedness hypotheses): the returned entry is real, and its key bounds every present
key. The `minKey?`/`maxKey?` corollaries are what `NatSet.min?`/`max?` re-export. -/

/-- The entry `minEntry?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_minEntry? (c : NatCollection L) (k : Nat) (v : V)
    (h : c.minEntry? = some (k, v)) : c.get? k = some v :=
  PTree.get?_of_minEntry? c.tree c.wf k v h

/-- The entry `maxEntry?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_maxEntry? (c : NatCollection L) (k : Nat) (v : V)
    (h : c.maxEntry? = some (k, v)) : c.get? k = some v :=
  PTree.get?_of_maxEntry? c.tree c.wf k v h

/-- `minEntry?`'s key is a lower bound on every present key. -/
theorem minEntry?_le (c : NatCollection L) (k : Nat) (v : V) (j : Nat)
    (h : c.minEntry? = some (k, v)) (hj : c.contains j = true) : k ≤ j :=
  PTree.minEntry?_le c.tree c.wf k v j h hj

/-- `maxEntry?`'s key is an upper bound on every present key. -/
theorem le_maxEntry? (c : NatCollection L) (k : Nat) (v : V) (j : Nat)
    (h : c.maxEntry? = some (k, v)) (hj : c.contains j = true) : j ≤ k :=
  PTree.le_maxEntry? c.tree c.wf k v j h hj

/-- The key `minKey?` returns is present. -/
theorem contains_of_minKey? (c : NatCollection L) (k : Nat) (h : c.minKey? = some k) :
    c.contains k = true := by
  replace h : c.minEntry?.map Prod.fst = some k := h
  obtain ⟨⟨k', v⟩, hmin, hfst⟩ := Option.map_eq_some_iff.mp h
  have hk : k' = k := hfst
  subst hk
  rw [contains_eq, get?_of_minEntry? c k' v hmin]
  rfl

/-- The key `maxKey?` returns is present. -/
theorem contains_of_maxKey? (c : NatCollection L) (k : Nat) (h : c.maxKey? = some k) :
    c.contains k = true := by
  replace h : c.maxEntry?.map Prod.fst = some k := h
  obtain ⟨⟨k', v⟩, hmax, hfst⟩ := Option.map_eq_some_iff.mp h
  have hk : k' = k := hfst
  subst hk
  rw [contains_eq, get?_of_maxEntry? c k' v hmax]
  rfl

/-- `minKey?`'s answer is a lower bound on every present key. -/
theorem minKey?_le (c : NatCollection L) (k j : Nat) (h : c.minKey? = some k)
    (hj : c.contains j = true) : k ≤ j := by
  replace h : c.minEntry?.map Prod.fst = some k := h
  obtain ⟨⟨k', v⟩, hmin, hfst⟩ := Option.map_eq_some_iff.mp h
  have hk : k' = k := hfst
  subst hk
  exact minEntry?_le c k' v j hmin hj

/-- `maxKey?`'s answer is an upper bound on every present key. -/
theorem le_maxKey? (c : NatCollection L) (k j : Nat) (h : c.maxKey? = some k)
    (hj : c.contains j = true) : j ≤ k := by
  replace h : c.maxEntry?.map Prod.fst = some k := h
  obtain ⟨⟨k', v⟩, hmax, hfst⟩ := Option.map_eq_some_iff.mp h
  have hk : k' = k := hfst
  subst hk
  exact le_maxEntry? c k' v j hmax hj

/-- The entry `entryGT?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_entryGT? (c : NatCollection L) (k j : Nat) (v : V)
    (h : c.entryGT? k = some (j, v)) : c.get? j = some v :=
  PTree.get?_of_entryGT? c.tree c.wf k j v h

/-- `entryGT?`'s answer is strictly greater than the query key. -/
theorem entryGT?_gt (c : NatCollection L) (k j : Nat) (v : V)
    (h : c.entryGT? k = some (j, v)) : k < j :=
  PTree.entryGT?_gt c.tree c.wf k j v h

/-- `entryGT?` returns the *least* key beyond the query key. -/
theorem entryGT?_le (c : NatCollection L) (k j' : Nat) (v : V) (j : Nat)
    (h : c.entryGT? k = some (j', v)) (hj : c.contains j = true) (hk : k < j) : j' ≤ j :=
  PTree.entryGT?_le c.tree c.wf k j' v j h hj hk

/-- A `none` from `entryGT?` is complete: no present key lies strictly above the query key. -/
theorem le_of_entryGT?_eq_none (c : NatCollection L) (k : Nat) (h : c.entryGT? k = none)
    (j : Nat) (hj : c.contains j = true) : j ≤ k :=
  PTree.le_of_entryGT?_eq_none c.tree c.wf k h j hj

/-- The entry `entryLT?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_entryLT? (c : NatCollection L) (k j : Nat) (v : V)
    (h : c.entryLT? k = some (j, v)) : c.get? j = some v :=
  PTree.get?_of_entryLT? c.tree c.wf k j v h

/-- `entryLT?`'s answer is strictly less than the query key. -/
theorem entryLT?_lt (c : NatCollection L) (k j : Nat) (v : V)
    (h : c.entryLT? k = some (j, v)) : j < k :=
  PTree.entryLT?_lt c.tree c.wf k j v h

/-- `entryLT?` returns the *greatest* key below the query key. -/
theorem le_entryLT? (c : NatCollection L) (k j' : Nat) (v : V) (j : Nat)
    (h : c.entryLT? k = some (j', v)) (hj : c.contains j = true) (hk : j < k) : j ≤ j' :=
  PTree.le_entryLT? c.tree c.wf k j' v j h hj hk

/-- A `none` from `entryLT?` is complete: no present key lies strictly below the query key. -/
theorem ge_of_entryLT?_eq_none (c : NatCollection L) (k : Nat) (h : c.entryLT? k = none)
    (j : Nat) (hj : c.contains j = true) : k ≤ j :=
  PTree.ge_of_entryLT?_eq_none c.tree c.wf k h j hj

/-- The entry `entryGE?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_entryGE? (c : NatCollection L) (k j : Nat) (v : V)
    (h : c.entryGE? k = some (j, v)) : c.get? j = some v := by
  unfold entryGE? at h
  cases hg : c.get? k with
  | some w =>
    rw [hg] at h
    replace h : some (k, w) = some (j, v) := h
    injection h with h1
    injection h1 with hk hv
    subst hk; subst hv
    exact hg
  | none =>
    rw [hg] at h
    replace h : c.entryGT? k = some (j, v) := h
    exact get?_of_entryGT? c k j v h

/-- `entryGE?`'s key is at or above the query key. -/
theorem entryGE?_ge (c : NatCollection L) (k j : Nat) (v : V)
    (h : c.entryGE? k = some (j, v)) : k ≤ j := by
  unfold entryGE? at h
  cases hg : c.get? k with
  | some w =>
    rw [hg] at h
    replace h : some (k, w) = some (j, v) := h
    injection h with h1
    injection h1 with hk hv
    subst hk
    exact Nat.le_refl _
  | none =>
    rw [hg] at h
    replace h : c.entryGT? k = some (j, v) := h
    exact Nat.le_of_lt (entryGT?_gt c k j v h)

/-- `entryGE?` returns the *least* key at or beyond the query key. -/
theorem entryGE?_le (c : NatCollection L) (k j' : Nat) (v : V) (j : Nat)
    (h : c.entryGE? k = some (j', v)) (hj : c.contains j = true) (hk : k ≤ j) : j' ≤ j := by
  unfold entryGE? at h
  cases hg : c.get? k with
  | some w =>
    rw [hg] at h
    replace h : some (k, w) = some (j', v) := h
    injection h with h1
    injection h1 with hk' hv
    subst hk'
    exact hk
  | none =>
    rw [hg] at h
    replace h : c.entryGT? k = some (j', v) := h
    have hne : k ≠ j := by
      intro he
      rw [contains_eq, ← he, hg] at hj
      simp at hj
    exact entryGT?_le c k j' v j h hj (Nat.lt_of_le_of_ne hk hne)

/-- A `none` from `entryGE?` is complete: every present key lies strictly below the query key. -/
theorem lt_of_entryGE?_eq_none (c : NatCollection L) (k : Nat) (h : c.entryGE? k = none)
    (j : Nat) (hj : c.contains j = true) : j < k := by
  unfold entryGE? at h
  cases hg : c.get? k with
  | some w =>
    rw [hg] at h
    replace h : some (k, w) = none := h
    simp at h
  | none =>
    rw [hg] at h
    replace h : c.entryGT? k = none := h
    have hle := le_of_entryGT?_eq_none c k h j hj
    have hne : j ≠ k := by
      intro he
      rw [contains_eq, he, hg] at hj
      simp at hj
    exact Nat.lt_of_le_of_ne hle hne

/-- The entry `entryLE?` returns is real: `get?` reads its value back at its key. -/
theorem get?_of_entryLE? (c : NatCollection L) (k j : Nat) (v : V)
    (h : c.entryLE? k = some (j, v)) : c.get? j = some v := by
  unfold entryLE? at h
  cases hg : c.get? k with
  | some w =>
    rw [hg] at h
    replace h : some (k, w) = some (j, v) := h
    injection h with h1
    injection h1 with hk hv
    subst hk; subst hv
    exact hg
  | none =>
    rw [hg] at h
    replace h : c.entryLT? k = some (j, v) := h
    exact get?_of_entryLT? c k j v h

/-- `entryLE?`'s key is at or below the query key. -/
theorem entryLE?_le (c : NatCollection L) (k j : Nat) (v : V)
    (h : c.entryLE? k = some (j, v)) : j ≤ k := by
  unfold entryLE? at h
  cases hg : c.get? k with
  | some w =>
    rw [hg] at h
    replace h : some (k, w) = some (j, v) := h
    injection h with h1
    injection h1 with hk hv
    subst hk
    exact Nat.le_refl _
  | none =>
    rw [hg] at h
    replace h : c.entryLT? k = some (j, v) := h
    exact Nat.le_of_lt (entryLT?_lt c k j v h)

/-- `entryLE?` returns the *greatest* key at or below the query key. -/
theorem le_entryLE? (c : NatCollection L) (k j' : Nat) (v : V) (j : Nat)
    (h : c.entryLE? k = some (j', v)) (hj : c.contains j = true) (hk : j ≤ k) : j ≤ j' := by
  unfold entryLE? at h
  cases hg : c.get? k with
  | some w =>
    rw [hg] at h
    replace h : some (k, w) = some (j', v) := h
    injection h with h1
    injection h1 with hk' hv
    subst hk'
    exact hk
  | none =>
    rw [hg] at h
    replace h : c.entryLT? k = some (j', v) := h
    have hne : j ≠ k := by
      intro he
      rw [contains_eq, he, hg] at hj
      simp at hj
    exact le_entryLT? c k j' v j h hj (Nat.lt_of_le_of_ne hk hne)

/-- A `none` from `entryLE?` is complete: every present key lies strictly above the query key. -/
theorem gt_of_entryLE?_eq_none (c : NatCollection L) (k : Nat) (h : c.entryLE? k = none)
    (j : Nat) (hj : c.contains j = true) : k < j := by
  unfold entryLE? at h
  cases hg : c.get? k with
  | some w =>
    rw [hg] at h
    replace h : some (k, w) = none := h
    simp at h
  | none =>
    rw [hg] at h
    replace h : c.entryLT? k = none := h
    have hge := ge_of_entryLT?_eq_none c k h j hj
    have hne : k ≠ j := by
      intro he
      rw [contains_eq, ← he, hg] at hj
      simp at hj
    exact Nat.lt_of_le_of_ne hge hne

/-- `popMinEntry?`'s entry is the collection's least entry (so `get?_of_minEntry?` and
`minEntry?_le` apply to it). -/
theorem minEntry?_of_popMinEntry? (c : NatCollection L) (e : Nat × V) (c' : NatCollection L)
    (h : c.popMinEntry? = some (e, c')) : c.minEntry? = some e := by
  unfold popMinEntry? at h
  cases hm : c.minEntry? with
  | none =>
    rw [hm] at h
    replace h : (none : Option ((Nat × V) × NatCollection L)) = some (e, c') := h
    simp at h
  | some e2 =>
    rw [hm] at h
    replace h : some (e2, c.erase e2.1) = some (e, c') := h
    injection h with h1
    injection h1 with he hc
    subst he
    rfl

/-- `popMinEntry?`'s rest is the collection with the popped key erased. -/
theorem popMinEntry?_erase (c : NatCollection L) (e : Nat × V) (c' : NatCollection L)
    (h : c.popMinEntry? = some (e, c')) : c' = c.erase e.1 := by
  unfold popMinEntry? at h
  cases hm : c.minEntry? with
  | none =>
    rw [hm] at h
    replace h : (none : Option ((Nat × V) × NatCollection L)) = some (e, c') := h
    simp at h
  | some e2 =>
    rw [hm] at h
    replace h : some (e2, c.erase e2.1) = some (e, c') := h
    injection h with h1
    injection h1 with he hc
    subst he
    exact hc.symm

/-- `popMinEntry?` answers `none` exactly on the empty collection (totality: a non-empty
collection always pops). -/
theorem popMinEntry?_eq_none (c : NatCollection L) :
    c.popMinEntry? = none ↔ c = empty := by
  constructor
  · intro h
    unfold popMinEntry? at h
    cases hm : c.minEntry? with
    | some e =>
      rw [hm] at h
      replace h : some (e, c.erase e.1) = none := h
      simp at h
    | none =>
      refine eq_empty_of_isEmpty c ?_
      show PTree.isNil c.tree = true
      by_cases hne : c.tree = .nil
      · rw [hne]; rfl
      · exfalso
        have hs := PTree.isSome_minEntry? c.tree c.wf hne
        replace hm : PTree.minEntry? c.tree = none := hm
        rw [hm] at hs
        simp at hs
  · intro h
    subst h
    unfold popMinEntry?
    have hm : (empty : NatCollection L).minEntry? = none := by
      show PTree.minEntry? (.nil : PTree L) = none
      rw [PTree.minEntry?]
    rw [hm]

/-- `popMaxEntry?`'s entry is the collection's greatest entry (so `get?_of_maxEntry?` and
`le_maxEntry?` apply to it). -/
theorem maxEntry?_of_popMaxEntry? (c : NatCollection L) (e : Nat × V) (c' : NatCollection L)
    (h : c.popMaxEntry? = some (e, c')) : c.maxEntry? = some e := by
  unfold popMaxEntry? at h
  cases hm : c.maxEntry? with
  | none =>
    rw [hm] at h
    replace h : (none : Option ((Nat × V) × NatCollection L)) = some (e, c') := h
    simp at h
  | some e2 =>
    rw [hm] at h
    replace h : some (e2, c.erase e2.1) = some (e, c') := h
    injection h with h1
    injection h1 with he hc
    subst he
    rfl

/-- `popMaxEntry?`'s rest is the collection with the popped key erased. -/
theorem popMaxEntry?_erase (c : NatCollection L) (e : Nat × V) (c' : NatCollection L)
    (h : c.popMaxEntry? = some (e, c')) : c' = c.erase e.1 := by
  unfold popMaxEntry? at h
  cases hm : c.maxEntry? with
  | none =>
    rw [hm] at h
    replace h : (none : Option ((Nat × V) × NatCollection L)) = some (e, c') := h
    simp at h
  | some e2 =>
    rw [hm] at h
    replace h : some (e2, c.erase e2.1) = some (e, c') := h
    injection h with h1
    injection h1 with he hc
    subst he
    exact hc.symm

/-- `popMaxEntry?` answers `none` exactly on the empty collection. -/
theorem popMaxEntry?_eq_none (c : NatCollection L) :
    c.popMaxEntry? = none ↔ c = empty := by
  constructor
  · intro h
    unfold popMaxEntry? at h
    cases hm : c.maxEntry? with
    | some e =>
      rw [hm] at h
      replace h : some (e, c.erase e.1) = none := h
      simp at h
    | none =>
      refine eq_empty_of_isEmpty c ?_
      show PTree.isNil c.tree = true
      by_cases hne : c.tree = .nil
      · rw [hne]; rfl
      · exfalso
        have hs := PTree.isSome_maxEntry? c.tree c.wf hne
        replace hm : PTree.maxEntry? c.tree = none := hm
        rw [hm] at hs
        simp at hs
  · intro h
    subst h
    unfold popMaxEntry?
    have hm : (empty : NatCollection L).maxEntry? = none := by
      show PTree.maxEntry? (.nil : PTree L) = none
      rw [PTree.maxEntry?]
    rw [hm]

/-! ### `erase` denotation -/

/-- Lookup after `erase`: the erased key reads `none`, every other key is unchanged. -/
theorem get?_erase (c : NatCollection L) (k j : Nat) :
    (c.erase k).get? j = if j = k then none else c.get? j :=
  PTree.get?_erase k c.tree c.wf j

/-- Membership after `erase`: the erased key is gone, every other key is untouched. -/
theorem contains_erase (c : NatCollection L) (k j : Nat) :
    (c.erase k).contains j = (c.contains j && !(j == k)) := by
  rw [contains_eq, contains_eq, get?_erase]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl]
    simp
  · rw [if_neg hjk, beq_eq_false_iff_ne.mpr hjk]
    simp

/-! ### Range-restriction denotation -/

/-- Lookup after `filterLt`: a key reads through exactly when it is strictly below the bound. -/
theorem get?_filterLt (c : NatCollection L) (k j : Nat) :
    (c.filterLt k).get? j = if j < k then c.get? j else none :=
  PTree.get?_filterLt k c.tree c.wf j

/-- Lookup after `filterGE`: a key reads through exactly when it is at or above the bound. -/
theorem get?_filterGE (c : NatCollection L) (k j : Nat) :
    (c.filterGE k).get? j = if k ≤ j then c.get? j else none :=
  PTree.get?_filterGE k c.tree c.wf j

/-- Lookup in `range`: a key reads through exactly when it lies in the inclusive window
`[lo, hi]`. -/
theorem get?_range (c : NatCollection L) (lo hi j : Nat) :
    (c.range lo hi).get? j = if lo ≤ j ∧ j ≤ hi then c.get? j else none := by
  show ((c.filterGE lo).filterLt (hi + 1)).get? j = _
  rw [get?_filterLt]
  by_cases h1 : j < hi + 1
  · rw [if_pos h1, get?_filterGE]
    by_cases h2 : lo ≤ j
    · rw [if_pos h2, if_pos ⟨h2, by omega⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.1)]
  · rw [if_neg h1, if_neg (fun h => h1 (by omega))]

/-! ### Disjointness denotation -/

/-- Disjointness characterization: `isDisjoint` answers `true` exactly when no key is present in
both collections. -/
theorem isDisjoint_iff {a b : NatCollection L} :
    a.isDisjoint b = true ↔ ∀ k, (a.contains k && b.contains k) = false :=
  PTree.isDisjoint_iff a.tree b.tree a.wf b.wf

/-- Disjointness is symmetric: sharing no key does not depend on the operand order. -/
theorem isDisjoint_symm {a b : NatCollection L} (h : a.isDisjoint b = true) :
    b.isDisjoint a = true :=
  isDisjoint_iff.mpr fun k => by rw [Bool.and_comm]; exact isDisjoint_iff.mp h k

/-- A key present in `a` is absent from `b` when the two collections are disjoint. -/
theorem contains_eq_false_of_isDisjoint {a b : NatCollection L} {k : Nat}
    (h : a.isDisjoint b = true) (hk : a.contains k = true) : b.contains k = false := by
  have hpair := isDisjoint_iff.mp h k
  rw [hk, Bool.true_and] at hpair
  exact hpair

end NatCollection

end NatCol
