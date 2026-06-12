import NatCol.Bits

/-!
# `Node`: a sparse 32-slot map

The workhorse of the trie. `positionsMask` records which of the 32 slots are present;
`elements` stores only the present children, compactly, in ascending slot order. The
array index of slot `i` is `arrayIndex positionsMask i` (popcount of the mask below
`i`), the standard HAMT trick.

These operations are generic in the child type `α`. The lattice operations
(`join`/`meet`/`restricts`) are driven by the masks so that children present on only
one side are reused (`join`) or dropped (`meet`) without inspecting them; the
`combine`/`rel` callbacks decide what happens on slots present in both. `combine`
returns `Option` so an empty intersection can prune a slot.

No `Inhabited α` is required: reads go through `xs[i]?`, and `set!`/`insertIdx!`/
`eraseIdx!` are total on `Array`.
-/

namespace NatCol

----------------------------------------------------------------------------------------------------
-- Implementation
----------------------------------------------------------------------------------------------------

/-- A sparse array of up to 32 children, addressed by a 5-bit slot index.

The `elements_compact` field is the structural invariant from `docs/DESIGN.md`: the
elements array holds *exactly* the present children, so its size equals the number of set
bits in `positionsMask`. Every `Node` value carries this proof, so it holds by
construction everywhere a node appears — and the operations below each re-establish it. -/
structure Node (α : Type u) where
  positionsMask : UInt32
  elements : Array α
  elements_compact : elements.size = popCount positionsMask

/-- Structural equality on the data fields (the `elements_compact` proof is irrelevant). -/
instance {α : Type u} [BEq α] : BEq (Node α) where
  beq a b := a.positionsMask == b.positionsMask && a.elements == b.elements

/-- The structural `BEq` decides propositional equality: it compares the two data fields
with their own (lawful) `BEq`s, and the proof field is equal by proof irrelevance. Needed so
that maps — whose leaves are `Node α` — inherit `LawfulBEq`. -/
instance {α : Type u} [BEq α] [LawfulBEq α] : LawfulBEq (Node α) where
  eq_of_beq {a b} h := by
    obtain ⟨ma, ea, ha⟩ := a
    obtain ⟨mb, eb, hb⟩ := b
    have h' : (ma == mb && ea == eb) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨h1, h2⟩ := h'
    have hmeq : ma = mb := eq_of_beq h1
    have heeq : ea = eb := eq_of_beq h2
    subst hmeq; subst heeq; rfl
  rfl {a} := by
    show (a.positionsMask == a.positionsMask && a.elements == a.elements) = true
    rw [Bool.and_eq_true]
    exact ⟨BEq.rfl, BEq.rfl⟩

/-- The value-level reading of `restricts` at a single slot/key: present on the left forces
present on the right with `rel` holding; absent on the left is vacuously fine. This is the
denotational counterpart of `restricts` the way `optVmeet` is for `meet`. Lives here (not in
`PTree`) because `Node.restricts_iff` already needs it. -/
def optRel {V : Type u} (rel : V → V → Bool) : Option V → Option V → Bool
  | some x, some y => rel x y
  | some _, none   => false
  | none,   _      => true

/-- Value-level intersection of two lookups: a key survives only if present on *both* sides.
The total-`combine` companion of `Node.optMeet`, used at the leaf/tree/collection levels where
the merge never prunes a present-on-both key. -/
def optVmeet {V : Type u} (c : V → V → V) : Option V → Option V → Option V
  | some x, some y => some (c x y)
  | _,      _      => none

/-- Value-level union of two lookups: a key survives if present on *either* side. Values present
on both are combined with `c`; a value present on one side is copied. The total-`combine` companion
of `Node.optJoin` (`combine x y = some (c x y)`), used at the leaf/tree/collection levels. -/
def optVjoin {V : Type u} (c : V → V → V) : Option V → Option V → Option V
  | some x, some y => some (c x y)
  | some x, none   => some x
  | none,   oy     => oy

/-- A leaf collection: maps 5-bit slot indices to values of type `V`. This is the single
seam that distinguishes sets (`UInt32` leaves, `V = Unit`) from maps (`Node α` leaves,
`V = α`); everything else is shared. -/
class LeafOps (L : Type u) (V : outParam (Type u)) where
  empty     : L
  isEmpty   : L → Bool
  size      : L → Nat
  get?      : L → UInt32 → Option V
  /-- Membership test at a slot, returning `Bool` directly so the lookup path avoids boxing an
  `Option` it only inspects for presence. Tied to `get?` by `contains_eq_isSome`. -/
  contains  : L → UInt32 → Bool
  insert    : L → UInt32 → V → L
  erase     : L → UInt32 → L
  modify    : L → UInt32 → (V → V) → L
  join      : (V → V → V) → L → L → L
  meet      : (V → V → V) → L → L → L
  restricts : (V → V → Bool) → L → L → Bool
  /-- Whether no slot is present on both leaves (one mask `AND`, no allocation). The leaf base
  case of `PTree.isDisjoint`. -/
  disjoint  : L → L → Bool
  /-- Keep `a`'s slots absent from `b` (set difference at the leaf; `b`'s values are irrelevant).
  The leaf base case of `PTree.diff`. -/
  diff      : L → L → L
  /-- Keep the slots present in exactly one leaf (shared slots cancel). The leaf base case of
  `PTree.symmDiff`. -/
  symmDiff  : L → L → L
  /-- Present `(slot, value)` pairs in ascending slot order. -/
  toArray   : L → Array (UInt32 × V)
  /-- Keep only the slots whose `(slot, value)` satisfies `p`. The leaf base case of
  `PTree.filter`; a fully-filtered leaf becomes empty, but that emptiness is governed one level
  up (`filterU` drops an emptied `tip`), so this carries no canonical-shape obligation of its own. -/
  filter    : (UInt32 → V → Bool) → L → L
  /-- A representative present slot of a non-empty leaf (the lowest set slot). `NatCol.PTree`
  reconstructs a representative key for a `tip` from this (`someKey`, `witnessKey`), which its
  branch/`join` routing needs to recover a node's shared prefix. -/
  someSlot  : L → UInt32
  /-- The occupancy bitmap: bit `i` is set iff slot `i` is present (agrees with `contains`).
  Powers the ordered queries (`PTree.minEntry?`/`entryGT?`/…), which pick slots by masked
  bit-scans (`lowestSetIdx`/`highestSetIdx` under `lowerMask`/`upperMask`). -/
  slotsMask : L → UInt32
  /-- `contains` agrees with `get?`'s presence: the `Bool` fast path matches the denotational
  lookup. Lets the collection layer keep its `get?`-based membership lemmas after routing
  `contains` through the boxing-free path. -/
  contains_eq_isSome : ∀ (l : L) (i : UInt32), contains l i = (get? l i).isSome
  /-- Inserting a value yields a non-empty leaf, so freshly-built subtrees are never empty.
  Part of the canonical-shape invariant (`PTree.WF`). -/
  insert_ne_empty : ∀ (l : L) (i : UInt32) (v : V), isEmpty (insert l i v) = false
  /-- Modifying a value never changes whether a leaf is empty (it touches values, not
  presence), so `modify` preserves canonical shape. -/
  isEmpty_modify : ∀ (l : L) (i : UInt32) (g : V → V), isEmpty (modify l i g) = isEmpty l
  /-- The empty leaf reads as empty. Lets the collection layer prove `empty.isEmpty = true`,
  which the lattice identities (e.g. left identity of `join`) bottom out in. -/
  isEmpty_empty : isEmpty (empty : L) = true
  /-- An empty leaf *is* the empty leaf (the canonical converse of `isEmpty_empty`). Lets the
  collection layer recover `c = empty` from `c.isEmpty = true` at height 0, which the right
  identity of `join` (`join a empty = a`) bottoms out in. -/
  eq_empty_of_isEmpty : ∀ (l : L), isEmpty l = true → l = empty
  /-- `restricts` is reflexive on a leaf when `rel` is reflexive on values: a leaf's keys are
  trivially a subset of its own, and `rel` holds on every coinciding value. Lets the collection
  layer prove reflexivity of `restricts`. -/
  restricts_refl : ∀ (rel : V → V → Bool), (∀ x, rel x x = true) →
    ∀ (l : L), restricts rel l l = true
  /-- `join` commutes when the combine is flipped: merging `a` into `b` with `f` equals
  merging `b` into `a` with `f`'s arguments swapped. Lets the collection layer derive
  commutativity of `join`; `joinEq_comm` lifts it through the tree. -/
  join_comm : ∀ (f g : V → V → V), (∀ x y, f x y = g y x) →
    ∀ (a b : L), join f a b = join g b a
  /-- `meet` commutes when the combine is flipped (the `meet` analogue of `join_comm`). Lets the
  collection layer derive commutativity of `meet`; `meetEq_comm` lifts it through the tree. -/
  meet_comm : ∀ (f g : V → V → V), (∀ x y, f x y = g y x) →
    ∀ (a b : L), meet f a b = meet g b a
  /-- `join` is associative when the combine is associative. Lets the collection layer derive
  associativity of `join`; `joinEq_assoc` lifts it through the tree. -/
  join_assoc : ∀ (c : V → V → V), (∀ x y z, c (c x y) z = c x (c y z)) →
    ∀ (a b d : L), join c (join c a b) d = join c a (join c b d)
  /-- Joining (with any combine) onto a non-empty leaf stays non-empty. Backs the `tip`/`tip`
  case of `PTree.WF_union`: a joined leaf stays non-empty, which `union`'s canonical-shape
  preservation needs. -/
  isEmpty_join : ∀ (c : V → V → V) (a b : L), isEmpty a = false → isEmpty (join c a b) = false
  /-- The empty leaf reads `none` everywhere. Backs the `get?`-based denotational semantics the
  `meet`-associativity proof is built against. -/
  get?_empty : ∀ (i : UInt32), get? (empty : L) i = none
  /-- `get?` reads a `meet` as the value-level intersection (`optVmeet`) of the two lookups: a
  slot survives only if present on both leaves. The leaf base case of `PTree.get?_meet`. Stated
  on in-range slots (`< 32`); leaf `get?` only ever reads `chunk`s, which are. -/
  get?_meet : ∀ (c : V → V → V) (a b : L) (i : UInt32), i < 32 →
    get? (meet c a b) i = optVmeet c (get? a i) (get? b i)
  /-- `get?` of a `join` is the value-level union of the two lookups. The leaf base case of
  `PTree.get?_union`. -/
  get?_join : ∀ (c : V → V → V) (a b : L) (i : UInt32), i < 32 →
    get? (join c a b) i = optVjoin c (get? a i) (get? b i)
  /-- `get?` reads an `insert` pointwise: the inserted slot reads the new value, every other slot
  is unchanged. Stated on in-range slots (`< 32`); leaf `get?`/`insert` only ever touch `chunk`s,
  which are. The leaf base case of `PTree.get?_insert`. -/
  get?_insert : ∀ (l : L) (i j : UInt32) (v : V), i < 32 → j < 32 →
    get? (insert l i v) j = if j = i then some v else get? l j
  /-- `get?` reads an `erase` pointwise: the erased slot reads `none`, every other slot is
  unchanged. Stated on in-range slots (`< 32`), like `get?_insert`. The leaf base case of
  `PTree.get?_erase`. -/
  get?_erase : ∀ (l : L) (i j : UInt32), i < 32 → j < 32 →
    get? (erase l i) j = if j = i then none else get? l j
  /-- `get?` reads a `filter` pointwise: a slot survives exactly when present and accepted by the
  predicate. The leaf base case of `PTree.get?_filterLt`/`get?_filterGE`. -/
  get?_filter : ∀ (p : UInt32 → V → Bool) (l : L) (j : UInt32), j < 32 →
    get? (filter p l) j = match get? l j with
      | some v => if p j v then some v else none
      | none => none
  /-- A leaf is determined by its `get?` at in-range slots. The leaf base case of `PTree.ext_get?`. -/
  get?_ext : ∀ (a b : L), (∀ i, i < 32 → get? a i = get? b i) → a = b
  /-- `restricts` reads denotationally: it holds exactly when, slot by slot, a present left value
  forces a related right value (`optRel`). The reflexivity hypothesis lets the *set* leaf — whose
  `restricts` discards `rel`, comparing only the bitsets — still satisfy this (its sole value is
  `()`, so reflexivity makes `rel` vacuous on shared slots). The leaf base case of
  `PTree.subset_iff`, which drives `restricts` transitivity. -/
  get?_restricts : ∀ (rel : V → V → Bool), (∀ x, rel x x = true) → ∀ (a b : L),
    (restricts rel a b = true ↔ ∀ i, i < 32 → optRel rel (get? a i) (get? b i) = true)
  /-- The representative slot of a non-empty leaf is in range (`< 32`). Backs the in-range
  reasoning `PTree.someKey`/`witnessKey` need (the low chunk must not bleed into the prefix). -/
  someSlot_lt : ∀ (l : L), isEmpty l = false → someSlot l < 32
  /-- The representative slot of a non-empty leaf is actually present. Backs `PTree.witnessKey`,
  which must exhibit a real member of the leaf. -/
  contains_someSlot : ∀ (l : L), isEmpty l = false → contains l (someSlot l) = true
  /-- The occupancy bitmap is accurate: an in-range bit is set exactly when the slot is present.
  What lets the ordered queries' bit-scans (`lowestSetIdx`/`highestSetIdx` over `slotsMask`)
  select real members and skip none — `PTree.minEntry?`'s denotational laws ride on it. -/
  testBit_slotsMask : ∀ (l : L) (i : UInt32), i < 32 → testBit (slotsMask l) i = contains l i
  /-- `disjoint` is the occupancy-bitmap `AND`: two leaves are disjoint exactly when their
  `slotsMask`s share no bit. With `testBit_slotsMask`, the single law `PTree.isDisjoint`'s
  no-shared-key characterization bottoms out in. -/
  disjoint_eq_slotsMask : ∀ (a b : L), disjoint a b = (slotsMask a &&& slotsMask b == 0)
  /-- Subtracting a leaf from itself empties it. The leaf base case of `PTree.diff_self`. -/
  isEmpty_diff_self : ∀ (l : L), isEmpty (diff l l) = true

/-- Leaf operations for sets: a `UInt32` is a 32-element bitset; the value type is `Unit`. This is
the set leaf instance the path-compressed `PTree` (and `NatSet`) instantiates at; it lives here in
the leaf foundation so it sits below `PTree`. -/
instance : LeafOps UInt32 Unit where
  empty := 0
  isEmpty u := u == 0
  size := popCount
  get? u i := if testBit u i then some () else none
  contains u i := testBit u i
  insert u i _ := setBit u i
  erase := clearBit
  modify u _ _ := u
  join _ a b := a ||| b
  meet _ a b := a &&& b
  restricts _ a b := (a &&& b) == a
  disjoint a b := (a &&& b) == 0
  diff a b := a &&& ~~~b
  symmDiff a b := a ^^^ b
  toArray u := Nat.fold 32 (fun i _ acc =>
    let iu := UInt32.ofNat i
    if testBit u iu then acc.push (iu, ()) else acc) #[]
  filter p u := Nat.fold 32 (fun i _ acc =>
    let iu := UInt32.ofNat i
    if testBit u iu && p iu () then setBit acc iu else acc) (0 : UInt32)
  someSlot := lowestSetIdx
  slotsMask u := u
  contains_eq_isSome u i := by
    show testBit u i = (if testBit u i then some () else none).isSome
    cases testBit u i <;> rfl
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
  get?_erase l i j hi hj := by
    show (if testBit (clearBit l i) j then some () else none)
        = if j = i then none else (if testBit l j then some () else none)
    rw [testBit_clearBit l i j hi hj]
    by_cases hji : j = i
    · subst hji
      simp
    · rw [if_neg hji, beq_eq_false_iff_ne.mpr (fun hc => hji hc.symm), Bool.not_false,
          Bool.and_true]
  get?_filter p u j hj := by
    have hjn : j.toNat < 32 := by
      have h := UInt32.lt_iff_toNat_lt.mp hj
      simpa using h
    rw [testBit_filterFold p u 32 (Nat.le_refl 32) j hj, decide_eq_true hjn, Bool.true_and]
    by_cases htb : testBit u j = true <;> by_cases hp : p j () = true <;> simp [htb, hp]
  get?_ext a b h := by
    apply eq_of_testBit_eq
    intro i hi
    have hi' := h i hi
    by_cases ha : testBit a i = true <;> by_cases hb : testBit b i = true <;> simp_all
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
  someSlot_lt u h := lowestSetIdx_lt u (beq_eq_false_iff_ne.mp h)
  contains_someSlot u h := testBit_lowestSetIdx u (beq_eq_false_iff_ne.mp h)
  testBit_slotsMask _ _ _ := rfl
  disjoint_eq_slotsMask _ _ := rfl
  isEmpty_diff_self u := by
    show ((u &&& ~~~u) == 0) = true
    simp [show u &&& ~~~u = 0 from by bv_decide]

namespace Node

def empty : Node α := ⟨0, Array.emptyWithCapacity 0, by simp [show popCount 0 = 0 from rfl]⟩

/-- An empty node (no slots present) whose element array is pre-allocated with capacity `c`.
The capacity is only an allocation hint, so this is equal *as a value* to `Node.empty`;
`join`/`meet` start their accumulator here, sized to the result's final element count, so the
ascending inserts that build the result never reallocate. -/
private def emptyWithCapacity (c : Nat) : Node α :=
  ⟨0, Array.emptyWithCapacity c, by simp [show popCount 0 = 0 from rfl]⟩

def singleton (i : UInt32) (a : α) : Node α :=
  ⟨setBit 0 i, #[a], by
    rw [popCount_setBit 0 i (testBit_zero i)]; simp [show popCount 0 = 0 from rfl]⟩

@[inline] def isEmpty (n : Node α) : Bool := n.positionsMask == 0

@[inline] def size (n : Node α) : Nat := popCount n.positionsMask

/-- The child at a *present* slot. The bit-set proof makes the compact index in-bounds
(`arrayIndex_lt` + the `elements_compact` field), so the read is total — no `Option`, no
spurious `none` to discharge at the call site. -/
@[inline] def get (n : Node α) (i : UInt32) (h : testBit n.positionsMask i = true) : α :=
  n.elements[arrayIndex n.positionsMask i]'(by
    rw [n.elements_compact]; exact arrayIndex_lt n.positionsMask i h)

/-- The child at slot `i`, if present. The dependent `if` hands the present-case proof to
`get`, so there is no spurious `none`. -/
@[inline] def get? (n : Node α) (i : UInt32) : Option α :=
  if h : testBit n.positionsMask i = true then some (n.get i h) else none

/-- General single-slot update: `f` sees the current value at slot `i` (if any) and
returns the new value (`none` removes the slot).

Matching on `hpres : testBit … = true/false` records whether the slot was present, which
is exactly what the compactness proofs need: a present slot's compact index is `< size`
(so `eraseIdx`/`set` are in bounds and clearing the bit drops the count by one), and an
absent slot's index is `≤ size` (so `insertIdx` is in bounds and setting the bit raises
the count by one). -/
@[specialize] def alter (n : Node α) (i : UInt32) (f : Option α → Option α) : Node α :=
  match hpres : testBit n.positionsMask i with
  | true =>
    match f (some (n.get i hpres)) with
    | some a => ⟨n.positionsMask, n.elements.set! (arrayIndex n.positionsMask i) a, by
        simp only [Array.set!, Array.size_setIfInBounds]; exact n.elements_compact⟩
    | none => ⟨clearBit n.positionsMask i, n.elements.eraseIdx! (arrayIndex n.positionsMask i), by
        have hlt : arrayIndex n.positionsMask i < n.elements.size := by
          rw [n.elements_compact]; exact arrayIndex_lt n.positionsMask i hpres
        have hcl := popCount_clearBit n.positionsMask i hpres
        rw [show n.elements.eraseIdx! (arrayIndex n.positionsMask i)
              = n.elements.eraseIdx (arrayIndex n.positionsMask i) hlt from dif_pos hlt,
            Array.size_eraseIdx, n.elements_compact]
        omega⟩
  | false =>
    match f none with
    | some a => ⟨setBit n.positionsMask i, n.elements.insertIdx! (arrayIndex n.positionsMask i) a, by
        have hle : arrayIndex n.positionsMask i ≤ n.elements.size := by
          rw [n.elements_compact]; exact arrayIndex_le n.positionsMask i
        have hsb := popCount_setBit n.positionsMask i hpres
        rw [show n.elements.insertIdx! (arrayIndex n.positionsMask i) a
              = n.elements.insertIdx (arrayIndex n.positionsMask i) a hle from dif_pos hle,
            Array.size_insertIdx, n.elements_compact, hsb]⟩
    | none => n

def insert (n : Node α) (i : UInt32) (a : α) : Node α := n.alter i (fun _ => some a)

def erase (n : Node α) (i : UInt32) : Node α := n.alter i (fun _ => none)

def modify (n : Node α) (i : UInt32) (f : α → α) : Node α := n.alter i (Option.map f)

/-- Iterate `f acc i child` over the *present* slots of `n` (those of `m`), lowest first
(`lowestSetIdx`/`clearLowest`), reading the child with `get?`/`Option.elim` (a function application,
as `restrictsLoop` feeds `get?` into `optRel`). Only the `popCount m` present slots are visited —
no full 0..31 scan. Terminates because `clearLowest` strictly decreases the mask. -/
@[specialize] private def foldLoop {β : Type v} (f : β → UInt32 → α → β) (n : Node α) (m : UInt32) (acc : β) : β :=
  if _hm : m = 0 then acc
  else foldLoop f n (clearLowest m)
        ((n.get? (lowestSetIdx m)).elim acc (fun a => f acc (lowestSetIdx m) a))
termination_by m.toNat
decreasing_by exact toNat_clearLowest_lt m _hm

/-- Fold over present slots in ascending slot order. -/
@[specialize] def fold {β : Type v} (f : β → UInt32 → α → β) (init : β) (n : Node α) : β :=
  foldLoop f n n.positionsMask init

/-- Monadic `foldLoop`: iterate `f acc i child` over the present slots of `n` (those of `mask`),
lowest first, threading effects through `m`. The monadic companion of `foldLoop`. -/
@[specialize] private def foldMLoop {β : Type v} {m : Type v → Type w} [Monad m] (f : β → UInt32 → α → m β)
    (n : Node α) (mask : UInt32) (acc : β) : m β :=
  if _hm : mask = 0 then pure acc
  else do
    let acc' ← (n.get? (lowestSetIdx mask)).elim (pure acc) (fun a => f acc (lowestSetIdx mask) a)
    foldMLoop f n (clearLowest mask) acc'
termination_by mask.toNat
decreasing_by exact toNat_clearLowest_lt mask _hm

/-- Monadic fold over present slots in ascending slot order, exposing the slot index. The monadic
companion of `fold` (which is the `m := Id` instance). -/
@[specialize] def foldM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → UInt32 → α → m β)
    (init : β) (n : Node α) : m β :=
  foldMLoop f n n.positionsMask init

/-- `all` driver: `&&`-accumulate `p` over the present slots of `n` (those of `m`), lowest first.
`&&` short-circuits the per-slot `p` once `acc` is `false`, and only the `popCount m` present slots
are visited — no full 0..31 scan (the `restrictsLoop` shape). -/
@[specialize] private def allLoop (p : UInt32 → α → Bool) (n : Node α) (m : UInt32) (acc : Bool) : Bool :=
  if _hm : m = 0 then acc
  else allLoop p n (clearLowest m)
        (acc && (n.get? (lowestSetIdx m)).elim true (fun a => p (lowestSetIdx m) a))
termination_by m.toNat
decreasing_by exact toNat_clearLowest_lt m _hm

/-- Whether every present slot (slot index + child) satisfies `p`. `&&`-folds `p` over the present
slots, short-circuiting the predicate once a slot fails. -/
@[specialize] def all (p : UInt32 → α → Bool) (n : Node α) : Bool :=
  allLoop p n n.positionsMask true

/-- `any` driver: `||`-accumulate `p` over the present slots of `n` (those of `m`), lowest first.
`||` short-circuits the per-slot `p` once `acc` is `true`; only present slots are visited. -/
@[specialize] private def anyLoop (p : UInt32 → α → Bool) (n : Node α) (m : UInt32) (acc : Bool) : Bool :=
  if _hm : m = 0 then acc
  else anyLoop p n (clearLowest m)
        (acc || (n.get? (lowestSetIdx m)).elim false (fun a => p (lowestSetIdx m) a))
termination_by m.toNat
decreasing_by exact toNat_clearLowest_lt m _hm

/-- Whether some present slot satisfies `p`. `||`-folds `p` over the present slots, short-circuiting
the predicate once a slot holds. The `any` companion of `all`. -/
@[specialize] def any (p : UInt32 → α → Bool) (n : Node α) : Bool :=
  anyLoop p n n.positionsMask false

/-- Monadic `all` driver: scan the present slots of `n` (those of `mask`), lowest first, running
`p` on each child and short-circuiting (returning `pure false` without recursing) at the first slot
where `p` returns `false` — later slots are then neither visited nor run. -/
@[specialize] private def allMLoop {m : Type → Type w} [Monad m] (p : UInt32 → α → m Bool) (n : Node α)
    (mask : UInt32) : m Bool :=
  if _hm : mask = 0 then pure true
  else do
    let keep ← (n.get? (lowestSetIdx mask)).elim (pure true) (fun a => p (lowestSetIdx mask) a)
    if keep then allMLoop p n (clearLowest mask) else pure false
termination_by mask.toNat
decreasing_by exact toNat_clearLowest_lt mask _hm

/-- Monadic `all`: whether every present slot satisfies the monadic predicate `p`, threading `p`'s
effects through `m` in ascending slot order and short-circuiting at the first slot where `p` returns
`false` (later slots are then neither visited nor run). The monadic companion of `all` (its
`m := Id` instance). -/
@[specialize] def allM {m : Type → Type w} [Monad m] (p : UInt32 → α → m Bool) (n : Node α) : m Bool :=
  allMLoop p n n.positionsMask

/-- Monadic `any` driver: scan the present slots of `n` (those of `mask`), lowest first, running
`p` on each child and short-circuiting (returning `pure true` without recursing) at the first slot
where `p` returns `true`. -/
@[specialize] private def anyMLoop {m : Type → Type w} [Monad m] (p : UInt32 → α → m Bool) (n : Node α)
    (mask : UInt32) : m Bool :=
  if _hm : mask = 0 then pure false
  else do
    let found ← (n.get? (lowestSetIdx mask)).elim (pure false) (fun a => p (lowestSetIdx mask) a)
    if found then pure true else anyMLoop p n (clearLowest mask)
termination_by mask.toNat
decreasing_by exact toNat_clearLowest_lt mask _hm

/-- Monadic `any`: whether some present slot satisfies the monadic predicate `p`, short-circuiting
at the first slot where it returns `true`. The `any` companion of `allM`. -/
@[specialize] def anyM {m : Type → Type w} [Monad m] (p : UInt32 → α → m Bool) (n : Node α) : m Bool :=
  anyMLoop p n n.positionsMask

/-- Map a function over every stored child, preserving the slot structure: the slot mask and
the array length are untouched, so only the element *type* changes (`α` to `β`). The compactness
invariant is inherited from `n` because `Array.map` preserves size. This is the functorial
action underlying `NatMap.map`. -/
@[inline] def map {β : Type v} (f : α → β) (n : Node α) : Node β :=
  ⟨n.positionsMask, n.elements.map f, by rw [Array.size_map]; exact n.elements_compact⟩

/-- Iterate `step acc i` over the *present* slots `i` of `m`, lowest first, clearing each bit as
it is consumed (`clearLowest`). Only the `popCount m` present slots are visited — no full 0..31
scan. Terminates because `clearLowest` strictly decreases the mask (`clearLowest_lt`). The driver
for `join`/`meet`: `m` is the union/intersection of the operands' masks, so a slot absent on both
sides is never touched. -/
@[specialize] private def mergeLoop (step : Node α → UInt32 → Node α) (m : UInt32) (acc : Node α) : Node α :=
  if _hm : m = 0 then acc
  else mergeLoop step (clearLowest m) (step acc (lowestSetIdx m))
termination_by m.toNat
decreasing_by exact toNat_clearLowest_lt m _hm

/-- One `join` slot step: merge slot `i` of `a` and `b` into `acc`. Present on both ↦ `combine`
(a `none` result prunes the slot); present on one ↦ copy that child; absent on both ↦ leave `acc`
unchanged. The `insert` appends at the end because `mergeLoop` visits slots in ascending order. -/
@[specialize] private def joinStep (combine : α → α → Option α) (a b acc : Node α) (i : UInt32) : Node α :=
  match ha : testBit a.positionsMask i, hb : testBit b.positionsMask i with
  | true, true =>
    match combine (a.get i ha) (b.get i hb) with
    | some v => acc.insert i v
    | none   => acc
  | true, false => acc.insert i (a.get i ha)
  | false, true => acc.insert i (b.get i hb)
  | false, false => acc

/-- Union of two nodes. Slots in exactly one side are reused as-is; slots in both are merged with
`combine` (a `none` result drops the slot). Built by stepping `joinStep` over the present slots of
the union mask `a.positionsMask ||| b.positionsMask` (via `mergeLoop`), so only present slots are
visited; the accumulator is pre-sized to that mask's slot count and the ascending inserts append,
so the result is compact by construction. -/
@[specialize] def join (combine : α → α → Option α) (a b : Node α) : Node α :=
  mergeLoop (joinStep combine a b) (a.positionsMask ||| b.positionsMask)
    (Node.emptyWithCapacity (popCount (a.positionsMask ||| b.positionsMask)))

/-- One `meet` slot step: only slots present on *both* sides survive (merged with `combine`, a
`none` result pruning); every other case drops the slot, leaving `acc`. -/
@[specialize] private def meetStep (combine : α → α → Option α) (a b acc : Node α) (i : UInt32) : Node α :=
  match ha : testBit a.positionsMask i, hb : testBit b.positionsMask i with
  | true, true =>
    match combine (a.get i ha) (b.get i hb) with
    | some v => acc.insert i v
    | none   => acc
  | true, false => acc
  | false, true => acc
  | false, false => acc

/-- Intersection of two nodes. Only slots present in both survive, merged with `combine`; a `none`
result (empty intersection) drops the slot. Built by stepping `meetStep` over the present slots of
the intersection mask `a.positionsMask &&& b.positionsMask` (via `mergeLoop`), so only the shared
slots are visited; pre-sized to that mask's slot count, so the result is compact by construction. -/
@[specialize] def meet (combine : α → α → Option α) (a b : Node α) : Node α :=
  mergeLoop (meetStep combine a b) (a.positionsMask &&& b.positionsMask)
    (Node.emptyWithCapacity (popCount (a.positionsMask &&& b.positionsMask)))

/-- One `filterMap` slot step: keep slot `i` of `n` when `f` maps its child to `some`, dropping it
on `none` or when the slot is absent. The single-operand analogue of `meetStep` (it reads the
original `n`, not `acc`); the `insert` appends because `mergeLoop` visits slots in ascending order. -/
@[specialize] private def filterMapStep (f : UInt32 → α → Option α) (n acc : Node α) (i : UInt32) : Node α :=
  match h : testBit n.positionsMask i with
  | true =>
    match f i (n.get i h) with
    | some y => acc.insert i y
    | none   => acc
  | false => acc

/-- Filter-and-map over present slots: for each present slot `i` holding child `a`, keep `f i a`
when it is `some` and drop the slot when it is `none`. Like `map`, but `f` is slot-aware and may
remove slots. Built — as `join`/`meet` are — by stepping `filterMapStep` over the present slots of
`n` (`mergeLoop`), so only the `popCount` present slots are visited (no 0..31 scan); pre-sized to
that count (an upper bound on the survivors), so the result is compact by construction. -/
def filterMap (f : UInt32 → α → Option α) (n : Node α) : Node α :=
  mergeLoop (filterMapStep f n) n.positionsMask
    (Node.emptyWithCapacity (popCount n.positionsMask))

/-- AND-fold `optRel`'s per-slot verdict over the *present* slots of `m`, lowest first
(`lowestSetIdx`/`clearLowest`). `&&` short-circuits the `optRel` call once `acc` is `false`, and
only the `popCount m` present slots are visited — no full 0..31 scan. Terminates because
`clearLowest` strictly decreases the mask. The driver for `restricts`: `m` is the left operand's
mask, so a slot absent on the left (where `restricts` is vacuously fine) is never touched. -/
@[specialize] private def restrictsLoop (rel : α → α → Bool) (a b : Node α) (m : UInt32) (acc : Bool) : Bool :=
  if _hm : m = 0 then acc
  else restrictsLoop rel a b (clearLowest m)
        (acc && optRel rel (a.get? (lowestSetIdx m)) (b.get? (lowestSetIdx m)))
termination_by m.toNat
decreasing_by exact toNat_clearLowest_lt m _hm

/-- `a` restricts `b`: every slot of `a` is present in `b`, and `rel` holds on every shared child.
The mask guard `a.mask &&& b.mask = a.mask` is the O(1) "domain subset" fast reject; the loop then
checks `optRel` on each of `a`'s present slots — the only slots where `restricts` is non-vacuous —
visiting just `popCount a.mask` of them rather than scanning all 32. -/
def restricts (rel : α → α → Bool) (a b : Node α) : Bool :=
  if (a.positionsMask &&& b.positionsMask) != a.positionsMask then false
  else restrictsLoop rel a b a.positionsMask true

/-- Value-level merge underlying `Node.join`: present on both sides ↦ `combine`; on one ↦ copy. -/
def optJoin (combine : α → α → Option α) : Option α → Option α → Option α
  | some x, some y => combine x y
  | some x, none   => some x
  | none,   some y => some y
  | none,   none   => none

/-- Value-level merge underlying `Node.meet`: present on *both* sides ↦ `combine`; otherwise drop. -/
def optMeet (combine : α → α → Option α) : Option α → Option α → Option α
  | some x, some y => combine x y
  | _,      _      => none

end Node

/-! ## Tests -/

section Tests
open Node

private def n0 : Node Nat := Node.empty
private def nA : Node Nat := (Node.singleton 1 10).insert 4 40 |>.insert 31 310
private def nB : Node Nat := (Node.singleton 4 99).insert 7 70

#guard n0.isEmpty
#guard !nA.isEmpty
#guard nA.size = 3
#guard nA.get? 1 = some 10
#guard nA.get? 4 = some 40
#guard nA.get? 31 = some 310
#guard nA.get? 2 = none
#guard nA.get? 0 = none

-- insert at slot 0 (lowest) and check ordering is preserved structurally
#guard (Node.singleton 5 50 |>.insert 0 0 |>.get? 0) = some 0
#guard (Node.singleton 5 50 |>.insert 0 0 |>.get? 5) = some 50

#guard (nA.insert 4 400 |>.get? 4) = some 400
#guard (nA.insert 4 400).size = 3

-- erase then re-query; erasing an absent slot is a no-op
#guard (nA.erase 4 |>.get? 4) = none
#guard (nA.erase 4).size = 2
-- `Node` has `BEq`/`LawfulBEq` but no `DecidableEq`, so node-vs-node tests stay on `==`
#guard nA.erase 2 == nA

-- modify only touches present slots
#guard (nA.modify 1 (· + 5) |>.get? 1) = some 15
#guard nA.modify 2 (· + 5) == nA

-- join: slot 4 collides (sum), others copied through
#guard (Node.join (fun x y => some (x + y)) nA nB |>.get? 1) = some 10
#guard (Node.join (fun x y => some (x + y)) nA nB |>.get? 4) = some 139
#guard (Node.join (fun x y => some (x + y)) nA nB |>.get? 7) = some 70
#guard (Node.join (fun x y => some (x + y)) nA nB).size = 4

-- meet: only the shared slot 4 survives
#guard (Node.meet (fun x y => some (x + y)) nA nB |>.get? 4) = some 139
#guard (Node.meet (fun x y => some (x + y)) nA nB).size = 1
#guard (Node.meet (fun _ _ => none) nA nB).isEmpty           -- pruned to empty

-- restricts: subset of slots + predicate on shared values
#guard Node.restricts (fun _ _ => true) (Node.singleton 4 40) nA
#guard !Node.restricts (fun _ _ => true) nA (Node.singleton 4 40)   -- nA has more slots
#guard Node.restricts (fun x y => x ≤ y) (Node.singleton 4 40) nA
#guard !Node.restricts (fun x y => x < y) (Node.singleton 4 40) nA  -- 40 < 40 fails
#guard Node.restricts (fun _ _ => true) Node.empty nA              -- empty restricts all

-- fold visits slots ascending
#guard nA.fold (fun acc i a => acc ++ [(i.toNat, a)]) [] = [(1, 10), (4, 40), (31, 310)]

-- the `elements_compact` invariant is a field every node carries, so it is available on
-- operation results too — here, on a `join` output — by construction, no side condition
example : (Node.join (fun x y => some (x + y)) nA nB).elements.size
        = popCount (Node.join (fun x y => some (x + y)) nA nB).positionsMask :=
  (Node.join (fun x y => some (x + y)) nA nB).elements_compact

end Tests

----------------------------------------------------------------------------------------------------
-- Theorems
----------------------------------------------------------------------------------------------------

/-- `optRel` is transitive when `rel` is: composing two restrictions composes the values via
`rel`-transitivity, and an absent left side stays vacuous. The engine of `restricts`
transitivity at every layer. -/
theorem optRel_trans {V : Type u} (rel : V → V → Bool)
    (htrans : ∀ x y z, rel x y = true → rel y z = true → rel x z = true) :
    ∀ (ox oy oz : Option V),
      optRel rel ox oy = true → optRel rel oy oz = true → optRel rel ox oz = true
  | none, _, _, _, _ => rfl
  | some _, none, _, h, _ => absurd h (by simp [optRel])
  | some _, some _, none, _, h => absurd h (by simp [optRel])
  | some x, some y, some z, hxy, hyz => htrans x y z hxy hyz

/-- `optRel` is anti-symmetric when `rel` is: mutual restriction forces both sides present (an
absent side fails the other direction) and pins their values equal via `rel`-antisymmetry. The
engine of `restricts` anti-symmetry at every layer. -/
theorem optRel_antisymm {V : Type u} (rel : V → V → Bool)
    (hantisymm : ∀ x y, rel x y = true → rel y x = true → x = y) :
    ∀ (ox oy : Option V),
      optRel rel ox oy = true → optRel rel oy ox = true → ox = oy
  | none, none, _, _ => rfl
  | none, some _, _, h => absurd h (by simp [optRel])
  | some _, none, h, _ => absurd h (by simp [optRel])
  | some x, some y, hxy, hyx => by rw [hantisymm x y hxy hyx]

/-- `optVmeet` is associative when the value combine is. -/
theorem optVmeet_assoc {V : Type u} (c : V → V → V) (hc : ∀ x y z, c (c x y) z = c x (c y z))
    (oa ob od : Option V) :
    optVmeet c (optVmeet c oa ob) od = optVmeet c oa (optVmeet c ob od) := by
  cases oa <;> cases ob <;> cases od <;> simp only [optVmeet]
  rw [hc]

/-- `optVmeet` with the combine's arguments flipped swaps the operands. -/
theorem optVmeet_flip {V : Type u} (c : V → V → V) (ox oy : Option V) :
    optVmeet (fun x y => c y x) oy ox = optVmeet c ox oy := by
  cases ox <;> cases oy <;> rfl

/-- A value present only on the left is copied through a `join`. -/
@[simp] theorem optVjoin_none_right {V : Type u} (c : V → V → V) (ox : Option V) :
    optVjoin c ox none = ox := by
  cases ox <;> rfl

/-- `optVjoin` with the combine's arguments flipped swaps the operands. -/
theorem optVjoin_flip {V : Type u} (c : V → V → V) (ox oy : Option V) :
    optVjoin (fun x y => c y x) oy ox = optVjoin c ox oy := by
  cases ox <;> cases oy <;> rfl

/-- `optVmeet` distributes over `optVjoin` from the left when the meet combine distributes over the
join combine pointwise (`hdist : cm x (cj y z) = cj (cm x y) (cm x z)`). One-sided keys are dropped
by `optVmeet` on both sides, so only the all-present case actually uses `hdist`. -/
theorem optVmeet_optVjoin_distrib {V : Type u} (cm cj : V → V → V)
    (hdist : ∀ x y z, cm x (cj y z) = cj (cm x y) (cm x z)) (oa ob oc : Option V) :
    optVmeet cm oa (optVjoin cj ob oc) = optVjoin cj (optVmeet cm oa ob) (optVmeet cm oa oc) := by
  cases oa <;> cases ob <;> cases oc <;> simp only [optVmeet, optVjoin] <;>
    first | rfl | rw [hdist]

/-- `optVjoin` distributes over `optVmeet` from the left, given the full lattice algebra on the
combines: the meet combine is idempotent (`hidem`) and absorbs the join combine (`habs1`/`habs2`),
and the join combine distributes over the meet combine (`hdist`). Unlike the dual law, *every*
mixed-presence case is non-trivial here, because `optVjoin` copies (rather than drops) one-sided
keys. -/
theorem optVjoin_optVmeet_distrib {V : Type u} (cj cm : V → V → V)
    (hidem : ∀ x, cm x x = x) (habs1 : ∀ x y, cm (cj x y) x = x) (habs2 : ∀ x y, cm x (cj x y) = x)
    (hdist : ∀ x y z, cj x (cm y z) = cm (cj x y) (cj x z)) (oa ob oc : Option V) :
    optVjoin cj oa (optVmeet cm ob oc) = optVmeet cm (optVjoin cj oa ob) (optVjoin cj oa oc) := by
  cases oa <;> cases ob <;> cases oc <;> simp only [optVmeet, optVjoin] <;>
    first | rfl | rw [hidem] | rw [habs1] | rw [habs2] | rw [hdist]

namespace Node

theorem get_mem (n : Node α) (i : UInt32) (h : testBit n.positionsMask i = true) :
    n.get i h ∈ n.elements := Array.getElem_mem _

/-! ### How `get?` reads a slot

The two reductions of `get?`'s dependent `if`, plus the merge accumulator's reading. Nearly
every proof below probes nodes only through `get?`, so these are the workhorse rewrites. -/

/-- A present slot reads its `get` value through `get?`. -/
private theorem get?_eq_some_get (n : Node α) (i : UInt32) (h : testBit n.positionsMask i = true) :
    n.get? i = some (n.get i h) := by rw [Node.get?, dif_pos h]

/-- An absent slot reads `none`. -/
private theorem get?_eq_none_of_testBit (n : Node α) (i : UInt32) (h : testBit n.positionsMask i = false) :
    n.get? i = none := by rw [Node.get?, dif_neg (by rw [h]; simp)]

/-- The pre-sized accumulator `join`/`meet` start from reads `none` everywhere — its capacity is
only an allocation hint, so it is `empty` as a value. -/
private theorem get?_emptyWithCapacity (c : Nat) (i : UInt32) :
    (Node.emptyWithCapacity c : Node α).get? i = none :=
  get?_eq_none_of_testBit _ i (testBit_zero i)

/-! ### Emptiness and mask lemmas backing the leaf obligations

These support the "no empty leaf" side of the canonical-shape invariant (`PTree.WF`). The mask
helpers record how `insert`/`alter` move `positionsMask`; the emptiness facts they feed
(`isEmpty_insert`, `isEmpty_alter_invariant`, `eq_empty_of_isEmpty`) discharge the map leaf's
`LeafOps.insert_ne_empty`/`isEmpty_modify`/`eq_empty_of_isEmpty` obligations. -/

/-- `insert` sets exactly slot `i` of the mask — even when it was already present, since
`setBit` is idempotent (so an `insert` result is never empty). -/
private theorem positionsMask_insert {α} (n : Node α) (i : UInt32) (v : α) :
    (n.insert i v).positionsMask = setBit n.positionsMask i := by
  unfold Node.insert Node.alter
  split
  · rename_i htb
    split
    · simp only; exact (setBit_eq_of_testBit n.positionsMask i htb).symm
    · rename_i hfn; simp at hfn
  · rename_i htb
    split
    · rfl
    · rename_i hfn; simp at hfn

/-- An `insert` result is never empty. -/
theorem isEmpty_insert {α} (n : Node α) (i : UInt32) (v : α) : (n.insert i v).isEmpty = false := by
  unfold Node.isEmpty
  rw [positionsMask_insert]
  exact beq_eq_false_iff_ne.mpr (setBit_ne_zero n.positionsMask i)

/-- A present child comes from the elements array. -/
theorem mem_of_get? {α} (n : Node α) (i : UInt32) (c : α) (h : n.get? i = some c) :
    c ∈ n.elements := by
  unfold Node.get? at h
  split at h
  · rename_i htb
    rw [Option.some.injEq] at h
    exact h ▸ n.get_mem i htb
  · exact absurd h (by simp)

/-- A single-slot update whose callback preserves presence (`some ↦ some`, `none ↦ none`)
leaves the mask unchanged. Used to show `modify` preserves the node's shape. -/
private theorem positionsMask_alter_invariant {α} (n : Node α) (i : UInt32) (g : Option α → Option α)
    (hg : ∀ o : Option α, (g o).isSome = o.isSome) :
    (n.alter i g).positionsMask = n.positionsMask := by
  unfold Node.alter
  split
  · rename_i htb
    split
    · rfl
    · rename_i hfn
      have hsome := hg (some (n.get i htb))
      rw [hfn] at hsome; simp at hsome
  · rename_i htb
    split
    · rename_i a hfa
      have hsome := hg none
      rw [hfa] at hsome; simp at hsome
    · rfl

/-- A presence-preserving single-slot update leaves emptiness unchanged. -/
theorem isEmpty_alter_invariant {α} (n : Node α) (i : UInt32) (g : Option α → Option α)
    (hg : ∀ o : Option α, (g o).isSome = o.isSome) : (n.alter i g).isEmpty = n.isEmpty := by
  unfold Node.isEmpty
  rw [positionsMask_alter_invariant n i g hg]

/-- An empty node *is* `Node.empty`: a zero mask has popcount `0`, so by `elements_compact`
the element array is empty too, pinning down both data fields (the proof field is irrelevant).
This is the converse of `isEmpty` the collection layer needs to recover `c = empty`. -/
theorem eq_empty_of_isEmpty {α} (n : Node α) (h : n.isEmpty = true) : n = Node.empty := by
  obtain ⟨m, e, hc⟩ := n
  simp only [Node.isEmpty] at h
  have hm : m = 0 := eq_of_beq h
  subst hm
  have he : e = #[] := Array.size_eq_zero_iff.mp (by rw [hc]; rfl)
  subst he
  rfl

/-- `Nat.fold` congruence requiring step agreement only on the indices actually visited
(`i < n`). Backs `Node.ext`, whose element-array extraction folds agree only on in-range
slots (`UInt32.ofNat i < 32`). -/
private theorem fold_step_congr_lt {β : Type v} (stepf stepg : β → Nat → β) (initf initg : β)
    (hinit : initf = initg) (n : Nat) (hstep : ∀ acc i, i < n → stepf acc i = stepg acc i) :
    Nat.fold n (fun i _ acc => stepf acc i) initf
      = Nat.fold n (fun i _ acc => stepg acc i) initg := by
  subst hinit
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Nat.fold_succ, Nat.fold_succ, ih (fun acc i hi => hstep acc i (Nat.lt_succ_of_lt hi)),
        hstep _ k (Nat.lt_succ_self k)]

/-! ### `get?` characterization and node extensionality

These support the `get?`-based denotational semantics the `NatCollection` lattice laws
(associativity, …) are proved against. `get?_join` reads off a `join` result slot-by-slot as a
value-level merge `optJoin`; `Node.ext` recovers a node from its `get?`. Slot indices are always
`< 32` here (they come from 5-bit `chunk`s), matching `UInt32`'s mod-32 shift semantics. -/

@[simp] theorem get?_empty (i : UInt32) : (Node.empty : Node α).get? i = none :=
  get?_eq_none_of_testBit _ i (testBit_zero i)

/-- A slot is present in the mask exactly when `get?` reports a value. -/
theorem testBit_eq_isSome_get? (n : Node α) (i : UInt32) :
    testBit n.positionsMask i = (n.get? i).isSome := by
  unfold Node.get?
  split <;> rename_i h <;> simp_all

theorem isEmpty_eq_false_of_get? (n : Node α) (s : UInt32) (h : (n.get? s).isSome) :
    Node.isEmpty n = false := by
  have htb : testBit n.positionsMask s = true := by rw [testBit_eq_isSome_get?]; exact h
  show (n.positionsMask == 0) = false
  apply beq_eq_false_iff_ne.mpr
  intro h0; rw [h0, testBit_zero] at htb; exact absurd htb (by simp)

/-- A non-empty node has a present slot (`< 32`). -/
private theorem exists_get?_of_isEmpty_false (n : Node α) (h : Node.isEmpty n = false) :
    ∃ i, i < 32 ∧ (n.get? i).isSome := by
  refine Classical.byContradiction fun hno => ?_
  have hzero : n.positionsMask = 0 := by
    apply eq_of_testBit_eq
    intro i hi
    rw [testBit_zero, testBit_eq_isSome_get? n i]
    cases hb : (n.get? i).isSome with
    | false => rfl
    | true => exact absurd ⟨i, hi, hb⟩ hno
  simp [Node.isEmpty, hzero] at h

/-- `none.elim` reduces to its default. Stated as a generic lemma (proved once, on abstract
arguments) so `elements_eq_extract` can `rw` with it instead of forcing the kernel to reduce
`Option.elim` applied to a large `Array.extract` term — which trips the kernel's recursion guard. -/
private theorem optElim_none {β : Type v} (a : β) (f : α → β) :
    (none : Option α).elim a f = a := rfl

/-- `some.elim` reduces to the function applied (the `some` companion of `optElim_none`). -/
private theorem optElim_some {β : Type v} (x : α) (a : β) (f : α → β) :
    (some x).elim a f = f x := rfl

/-- Forward extraction: a node's element array is its present children read out in ascending slot
order via `get?`. The fold appends each present slot's child; the invariant tracks the built prefix
as `elements.extract 0 (arrayIndex …)`, reaching the whole array at the slot-31 boundary
(`popCount_split31`, since `UInt32`'s `lowerMask` wraps at 32). Backs `Node.ext`. -/
private theorem elements_eq_extract (n : Node α) :
    n.elements
      = Nat.fold 32 (fun s _ acc => (n.get? (UInt32.ofNat s)).elim acc (fun c => acc.push c)) #[] := by
  have htoNat : ∀ j : Nat, j < 32 → (UInt32.ofNat j).toNat = j :=
    fun j hj => UInt32.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hj (by decide))
  have h0eq : (UInt32.ofNat 0 : UInt32) = 0 := by
    apply UInt32.toNat_inj.mp
    rw [htoNat 0 (by omega), show ((0 : UInt32).toNat) = 0 from rfl]
  have h31eq : (UInt32.ofNat 31 : UInt32) = 31 := by
    apply UInt32.toNat_inj.mp
    rw [htoNat 31 (by omega), show ((31 : UInt32).toNat) = 31 from rfl]
  have inv : ∀ m, m ≤ 31 →
      Nat.fold m (fun s _ acc => (n.get? (UInt32.ofNat s)).elim acc (fun c => acc.push c)) #[]
        = n.elements.extract 0 (arrayIndex n.positionsMask (UInt32.ofNat m)) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.fold_zero,
          show arrayIndex n.positionsMask (UInt32.ofNat 0) = 0 from by
            rw [h0eq]
            show popCount (n.positionsMask &&& lowerMask 0) = 0
            rw [show n.positionsMask &&& lowerMask 0 = 0 from by unfold lowerMask; bv_decide]
            rfl,
          Array.extract_eq_empty_of_le (by omega)]
    | succ k ih =>
      intro hk1
      have hiu : (UInt32.ofNat k) < 31 := by
        rw [UInt32.lt_iff_toNat_lt, htoNat k (by omega),
            show (31 : UInt32).toNat = 31 from by decide]; omega
      have hofs : UInt32.ofNat (k + 1) = UInt32.ofNat k + 1 := by
        apply UInt32.toNat_inj.mp
        rw [htoNat (k + 1) (by omega), UInt32.toNat_add, htoNat k (by omega),
            show ((1 : UInt32).toNat) = 1 from rfl, show (2 : Nat) ^ 32 = 4294967296 from rfl,
            Nat.mod_eq_of_lt (by omega)]
      rw [Nat.fold_succ, ih (by omega), hofs, arrayIndex_succ n.positionsMask (UInt32.ofNat k) hiu]
      by_cases htb : testBit n.positionsMask (UInt32.ofNat k) = true
      · have hAlt : arrayIndex n.positionsMask (UInt32.ofNat k) < n.elements.size := by
          rw [n.elements_compact]; exact arrayIndex_lt _ _ htb
        rw [get?_eq_some_get n (UInt32.ofNat k) htb, optElim_some, if_pos htb,
            show n.get (UInt32.ofNat k) htb
              = n.elements[arrayIndex n.positionsMask (UInt32.ofNat k)]'hAlt from rfl,
            Array.push_extract_getElem hAlt, Nat.min_eq_left (Nat.zero_le _)]
      · rw [get?_eq_none_of_testBit n (UInt32.ofNat k) (by simpa using htb),
            optElim_none, if_neg htb, Nat.add_zero]
  show n.elements
      = Nat.fold (31 + 1) (fun s _ acc => (n.get? (UInt32.ofNat s)).elim acc (fun c => acc.push c)) #[]
  rw [Nat.fold_succ, inv 31 (Nat.le_refl 31)]
  by_cases htb : testBit n.positionsMask (UInt32.ofNat 31) = true
  · have hAlt : arrayIndex n.positionsMask (UInt32.ofNat 31) < n.elements.size := by
      rw [n.elements_compact]; exact arrayIndex_lt _ _ htb
    have hsize : arrayIndex n.positionsMask (UInt32.ofNat 31) + 1 = n.elements.size := by
      rw [n.elements_compact]
      show popCount (n.positionsMask &&& lowerMask (UInt32.ofNat 31)) + 1 = popCount n.positionsMask
      rw [h31eq, popCount_split31 n.positionsMask, if_pos (by rw [← h31eq]; exact htb)]
    rw [get?_eq_some_get n (UInt32.ofNat 31) htb, optElim_some,
        show n.get (UInt32.ofNat 31) htb
          = n.elements[arrayIndex n.positionsMask (UInt32.ofNat 31)]'hAlt from rfl,
        Array.push_extract_getElem hAlt, Nat.min_eq_left (Nat.zero_le _), hsize,
        Array.extract_eq_self_of_le (Nat.le_refl _)]
  · have hsize : arrayIndex n.positionsMask (UInt32.ofNat 31) = n.elements.size := by
      rw [n.elements_compact]
      show popCount (n.positionsMask &&& lowerMask (UInt32.ofNat 31)) = popCount n.positionsMask
      rw [h31eq, popCount_split31 n.positionsMask, if_neg (by rw [← h31eq]; exact htb), Nat.add_zero]
    rw [get?_eq_none_of_testBit n (UInt32.ofNat 31) (by simpa using htb),
        optElim_none, hsize, Array.extract_eq_self_of_le (Nat.le_refl _)]

/-- Node extensionality: a node is determined by its `get?` at slots `0..31`. Masks agree by
`testBit_eq_isSome_get?`; the element arrays agree because each is `get?`-extracted
(`elements_eq_extract`) and the extractions step-by-step agree. -/
theorem ext {a b : Node α} (h : ∀ i, i < 32 → a.get? i = b.get? i) : a = b := by
  have hmask : a.positionsMask = b.positionsMask := by
    apply eq_of_testBit_eq
    intro i hi
    rw [testBit_eq_isSome_get? a i, testBit_eq_isSome_get? b i, h i hi]
  have hel : a.elements = b.elements := by
    rw [elements_eq_extract a, elements_eq_extract b]
    refine fold_step_congr_lt _ _ _ _ rfl 32 ?_
    intro acc s hs
    have hsu : (UInt32.ofNat s) < 32 := by
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hs (by decide)),
          show (32 : UInt32).toNat = 32 from by decide]; omega
    rw [h (UInt32.ofNat s) hsu]
  obtain ⟨ma, ea, hca⟩ := a; obtain ⟨mb, eb, hcb⟩ := b
  simp only at hmask hel
  subst hmask; subst hel; rfl

/-! ### `map`: the functorial action on values

`map f` rewrites every stored child with `f`, leaving the slot structure (`positionsMask`,
array length, which slots are present) untouched. These are the building blocks for the `NatMap`
`Functor`/`LawfulFunctor` instance: the mask facts feed canonical-shape preservation, and
`map_id`/`map_comp`/`get?_map` are the functor laws at the leaf level. -/

/-- `map` preserves the slot mask (it only rewrites values). -/
@[simp] theorem map_positionsMask {β : Type v} (f : α → β) (n : Node α) :
    (n.map f).positionsMask = n.positionsMask := rfl

/-- `map` preserves emptiness (the mask is unchanged). -/
@[simp] theorem isEmpty_map {β : Type v} (f : α → β) (n : Node α) :
    (n.map f).isEmpty = n.isEmpty := rfl

/-- Mapping the identity is the identity. -/
@[simp, grind =]
theorem map_id (n : Node α) : n.map id = n := by
  obtain ⟨m, e, hc⟩ := n
  simp only [Node.map, Array.map_id]

/-- Mapping a composition is the composition of maps. -/
theorem map_comp {β γ : Type v} (f : α → β) (g : β → γ) (n : Node α) :
    n.map (g ∘ f) = (n.map f).map g := by
  obtain ⟨m, e, hc⟩ := n
  simp only [Node.map, Array.map_map]

/-- `get?` reads a `map` pointwise: looking up a slot applies `f` to whatever was there. -/
theorem get?_map {β : Type v} (f : α → β) (n : Node α) (i : UInt32) :
    (n.map f).get? i = (n.get? i).map f := by
  cases hb : testBit n.positionsMask i with
  | true =>
    rw [get?_eq_some_get n i hb, get?_eq_some_get (n.map f) i hb]
    show some ((n.map f).get i hb) = some (f (n.get i hb))
    congr 1
    show (n.elements.map f)[arrayIndex n.positionsMask i]'_ = f (n.elements[arrayIndex n.positionsMask i]'_)
    rw [Array.getElem_map]
  | false =>
    rw [get?_eq_none_of_testBit n i hb, get?_eq_none_of_testBit (n.map f) i hb]
    simp

/-- **`restrictsLoop` characterization**: the loop AND-folds `optRel`'s per-slot verdict over the
present slots of `m`, so it is `true` exactly when the seed `acc` is and `optRel rel` relates the
two nodes' `get?` readings at every present slot of `m`. Proved by well-founded recursion on `m`
— the present-slot bit-scan analogue of the old `restricts_fold_iff`. -/
private theorem restrictsLoop_iff {α} (rel : α → α → Bool) (a b : Node α) (m : UInt32) (acc : Bool) :
    restrictsLoop rel a b m acc = true ↔
      (acc = true ∧ ∀ i : UInt32, i < 32 → testBit m i = true →
        optRel rel (a.get? i) (b.get? i) = true) := by
  by_cases hm : m = 0
  · subst hm
    rw [restrictsLoop, dif_pos rfl]
    constructor
    · exact fun h => ⟨h, fun i _ hbit => by rw [testBit_zero] at hbit; exact absurd hbit (by simp)⟩
    · exact fun h => h.1
  · rw [restrictsLoop, dif_neg hm]
    have hi_lt : lowestSetIdx m < 32 := lowestSetIdx_lt m hm
    have hi_mem : testBit m (lowestSetIdx m) = true := testBit_lowestSetIdx m hm
    rw [restrictsLoop_iff rel a b (clearLowest m)
          (acc && optRel rel (a.get? (lowestSetIdx m)) (b.get? (lowestSetIdx m)))]
    constructor
    · rintro ⟨hand, hrest⟩
      rw [Bool.and_eq_true] at hand
      refine ⟨hand.1, fun i hi hbit => ?_⟩
      by_cases hji : i = lowestSetIdx m
      · subst hji; exact hand.2
      · exact hrest i hi (by rw [testBit_clearLowest_of_ne m i hi hji]; exact hbit)
    · rintro ⟨hacc, hall⟩
      refine ⟨by rw [Bool.and_eq_true]; exact ⟨hacc, hall (lowestSetIdx m) hi_lt hi_mem⟩,
              fun i hi hbit => hall i hi (testBit_of_clearLowest m i hbit)⟩
termination_by m.toNat
decreasing_by exact toNat_clearLowest_lt m hm

/-- **`restricts` characterization**: a node restricts another exactly when, slot by slot, the
left's value forces a related right value (`optRel`). The mask-subset guard is the "present on
the left ⇒ present on the right" half; the fold is the "`rel` on shared values" half. The
denotational reading `restricts` transitivity is proved against. -/
theorem restricts_iff {α} (rel : α → α → Bool) (a b : Node α) :
    Node.restricts rel a b = true ↔ ∀ i : UInt32, i < 32 → optRel rel (a.get? i) (b.get? i) = true := by
  -- the mask subset condition `M` is exactly "present on the left ⇒ present on the right"
  have hMD : (a.positionsMask &&& b.positionsMask = a.positionsMask)
      ↔ ∀ i : UInt32, i < 32 → testBit a.positionsMask i = true → testBit b.positionsMask i = true := by
    constructor
    · intro hM i _ hai
      have hbit : testBit (a.positionsMask &&& b.positionsMask) i = testBit a.positionsMask i := by rw [hM]
      rw [testBit_and, hai] at hbit; simpa using hbit
    · intro hD
      apply eq_of_testBit_eq
      intro i hi
      rw [testBit_and]
      cases hai : testBit a.positionsMask i with
      | false => simp
      | true => simp [hD i hi hai]
  unfold Node.restricts
  split
  · -- guard fired: the masks are not in subset position, so the domain half already fails
    rename_i hguard
    have hne : a.positionsMask &&& b.positionsMask ≠ a.positionsMask := by simpa [bne] using hguard
    constructor
    · intro h; exact absurd h (by simp)
    · intro hall
      refine absurd (hMD.mpr ?_) hne
      intro iu hiu haiu
      have hoptiu := hall iu hiu
      rw [get?_eq_some_get a iu haiu] at hoptiu
      cases hgb : b.get? iu with
      | some y => rw [testBit_eq_isSome_get?, hgb]; rfl
      | none => rw [hgb] at hoptiu; simp [optRel] at hoptiu
  · -- guard did not fire: masks are in subset position; the loop checks `optRel` on every present
    -- slot of `a` — the only slots where `restricts` is non-vacuous
    rw [restrictsLoop_iff]
    constructor
    · -- the loop's "optRel on a's present slots" extends to all keys: an absent left slot is vacuous
      rintro ⟨_, hloop⟩ iu hiu
      cases hga : a.get? iu with
      | none => rfl
      | some x =>
        have haiu : testBit a.positionsMask iu = true := by rw [testBit_eq_isSome_get?, hga]; rfl
        have h := hloop iu hiu haiu
        rw [hga] at h
        exact h
    · intro hO
      exact ⟨rfl, fun iu hiu _ => hO iu hiu⟩

/-- `restricts` is reflexive when `rel` is reflexive on the stored children: slot by slot, a
node trivially coincides with itself, and `rel`-reflexivity discharges the shared-value check. -/
theorem restricts_self {α} (rel : α → α → Bool) (n : Node α)
    (hrel : ∀ x ∈ n.elements, rel x x = true) :
    Node.restricts rel n n = true := by
  rw [restricts_iff]
  intro i _
  cases hg : n.get? i with
  | none => rfl
  | some x => exact hrel x (mem_of_get? n i x hg)

/-- `get?` as a (proof-free) `getElem?` on the compact array. Lets `get?` lemmas reason about
the underlying `Array` operations without carrying `Node.get`'s in-bounds proof. -/
private theorem get?_eq_getElem? (n : Node α) (j : UInt32) :
    n.get? j = if testBit n.positionsMask j then n.elements[arrayIndex n.positionsMask j]? else none := by
  unfold Node.get?
  by_cases h : testBit n.positionsMask j = true
  · rw [dif_pos h, if_pos h, Node.get,
        Array.getElem?_eq_getElem (by rw [n.elements_compact]; exact arrayIndex_lt _ _ h)]
  · rw [dif_neg h, if_neg h]

/-- `get?` after `insert`: slot `i` reads the new value `v`, every other slot is unchanged.
Slots are `< 32` (5-bit chunks); the proof tracks how the compact `arrayIndex` of each slot
moves under the `set!`/`insertIdx` that `insert` performs. -/
theorem get?_insert (n : Node α) (i : UInt32) (v : α) (j : UInt32) (hi : i < 32) (hj : j < 32) :
    (n.insert i v).get? j = if j = i then some v else n.get? j := by
  have hsize : arrayIndex n.positionsMask i ≤ n.elements.size := by
    rw [n.elements_compact]; exact arrayIndex_le _ _
  have hidx_i_lt : testBit n.positionsMask i = true → arrayIndex n.positionsMask i < n.elements.size :=
    fun h => by rw [n.elements_compact]; exact arrayIndex_lt _ _ h
  rw [get?_eq_getElem? (n.insert i v) j, get?_eq_getElem? n j]
  cases hpres : testBit n.positionsMask i with
  | true =>
    -- in-place overwrite; mask unchanged (set bit already set)
    have hmask : (n.insert i v).positionsMask = n.positionsMask := by
      rw [positionsMask_insert, setBit_eq_of_testBit _ _ hpres]
    have hel : (n.insert i v).elements = n.elements.set! (arrayIndex n.positionsMask i) v := by
      unfold Node.insert Node.alter; simp only []
      split
      · rfl
      · rename_i htb; rw [hpres] at htb; exact absurd htb (by decide)
    rw [hmask, hel, Array.set!_eq_setIfInBounds]
    by_cases hji : j = i
    · subst hji
      rw [if_pos hpres, Array.getElem?_setIfInBounds, if_pos rfl, if_pos (hidx_i_lt hpres)]
      simp
    · rw [if_neg hji]
      by_cases hbj : testBit n.positionsMask j = true
      · rw [if_pos hbj, if_pos hbj, Array.getElem?_setIfInBounds,
            if_neg (arrayIndex_inj n.positionsMask i j hi hj hpres hbj (Ne.symm hji))]
      · rw [if_neg hbj, if_neg hbj]
  | false =>
    -- fresh slot inserted; index shifts by one above `i`
    have hmask : (n.insert i v).positionsMask = setBit n.positionsMask i := positionsMask_insert n i v
    have hel : (n.insert i v).elements = n.elements.insertIdx (arrayIndex n.positionsMask i) v hsize := by
      unfold Node.insert Node.alter; simp only []
      split
      · rename_i htb; rw [hpres] at htb; exact absurd htb (by decide)
      · exact dif_pos hsize
    rw [hmask, hel]
    by_cases hji : j = i
    · subst hji
      rw [if_pos (by rw [testBit_setBit _ _ _ hi hj]; simp),
          arrayIndex_setBit_self, Array.getElem?_insertIdx_self hsize]
      simp
    · rw [if_neg hji]
      have htbsb : testBit (setBit n.positionsMask i) j = testBit n.positionsMask j := by
        rw [testBit_setBit _ _ _ hi hj]; simp [beq_eq_false_iff_ne.mpr (Ne.symm hji)]
      rw [htbsb]
      by_cases hbj : testBit n.positionsMask j = true
      · rw [if_pos hbj, if_pos hbj]
        -- compare slot j against i to place the read in the shifted array
        rcases UInt32.lt_or_lt_of_ne (Ne.symm hji) with hgt | hlt
        · -- i < j : the index shifts up by one
          rw [arrayIndex_setBit_of_gt _ _ _ hi hj hgt hpres, Array.getElem?_insertIdx hsize,
              if_neg (by have := arrayIndex_le_of_le n.positionsMask i j hi hj (UInt32.le_of_lt hgt); omega),
              if_neg (by have := arrayIndex_le_of_le n.positionsMask i j hi hj (UInt32.le_of_lt hgt); omega),
              Nat.add_sub_cancel]
        · -- j < i : the index is below the insertion point, unchanged
          rw [arrayIndex_setBit_of_le _ _ _ hi hj (UInt32.le_of_lt hlt),
              Array.getElem?_insertIdx_of_lt hsize (arrayIndex_lt_of_lt _ j i hj hi hbj hlt)]
      · rw [if_neg hbj, if_neg hbj]

/-- `get?` after `erase`: slot `i` reads `none`, every other slot is unchanged — `get?_insert`'s
erase mirror. An absent slot makes `erase` a no-op; a present slot `eraseIdx`s its element, and
the compact `arrayIndex` of every higher slot drops by one. -/
theorem get?_erase (n : Node α) (i j : UInt32) (hi : i < 32) (hj : j < 32) :
    (n.erase i).get? j = if j = i then none else n.get? j := by
  cases hpres : testBit n.positionsMask i with
  | false =>
    -- absent slot: erase is a no-op, and slot `i` already reads `none`
    have herase : n.erase i = n := by
      unfold Node.erase Node.alter
      simp only []
      split
      · rename_i htb; rw [hpres] at htb; exact absurd htb (by decide)
      · rfl
    rw [herase]
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl, get?_eq_getElem?, if_neg (by rw [hpres]; exact Bool.false_ne_true)]
    · rw [if_neg hji]
  | true =>
    have hidx_lt : arrayIndex n.positionsMask i < n.elements.size := by
      rw [n.elements_compact]; exact arrayIndex_lt _ _ hpres
    have hmask : (n.erase i).positionsMask = clearBit n.positionsMask i := by
      unfold Node.erase Node.alter
      simp only []
      split
      · rfl
      · rename_i htb; rw [hpres] at htb; exact absurd htb (by decide)
    have hel : (n.erase i).elements
        = n.elements.eraseIdx (arrayIndex n.positionsMask i) hidx_lt := by
      unfold Node.erase Node.alter
      simp only []
      split
      · exact dif_pos hidx_lt
      · rename_i htb; rw [hpres] at htb; exact absurd htb (by decide)
    rw [get?_eq_getElem? (n.erase i) j, get?_eq_getElem? n j, hmask, hel]
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl, if_neg (by rw [testBit_clearBit _ _ _ hi hi]; simp)]
    · rw [if_neg hji]
      have htbcb : testBit (clearBit n.positionsMask i) j = testBit n.positionsMask j := by
        rw [testBit_clearBit _ _ _ hi hj, beq_eq_false_iff_ne.mpr (fun hc => hji hc.symm),
            Bool.not_false, Bool.and_true]
      rw [htbcb]
      by_cases hbj : testBit n.positionsMask j = true
      · rw [if_pos hbj, if_pos hbj]
        rcases UInt32.lt_or_lt_of_ne (Ne.symm hji) with hgt | hlt
        · -- i < j : the read sits above the erasure point, its index dropped by one
          have hshift := arrayIndex_clearBit_of_gt n.positionsMask i j hi hj hgt hpres
          have hmono := arrayIndex_lt_of_lt n.positionsMask i j hi hj hpres hgt
          rw [Array.getElem?_eraseIdx hidx_lt, if_neg (by omega), ← hshift]
        · -- j < i : the read index is below the erasure point, unchanged
          rw [arrayIndex_clearBit_of_le _ _ _ hi hj (UInt32.le_of_lt hlt),
              Array.getElem?_eraseIdx hidx_lt,
              if_pos (arrayIndex_lt_of_lt _ j i hj hi hbj hlt)]
      · rw [if_neg hbj, if_neg hbj]

/-- `get?` of a `mergeLoop` result, given the step characterized at the slot it visits (`hself`,
which the fresh accumulator validates) and off it (`hother`). The loop invariant: visiting the
present slots of `m` fills each with `G`, leaving every other slot at the accumulator's value. The
single proof both `get?_join` and `get?_meet` are built on. -/
private theorem get?_mergeLoop {α} {step : Node α → UInt32 → Node α} {G : UInt32 → Option α}
    (hself : ∀ (acc : Node α) (i : UInt32), i < 32 → acc.get? i = none → (step acc i).get? i = G i)
    (hother : ∀ (acc : Node α) (i j : UInt32), i < 32 → j < 32 → j ≠ i →
                (step acc i).get? j = acc.get? j)
    (m : UInt32) (acc : Node α) (j : UInt32) (hj : j < 32)
    (hfresh : ∀ s, s < 32 → testBit m s = true → acc.get? s = none) :
    (mergeLoop step m acc).get? j = if testBit m j = true then G j else acc.get? j := by
  by_cases hm : m = 0
  · rw [mergeLoop, dif_pos hm, hm, testBit_zero, if_neg Bool.false_ne_true]
  · rw [mergeLoop, dif_neg hm]
    have hi_lt : lowestSetIdx m < 32 := lowestSetIdx_lt m hm
    have hi_mem : testBit m (lowestSetIdx m) = true := testBit_lowestSetIdx m hm
    have hacc'_fresh : ∀ s, s < 32 → testBit (clearLowest m) s = true →
        (step acc (lowestSetIdx m)).get? s = none := by
      intro s hs hsmem
      have hs_ne : s ≠ lowestSetIdx m := by
        intro hsi; rw [hsi, testBit_clearLowest_self m hm] at hsmem; exact absurd hsmem (by simp)
      rw [hother acc (lowestSetIdx m) s hi_lt hs hs_ne]
      exact hfresh s hs (testBit_of_clearLowest m s hsmem)
    rw [get?_mergeLoop hself hother (clearLowest m) (step acc (lowestSetIdx m)) j hj hacc'_fresh]
    by_cases hji : j = lowestSetIdx m
    · have hcl : testBit (clearLowest m) j = false := by rw [hji]; exact testBit_clearLowest_self m hm
      have hmm : testBit m j = true := by rw [hji]; exact hi_mem
      rw [hcl, hmm, if_neg Bool.false_ne_true, if_pos rfl, hji]
      exact hself acc (lowestSetIdx m) hi_lt (hfresh (lowestSetIdx m) hi_lt hi_mem)
    · rw [testBit_clearLowest_of_ne m j hj hji, hother acc (lowestSetIdx m) j hi_lt hj hji]
termination_by m.toNat
decreasing_by exact toNat_clearLowest_lt m hm

/-- `get?` of `joinStep` at the slot it visits: the merged value `optJoin combine (a? i) (b? i)`,
provided the accumulator is fresh there. The `hself` obligation of `get?_mergeLoop` for `join`. -/
private theorem joinStep_get?_self (combine : α → α → Option α) (a b acc : Node α) (i : UInt32)
    (hi : i < 32) (hfresh : acc.get? i = none) :
    (joinStep combine a b acc i).get? i = optJoin combine (a.get? i) (b.get? i) := by
  unfold joinStep
  split
  · rename_i h1 h2
    rw [get?_eq_some_get a i h1, get?_eq_some_get b i h2]
    simp only [optJoin]
    split
    · rename_i v hv; rw [get?_insert _ _ _ _ hi hi, if_pos rfl, hv]
    · rename_i hv; rw [hfresh, hv]
  · rename_i h1 h2
    rw [get?_eq_some_get a i h1, get?_eq_none_of_testBit b i h2]
    simp only [optJoin]; rw [get?_insert _ _ _ _ hi hi, if_pos rfl]
  · rename_i h1 h2
    rw [get?_eq_none_of_testBit a i h1, get?_eq_some_get b i h2]
    simp only [optJoin]; rw [get?_insert _ _ _ _ hi hi, if_pos rfl]
  · rename_i h1 h2
    rw [get?_eq_none_of_testBit a i h1, get?_eq_none_of_testBit b i h2]
    simp only [optJoin]; exact hfresh

/-- `get?` of `joinStep` off the slot it visits: unchanged from `acc`. The `hother` obligation of
`get?_mergeLoop` for `join` (no freshness needed). -/
private theorem joinStep_get?_other (combine : α → α → Option α) (a b acc : Node α) (i j : UInt32)
    (hi : i < 32) (hj : j < 32) (hne : j ≠ i) :
    (joinStep combine a b acc i).get? j = acc.get? j := by
  unfold joinStep
  split
  · rename_i h1 h2
    split
    · rename_i v hv; rw [get?_insert _ _ _ _ hi hj, if_neg hne]
    · rfl
  · rename_i h1 h2; rw [get?_insert _ _ _ _ hi hj, if_neg hne]
  · rename_i h1 h2; rw [get?_insert _ _ _ _ hi hj, if_neg hne]
  · rfl

/-- `get?` of a `Node.join`: a value-level merge of the two lookups. Specializes the generic
`get?_mergeLoop` invariant to `join` (step `joinStep`, mask the union `a ||| b`), then reads off
the result: a slot in the union mask gets `optJoin`, and a slot outside it is `none` on both sides
(the empty accumulator and the value-level merge of two absent lookups). -/
theorem get?_join (combine : α → α → Option α) (a b : Node α) (j : UInt32) (hj : j < 32) :
    (Node.join combine a b).get? j = optJoin combine (a.get? j) (b.get? j) := by
  unfold Node.join
  rw [get?_mergeLoop (joinStep_get?_self combine a b) (joinStep_get?_other combine a b)
        (a.positionsMask ||| b.positionsMask)
        (Node.emptyWithCapacity (popCount (a.positionsMask ||| b.positionsMask))) j hj
        (fun s _ _ => get?_emptyWithCapacity _ s)]
  by_cases hjm : testBit (a.positionsMask ||| b.positionsMask) j = true
  · rw [if_pos hjm]
  · rw [if_neg hjm]
    rw [testBit_or, Bool.or_eq_true, not_or] at hjm
    obtain ⟨hna, hnb⟩ := hjm
    rw [get?_eq_none_of_testBit a j (by simpa using hna),
        get?_eq_none_of_testBit b j (by simpa using hnb)]
    exact get?_emptyWithCapacity _ j

/-- `get?` of `filterMapStep` at the slot it visits: the filtered-and-mapped value, provided the
accumulator is fresh there. The `hself` obligation of `get?_mergeLoop` for `filterMap`. -/
private theorem filterMapStep_get?_self (f : UInt32 → α → Option α) (n : Node α)
    (acc : Node α) (i : UInt32) (hi : i < 32) (hfresh : acc.get? i = none) :
    (filterMapStep f n acc i).get? i
      = match n.get? i with
        | some v => f i v
        | none => none := by
  unfold filterMapStep
  split
  · rename_i h
    rw [get?_eq_some_get n i h]
    split
    · rename_i y hy
      rw [get?_insert _ _ _ _ hi hi, if_pos rfl]
      exact hy.symm
    · rename_i hy
      rw [hfresh]
      exact hy.symm
  · rename_i h
    rw [get?_eq_none_of_testBit n i h]
    exact hfresh

/-- `get?` of `filterMapStep` off the slot it visits: unchanged from `acc`. The `hother`
obligation of `get?_mergeLoop` for `filterMap`. -/
private theorem filterMapStep_get?_other (f : UInt32 → α → Option α) (n : Node α)
    (acc : Node α) (i j : UInt32) (hi : i < 32) (hj : j < 32) (hne : j ≠ i) :
    (filterMapStep f n acc i).get? j = acc.get? j := by
  unfold filterMapStep
  split
  · split
    · rw [get?_insert _ _ _ _ hi hj, if_neg hne]
    · rfl
  · rfl

/-- `get?` of a `filterMap`: the lookup, filtered and mapped value-wise. Specializes
`get?_mergeLoop` (step `filterMapStep`, mask `n`'s own); a slot outside the mask is `none` on
both sides. -/
theorem get?_filterMap (f : UInt32 → α → Option α) (n : Node α) (j : UInt32) (hj : j < 32) :
    (Node.filterMap f n).get? j
      = match n.get? j with
        | some v => f j v
        | none => none := by
  unfold Node.filterMap
  rw [get?_mergeLoop (filterMapStep_get?_self f n) (filterMapStep_get?_other f n)
        n.positionsMask (Node.emptyWithCapacity (popCount n.positionsMask)) j hj
        (fun s _ _ => get?_emptyWithCapacity _ s)]
  by_cases hjm : testBit n.positionsMask j = true
  · rw [if_pos hjm]
  · rw [if_neg hjm, get?_eq_none_of_testBit n j (by simpa using hjm)]
    exact get?_emptyWithCapacity _ j

/-- Associativity of `Node.join` for a combine that merges associatively at every slot. Both sides
agree at every `get?` slot: `get?_join` reduces each to the nested value-level merge `optJoin`, and
`hassoc` is exactly its associativity per slot; `Node.ext` then concludes. -/
theorem join_assoc (combine : α → α → Option α) (a b d : Node α)
    (hassoc : ∀ s, s < 32 → optJoin combine (optJoin combine (a.get? s) (b.get? s)) (d.get? s)
                          = optJoin combine (a.get? s) (optJoin combine (b.get? s) (d.get? s))) :
    Node.join combine (Node.join combine a b) d = Node.join combine a (Node.join combine b d) := by
  apply Node.ext
  intro i hi
  rw [get?_join combine (Node.join combine a b) d i hi, get?_join combine a b i hi,
      get?_join combine a (Node.join combine b d) i hi, get?_join combine b d i hi]
  exact hassoc i hi

/-- Joining (with a total, never-pruning combine) onto a non-empty node stays non-empty: the
present slot of `a` survives in the result (`get?_join`). Backs the leaf `isEmpty_join` law for
maps. -/
theorem isEmpty_join_left (c : α → α → α) (a b : Node α) (hne : Node.isEmpty a = false) :
    Node.isEmpty (Node.join (fun x y => some (c x y)) a b) = false := by
  obtain ⟨s, hs, hsome⟩ := exists_get?_of_isEmpty_false a hne
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
  apply isEmpty_eq_false_of_get? _ s
  rw [get?_join _ _ _ _ hs, hx]
  cases b.get? s <;> simp [optJoin]

/-- The value-level merge of a *total* (never-pruning) combine is associative when the combine is.
The per-slot obligation of `join_assoc` for maps. -/
theorem optJoin_someC_assoc (c : α → α → α) (hc : ∀ x y z, c (c x y) z = c x (c y z))
    (oa ob od : Option α) :
    optJoin (fun x y => some (c x y)) (optJoin (fun x y => some (c x y)) oa ob) od
      = optJoin (fun x y => some (c x y)) oa (optJoin (fun x y => some (c x y)) ob od) := by
  rcases oa with _ | x <;> rcases ob with _ | y <;> rcases od with _ | z <;> simp only [optJoin]
  rw [hc]

/-! ### `get?` characterization of `meet`, and commutativity

The `meet` analogue of the `join` `get?` block above. `optMeet` is the value-level intersection:
a slot survives only if present on *both* sides (and the `combine` does not prune it). `get?_meet`
reads off a `meet` result slot-by-slot via the same `get?_mergeLoop` invariant. Commutativity of
both operations then falls out of `Node.ext` + `get?_join`/`get?_meet`. -/

/-- `get?` of `meetStep` at the slot it visits: `optMeet combine (a? i) (b? i)` (the slot survives
only if present on both sides), provided the accumulator is fresh there. The `hself` obligation of
`get?_mergeLoop` for `meet`. -/
private theorem meetStep_get?_self (combine : α → α → Option α) (a b acc : Node α) (i : UInt32)
    (hi : i < 32) (hfresh : acc.get? i = none) :
    (meetStep combine a b acc i).get? i = optMeet combine (a.get? i) (b.get? i) := by
  unfold meetStep
  split
  · rename_i h1 h2
    rw [get?_eq_some_get a i h1, get?_eq_some_get b i h2]
    simp only [optMeet]
    split
    · rename_i v hv; rw [get?_insert _ _ _ _ hi hi, if_pos rfl, hv]
    · rename_i hv; rw [hfresh, hv]
  · rename_i h1 h2
    rw [get?_eq_none_of_testBit b i h2, hfresh]
    cases a.get? i <;> rfl
  · rename_i h1 h2
    rw [get?_eq_none_of_testBit a i h1, hfresh]
    simp only [optMeet]
  · rename_i h1 h2
    rw [get?_eq_none_of_testBit a i h1, hfresh]
    simp only [optMeet]

/-- `get?` of `meetStep` off the slot it visits: unchanged from `acc`. The `hother` obligation of
`get?_mergeLoop` for `meet`. -/
private theorem meetStep_get?_other (combine : α → α → Option α) (a b acc : Node α) (i j : UInt32)
    (hi : i < 32) (hj : j < 32) (hne : j ≠ i) :
    (meetStep combine a b acc i).get? j = acc.get? j := by
  unfold meetStep
  split
  · rename_i h1 h2
    split
    · rename_i v hv; rw [get?_insert _ _ _ _ hi hj, if_neg hne]
    · rfl
  · rfl
  · rfl
  · rfl

/-- `get?` of a `Node.meet`: a value-level intersection of the two lookups. Specializes
`get?_mergeLoop` to `meet` (step `meetStep`, mask the intersection `a &&& b`); a slot outside the
intersection mask is absent on at least one side, so `optMeet` there is `none`. -/
theorem get?_meet (combine : α → α → Option α) (a b : Node α) (j : UInt32) (hj : j < 32) :
    (Node.meet combine a b).get? j = optMeet combine (a.get? j) (b.get? j) := by
  unfold Node.meet
  rw [get?_mergeLoop (meetStep_get?_self combine a b) (meetStep_get?_other combine a b)
        (a.positionsMask &&& b.positionsMask)
        (Node.emptyWithCapacity (popCount (a.positionsMask &&& b.positionsMask))) j hj
        (fun s _ _ => get?_emptyWithCapacity _ s)]
  by_cases hjm : testBit (a.positionsMask &&& b.positionsMask) j = true
  · rw [if_pos hjm]
  · rw [if_neg hjm, get?_emptyWithCapacity]
    have hfb : (testBit a.positionsMask j && testBit b.positionsMask j) = false := by
      rw [← testBit_and]; simpa using hjm
    cases ha : a.get? j with
    | none => simp [optMeet]
    | some x =>
      cases hb : b.get? j with
      | none => simp [optMeet]
      | some y =>
        exfalso
        have hta : testBit a.positionsMask j = true := by rw [testBit_eq_isSome_get?, ha]; rfl
        have htb : testBit b.positionsMask j = true := by rw [testBit_eq_isSome_get?, hb]; rfl
        rw [hta, htb] at hfb; simp at hfb

/-- `join` commutes when the combine is flipped: merging `a` into `b` with `f` equals merging `b`
into `a` with `f`'s arguments swapped. Both sides agree at every `get?` slot (`get?_join` reduces
each to `optJoin`, which `hfg` flips), so `Node.ext` concludes. -/
theorem join_comm {α} {f g : α → α → Option α} (a b : Node α) (hfg : ∀ x y, f x y = g y x) :
    Node.join f a b = Node.join g b a := by
  apply Node.ext
  intro i hi
  rw [get?_join f a b i hi, get?_join g b a i hi]
  cases a.get? i <;> cases b.get? i <;> simp only [optJoin] <;> first | rfl | exact hfg _ _

/-- `meet` commutes when the combine is flipped (the `meet` analogue of `join_comm`). -/
theorem meet_comm {α} {f g : α → α → Option α} (a b : Node α) (hfg : ∀ x y, f x y = g y x) :
    Node.meet f a b = Node.meet g b a := by
  apply Node.ext
  intro i hi
  rw [get?_meet f a b i hi, get?_meet g b a i hi]
  cases a.get? i <;> cases b.get? i <;> simp only [optMeet] <;> first | rfl | exact hfg _ _

/-- A node with all slots absent (`get? = none` everywhere on in-range slots) is empty. The
contrapositive of `exists_get?_of_isEmpty_false`. -/
private theorem isEmpty_of_get?_eq_none (n : Node α) (h : ∀ i, i < 32 → n.get? i = none) :
    Node.isEmpty n = true := by
  cases hne : Node.isEmpty n with
  | true => rfl
  | false =>
    obtain ⟨i, hi, hsome⟩ := exists_get?_of_isEmpty_false n hne
    rw [h i hi] at hsome
    exact absurd hsome (by simp)

/-- An empty node reads `none` at every slot. -/
theorem get?_eq_none_of_isEmpty (n : Node α) (h : Node.isEmpty n = true) (s : UInt32) :
    n.get? s = none := by
  have hmask : n.positionsMask = 0 := eq_of_beq (show (n.positionsMask == 0) = true from h)
  have hb := testBit_eq_isSome_get? n s
  rw [hmask, testBit_zero] at hb
  cases hg : n.get? s with
  | none => rfl
  | some v => rw [hg] at hb; simp at hb

/-- A single-slot update depends on the leaf only through its current value at that slot, so two
callbacks agreeing on `n.get? i` give the same result. -/
private theorem alter_congr (n : Node α) (i : UInt32) (f g : Option α → Option α)
    (h : f (n.get? i) = g (n.get? i)) : n.alter i f = n.alter i g := by
  unfold Node.alter
  split <;> rename_i hp
  · rw [get?_eq_some_get n i hp] at h
    rw [h]
  · rw [get?_eq_none_of_testBit n i hp] at h
    rw [h]

/-- When the callback yields a value, `alter` coincides with `insert` of that value (it only ever
inspects the current slot, which `insert` overwrites unconditionally). Lets the spine/lift bridges
reuse `get?_insert` for `alter`-built nodes whose callback never prunes. -/
theorem alter_eq_insert (n : Node α) (i : UInt32) (f : Option α → Option α) (w : α)
    (h : f (n.get? i) = some w) : n.alter i f = n.insert i w :=
  alter_congr n i f (fun _ => some w) (by rw [h])

/-- `get?` of an `alter` whose callback yields a value: slot `i` reads that value, every other slot
is unchanged (a corollary of `alter_eq_insert` + `get?_insert`). -/
private theorem get?_alter_of_some (n : Node α) (i : UInt32) (f : Option α → Option α) (w : α)
    (hfw : f (n.get? i) = some w) (j : UInt32) (hi : i < 32) (hj : j < 32) :
    (n.alter i f).get? j = if j = i then some w else n.get? j := by
  rw [alter_eq_insert n i f w hfw, get?_insert n i w j hi hj]

end Node

end NatCol
