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

namespace Node

/-- The empty node (no slots present), backed by a zero-capacity array. -/
def empty : Node α := ⟨0, Array.emptyWithCapacity 0, by simp [show popCount 0 = 0 from rfl]⟩

/-- An empty node (no slots present) whose element array is pre-allocated with capacity `c`.
The capacity is only an allocation hint, so this is equal *as a value* to `Node.empty`;
`join`/`meet` start their accumulator here, sized to the result's final element count, so the
ascending inserts that build the result never reallocate. -/
private def emptyWithCapacity (c : Nat) : Node α :=
  ⟨0, Array.emptyWithCapacity c, by simp [show popCount 0 = 0 from rfl]⟩

/-- A node with a single child at slot `i`. -/
def singleton (i : UInt32) (a : α) : Node α :=
  ⟨setBit 0 i, #[a], by
    rw [popCount_setBit 0 i (testBit_zero i)]; simp [show popCount 0 = 0 from rfl]⟩

/-- Has no present slots. -/
def isEmpty (n : Node α) : Bool := n.positionsMask == 0

/-- Number of present slots. -/
def size (n : Node α) : Nat := popCount n.positionsMask

/-- The child at a *present* slot. The bit-set proof makes the compact index in-bounds
(`arrayIndex_lt` + the `elements_compact` field), so the read is total — no `Option`, no
spurious `none` to discharge at the call site. -/
def get (n : Node α) (i : UInt32) (h : testBit n.positionsMask i = true) : α :=
  n.elements[arrayIndex n.positionsMask i]'(by
    rw [n.elements_compact]; exact arrayIndex_lt n.positionsMask i h)

/-- A child read from a present slot is one of the stored children. -/
theorem get_mem (n : Node α) (i : UInt32) (h : testBit n.positionsMask i = true) :
    n.get i h ∈ n.elements := Array.getElem_mem _

/-- The child at slot `i`, if present. The dependent `if` hands the present-case proof to
`get`, so there is no spurious `none`. -/
def get? (n : Node α) (i : UInt32) : Option α :=
  if h : testBit n.positionsMask i = true then some (n.get i h) else none

/-- General single-slot update: `f` sees the current value at slot `i` (if any) and
returns the new value (`none` removes the slot).

Matching on `hpres : testBit … = true/false` records whether the slot was present, which
is exactly what the compactness proofs need: a present slot's compact index is `< size`
(so `eraseIdx`/`set` are in bounds and clearing the bit drops the count by one), and an
absent slot's index is `≤ size` (so `insertIdx` is in bounds and setting the bit raises
the count by one). -/
def alter (n : Node α) (i : UInt32) (f : Option α → Option α) : Node α :=
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

/-- Insert (or overwrite) the child at slot `i`. -/
def insert (n : Node α) (i : UInt32) (a : α) : Node α := n.alter i (fun _ => some a)

/-- Remove the child at slot `i`. -/
def erase (n : Node α) (i : UInt32) : Node α := n.alter i (fun _ => none)

/-- Apply `f` to the child at slot `i`, if present. -/
def modify (n : Node α) (i : UInt32) (f : α → α) : Node α := n.alter i (Option.map f)

/-- Fold over present slots in ascending slot order, exposing the slot index. -/
def foldl {β : Type v} (f : β → UInt32 → α → β) (init : β) (n : Node α) : β :=
  Nat.fold 32 (fun i _ (acc : β) =>
    let iu := UInt32.ofNat i
    if h : testBit n.positionsMask iu = true then f acc iu (n.get iu h) else acc) init

/-- Union of two nodes. Slots in exactly one side are reused as-is; slots in both are
merged with `combine` (a `none` result drops the slot).

The result is assembled by `insert`ing present slots into an empty accumulator in ascending
order. Each `insert` of a fresh, larger slot appends to the element array (its compact index
is the current size) — identical data to a plain `push` — but routes through the
compactness-preserving `alter`, so the result is compact by construction with no extra proof.
The accumulator is pre-sized to `popCount (a.positionsMask ||| b.positionsMask)`, the exact
slot count of the union mask (an upper bound on the result, since `combine` may prune), so
those appends never reallocate. -/
def join (combine : α → α → Option α) (a b : Node α) : Node α :=
  let step := fun (acc : Node α) i =>
    let iu := UInt32.ofNat i
    match ha : testBit a.positionsMask iu, hb : testBit b.positionsMask iu with
    | true, true =>
      match combine (a.get iu ha) (b.get iu hb) with
      | some v => acc.insert iu v
      | none   => acc
    | true, false => acc.insert iu (a.get iu ha)
    | false, true => acc.insert iu (b.get iu hb)
    | false, false => acc
  Nat.fold 32 (fun i _ acc => step acc i)
    (Node.emptyWithCapacity (popCount (a.positionsMask ||| b.positionsMask)))

/-- Intersection of two nodes. Only slots present in both survive, merged with
`combine`; a `none` result (empty intersection) drops the slot. As with `join`, the result is
built by ascending `insert` into an empty accumulator, so it is compact by construction. The
accumulator is pre-sized to `popCount (a.positionsMask &&& b.positionsMask)`, the slot count
of the intersection mask (an upper bound on the result), so the inserts never reallocate. -/
def meet (combine : α → α → Option α) (a b : Node α) : Node α :=
  let step := fun (acc : Node α) i =>
    let iu := UInt32.ofNat i
    match ha : testBit a.positionsMask iu, hb : testBit b.positionsMask iu with
    | true, true =>
      match combine (a.get iu ha) (b.get iu hb) with
      | some v => acc.insert iu v
      | none   => acc
    | true, false => acc
    | false, true => acc
    | false, false => acc
  Nat.fold 32 (fun i _ acc => step acc i)
    (Node.emptyWithCapacity (popCount (a.positionsMask &&& b.positionsMask)))

/-- `a` restricts `b`: every slot of `a` is present in `b`, and `rel` holds on every
shared child. -/
def restricts (rel : α → α → Bool) (a b : Node α) : Bool :=
  if (a.positionsMask &&& b.positionsMask) != a.positionsMask then false
  else
    let step := fun (ok : Bool) i =>
      let iu := UInt32.ofNat i
      match ha : testBit a.positionsMask iu, hb : testBit b.positionsMask iu with
      | true, true => ok && rel (a.get iu ha) (b.get iu hb)
      | true, false => ok
      | false, true => ok
      | false, false => ok
    Nat.fold 32 (fun i _ ok => step ok i) true

/-! ### Lemmas backing the `NatCollection` canonical-shape invariant

These support the collection layer's "no empty subtree" proof (`Tree.Full`). `mem_alter`
identifies where a freshly-stored child can come from after a single-slot update, so each
update preserves the per-child property. `join_forall`/`meet_forall` lift a property `P`
over all stored children through the 32-slot fold that builds a merge: every element of the
result is either reused from an operand or produced by `combine`, so it satisfies `P` as
long as the operands' children and the `combine` outputs do. The mask helpers record how
`insert`/`singleton` move `positionsMask`, feeding the height-minimality (`Tree.TopProper`)
proofs. -/

/-- Where a child of `n.alter i f` comes from: either it was already in `n`, or it is the
value `f` produced for slot `i`. -/
theorem mem_alter {α} (n : Node α) (i : UInt32) (f : Option α → Option α) (x : α)
    (hx : x ∈ (n.alter i f).elements) :
    x ∈ n.elements ∨ (∃ a, f (n.get? i) = some a ∧ x = a) := by
  unfold Node.alter at hx
  split at hx
  · rename_i htb
    rw [show n.get? i = some (n.get i htb) from by rw [Node.get?, dif_pos htb]]
    split at hx
    · rename_i a hfa
      simp only at hx
      rcases Array.mem_or_eq_of_mem_setIfInBounds hx with h | h
      · exact Or.inl h
      · exact Or.inr ⟨a, hfa, h⟩
    · rename_i hfn
      simp only at hx
      have hlt : arrayIndex n.positionsMask i < n.elements.size := by
        rw [n.elements_compact]; exact arrayIndex_lt n.positionsMask i htb
      rw [show n.elements.eraseIdx! (arrayIndex n.positionsMask i)
            = n.elements.eraseIdx (arrayIndex n.positionsMask i) hlt from dif_pos hlt] at hx
      exact Or.inl (Array.mem_of_mem_eraseIdx hx)
  · rename_i htb
    rw [show n.get? i = none from by rw [Node.get?, dif_neg (by simp [htb])]]
    split at hx
    · rename_i a hfa
      simp only at hx
      have hle : arrayIndex n.positionsMask i ≤ n.elements.size := by
        rw [n.elements_compact]; exact arrayIndex_le n.positionsMask i
      rw [show n.elements.insertIdx! (arrayIndex n.positionsMask i) a
            = n.elements.insertIdx (arrayIndex n.positionsMask i) a hle from dif_pos hle] at hx
      rcases Array.mem_insertIdx.mp hx with h | h
      · exact Or.inr ⟨a, hfa, h⟩
      · exact Or.inl h
    · rename_i hfn
      exact Or.inl hx

private theorem mem_insert {α} (n : Node α) (i : UInt32) (v x : α)
    (hx : x ∈ (n.insert i v).elements) : x = v ∨ x ∈ n.elements := by
  unfold Node.insert at hx
  rcases mem_alter n i (fun _ => some v) x hx with h | ⟨a, ha, hxa⟩
  · exact Or.inr h
  · exact Or.inl (hxa.trans (Option.some.inj ha).symm)

/-- Generic `Nat.fold` invariant: if every step keeps all accumulator elements satisfying
`P`, the final accumulator does too. -/
private theorem fold_elements_forall {α} {P : α → Prop}
    (step : Node α → Nat → Node α)
    (hstep : ∀ acc i, (∀ z ∈ acc.elements, P z) → ∀ z ∈ (step acc i).elements, P z)
    (n : Nat) (acc0 : Node α) (h0 : ∀ z ∈ acc0.elements, P z) :
    ∀ z ∈ (Nat.fold n (fun i _ acc => step acc i) acc0).elements, P z := by
  induction n with
  | zero => exact h0
  | succ k ih => rw [Nat.fold_succ]; exact hstep _ k ih

/-- Every child of a `join` result satisfies `P`, provided both operands' children and all
`combine` outputs do. -/
theorem join_forall {α} {P : α → Prop} {combine : α → α → Option α} {a b : Node α}
    (hPa : ∀ x ∈ a.elements, P x) (hPb : ∀ y ∈ b.elements, P y)
    (hPc : ∀ x ∈ a.elements, ∀ y ∈ b.elements, ∀ v, combine x y = some v → P v) :
    ∀ z ∈ (Node.join combine a b).elements, P z := by
  unfold Node.join
  apply fold_elements_forall
  · intro acc i hacc z hz
    dsimp only at hz ⊢
    split at hz
    · rename_i ha hb
      split at hz
      · rename_i v hcv
        rcases mem_insert _ _ _ _ hz with h | h
        · subst h; exact hPc _ (a.get_mem _ ha) _ (b.get_mem _ hb) _ hcv
        · exact hacc _ h
      · exact hacc _ hz
    · rename_i ha hb
      rcases mem_insert _ _ _ _ hz with h | h
      · subst h; exact hPa _ (a.get_mem _ ha)
      · exact hacc _ h
    · rename_i ha hb
      rcases mem_insert _ _ _ _ hz with h | h
      · subst h; exact hPb _ (b.get_mem _ hb)
      · exact hacc _ h
    · exact hacc _ hz
  · intro z hz; simp [Node.emptyWithCapacity] at hz

/-- Every child of a `meet` result satisfies `P`, provided all `combine` outputs do (only
slots present in both operands survive, so the operands' own children are irrelevant). -/
theorem meet_forall {α} {P : α → Prop} {combine : α → α → Option α} {a b : Node α}
    (hPc : ∀ x ∈ a.elements, ∀ y ∈ b.elements, ∀ v, combine x y = some v → P v) :
    ∀ z ∈ (Node.meet combine a b).elements, P z := by
  unfold Node.meet
  apply fold_elements_forall
  · intro acc i hacc z hz
    dsimp only at hz ⊢
    split at hz
    · rename_i ha hb
      split at hz
      · rename_i v hcv
        rcases mem_insert _ _ _ _ hz with h | h
        · subst h; exact hPc _ (a.get_mem _ ha) _ (b.get_mem _ hb) _ hcv
        · exact hacc _ h
      · exact hacc _ hz
    · exact hacc _ hz
    · exact hacc _ hz
    · exact hacc _ hz
  · intro z hz; simp [Node.emptyWithCapacity] at hz

/-- `singleton`'s mask is a single set bit. -/
private theorem singleton_positionsMask {α} (i : UInt32) (a : α) :
    (Node.singleton i a).positionsMask = setBit 0 i := rfl

/-- A singleton node is never empty. -/
theorem isEmpty_singleton {α} (i : UInt32) (a : α) : (Node.singleton i a).isEmpty = false := by
  unfold Node.isEmpty
  rw [singleton_positionsMask]
  exact beq_eq_false_iff_ne.mpr (setBit_ne_zero 0 i)

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

/-- A single-slot update whose callback yields a value sets exactly slot `i` of the mask
(again idempotently). This drives the `insert` mask facts at the `Tree` level — that the
slot is populated and the mask only grows — and hence height-minimality and non-emptiness. -/
theorem positionsMask_alter_of_isSome {α} (n : Node α) (i : UInt32) (f : Option α → Option α)
    (hf : (f (n.get? i)).isSome = true) :
    (n.alter i f).positionsMask = setBit n.positionsMask i := by
  unfold Node.alter
  split
  · rename_i htb
    rw [show n.get? i = some (n.get i htb) from by rw [Node.get?, dif_pos htb]] at hf
    split
    · simp only; exact (setBit_eq_of_testBit n.positionsMask i htb).symm
    · rename_i hfn; rw [hfn] at hf; simp at hf
  · rename_i htb
    rw [show n.get? i = none from by rw [Node.get?, dif_neg (by simp [htb])]] at hf
    split
    · rfl
    · rename_i hfn; rw [hfn] at hf; simp at hf

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

/-- A `Nat.fold` whose every step preserves `true` stays `true`. Backs `restricts_self`'s
32-slot scan (each slot keeps the running "ok" flag `true`). -/
private theorem fold_const_true (step : Bool → Nat → Bool)
    (hstep : ∀ ok i, ok = true → step ok i = true) (m : Nat) :
    Nat.fold m (fun i _ ok => step ok i) true = true := by
  induction m with
  | zero => rfl
  | succ k ih => rw [Nat.fold_succ]; exact hstep _ k ih

/-- `restricts` is reflexive when `rel` is reflexive on the stored children: every slot of a
node is trivially present in itself, and `rel` holds on each coinciding child. -/
theorem restricts_self {α} (rel : α → α → Bool) (n : Node α)
    (hrel : ∀ x ∈ n.elements, rel x x = true) :
    Node.restricts rel n n = true := by
  unfold Node.restricts
  split
  · -- the mask-subset guard can't fire: `m &&& m = m`
    rename_i hc
    have : n.positionsMask &&& n.positionsMask = n.positionsMask := by bv_decide
    simp_all
  · -- every slot keeps the running flag true: only a present slot is checked, and `rel`
    -- holds there on the (single) coinciding child
    apply fold_const_true
    intro ok i hok
    subst hok
    -- expose the per-slot `match` (hidden under the `let iu`), then scan its arms: the only
    -- non-trivial one is "present in both", closed by `rel`-reflexivity on the shared child
    extract_lets iu
    split <;> first
      | (rename_i ha _; rw [Bool.true_and]; exact hrel _ (n.get_mem _ ha))
      | rfl

/-- `Nat.fold` congruence: equal seeds and pointwise-equal steps give equal results. Backs
`join_comm`, where the two folds differ only in their (definitionally pruning) per-slot steps
and a commuted capacity hint. -/
private theorem fold_step_congr {β : Type v} (stepf stepg : β → Nat → β) (initf initg : β)
    (hinit : initf = initg) (hstep : ∀ acc i, stepf acc i = stepg acc i) (n : Nat) :
    Nat.fold n (fun i _ acc => stepf acc i) initf
      = Nat.fold n (fun i _ acc => stepg acc i) initg := by
  subst hinit
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.fold_succ, Nat.fold_succ, ih, hstep]

/-- `Nat.fold` congruence requiring step agreement only on the indices actually visited
(`i < n`). Backs `join_assoc`, where the two folds' steps agree only on in-range slots
(`UInt32.ofNat i < 32`). -/
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

/-- `join` commutes when the combine is flipped: merging `a` into `b` with `f` equals merging
`b` into `a` with `f`'s arguments swapped. The two folds run over the same slots (`|||` is
commutative, so the capacity seeds match); on each slot the present/absent cases line up and
the both-present case agrees by `hfg`. -/
theorem join_comm {α} {f g : α → α → Option α} (a b : Node α)
    (hfg : ∀ x y, f x y = g y x) :
    Node.join f a b = Node.join g b a := by
  simp only [Node.join]
  refine fold_step_congr _ _ _ _ ?_ ?_ 32
  · -- the capacity seeds agree because `|||` is commutative
    rw [show a.positionsMask ||| b.positionsMask = b.positionsMask ||| a.positionsMask from by
      bv_decide]
  · -- per slot: scan the four present/absent cases; the both-present one closes by `hfg`
    intro acc i
    dsimp only
    split <;> symm <;> split <;> simp_all

/-- `meet` commutes when the combine is flipped: intersecting `a` with `b` using `f` equals
intersecting `b` with `a` with `f`'s arguments swapped. The two folds run over the same slots
(`&&&` is commutative, so the capacity seeds match); on each slot only the both-present case
contributes, and it agrees by `hfg` (the other three drop the slot regardless). -/
theorem meet_comm {α} {f g : α → α → Option α} (a b : Node α)
    (hfg : ∀ x y, f x y = g y x) :
    Node.meet f a b = Node.meet g b a := by
  simp only [Node.meet]
  refine fold_step_congr _ _ _ _ ?_ ?_ 32
  · -- the capacity seeds agree because `&&&` is commutative
    rw [show a.positionsMask &&& b.positionsMask = b.positionsMask &&& a.positionsMask from by
      bv_decide]
  · -- per slot: scan the four present/absent cases; the both-present one closes by `hfg`
    intro acc i
    dsimp only
    split <;> symm <;> split <;> simp_all

/-! ### `get?` characterization and node extensionality

These support the `get?`-based denotational semantics the `NatCollection` lattice laws
(associativity, …) are proved against. `get?_join` reads off a `join` result slot-by-slot as a
value-level merge `optJoin`; `Node.ext` recovers a node from its `get?`. Slot indices are always
`< 32` here (they come from 5-bit `chunk`s), matching `UInt32`'s mod-32 shift semantics. -/

/-- Value-level merge underlying `Node.join`: present on both sides ↦ `combine`; on one ↦ copy. -/
def optJoin (combine : α → α → Option α) : Option α → Option α → Option α
  | some x, some y => combine x y
  | some x, none   => some x
  | none,   some y => some y
  | none,   none   => none

/-- The empty node reads `none` everywhere. -/
@[simp] theorem get?_empty (i : UInt32) : (Node.empty : Node α).get? i = none := by
  unfold Node.get?
  rw [dif_neg (by simp [Node.empty, testBit_zero])]

/-- A slot is present in the mask exactly when `get?` reports a value. -/
theorem testBit_eq_isSome_get? (n : Node α) (i : UInt32) :
    testBit n.positionsMask i = (n.get? i).isSome := by
  unfold Node.get?
  split <;> rename_i h <;> simp_all

/-- A node with a present slot is non-empty. -/
theorem isEmpty_eq_false_of_get? (n : Node α) (s : UInt32) (h : (n.get? s).isSome) :
    Node.isEmpty n = false := by
  have htb : testBit n.positionsMask s = true := by rw [testBit_eq_isSome_get?]; exact h
  show (n.positionsMask == 0) = false
  apply beq_eq_false_iff_ne.mpr
  intro h0; rw [h0, testBit_zero] at htb; exact absurd htb (by simp)

/-- A non-empty node has a present slot (`< 32`). -/
theorem exists_get?_of_isEmpty_false (n : Node α) (h : Node.isEmpty n = false) :
    ∃ i, i < 32 ∧ (n.get? i).isSome := by
  rcases Classical.em (∃ i, i < 32 ∧ (n.get? i).isSome) with hyes | hno
  · exact hyes
  · exfalso
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
        rw [show n.get? (UInt32.ofNat k) = some (n.get (UInt32.ofNat k) htb) from by
              unfold Node.get?; rw [dif_pos htb],
            optElim_some, if_pos htb,
            show n.get (UInt32.ofNat k) htb
              = n.elements[arrayIndex n.positionsMask (UInt32.ofNat k)]'hAlt from rfl,
            Array.push_extract_getElem hAlt, Nat.min_eq_left (Nat.zero_le _)]
      · rw [show n.get? (UInt32.ofNat k) = none from by unfold Node.get?; rw [dif_neg htb],
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
    rw [show n.get? (UInt32.ofNat 31) = some (n.get (UInt32.ofNat 31) htb) from by
          unfold Node.get?; rw [dif_pos htb],
        optElim_some,
        show n.get (UInt32.ofNat 31) htb
          = n.elements[arrayIndex n.positionsMask (UInt32.ofNat 31)]'hAlt from rfl,
        Array.push_extract_getElem hAlt, Nat.min_eq_left (Nat.zero_le _), hsize,
        Array.extract_eq_self_of_le (Nat.le_refl _)]
  · have hsize : arrayIndex n.positionsMask (UInt32.ofNat 31) = n.elements.size := by
      rw [n.elements_compact]
      show popCount (n.positionsMask &&& lowerMask (UInt32.ofNat 31)) = popCount n.positionsMask
      rw [h31eq, popCount_split31 n.positionsMask, if_neg (by rw [← h31eq]; exact htb), Nat.add_zero]
    rw [show n.get? (UInt32.ofNat 31) = none from by unfold Node.get?; rw [dif_neg htb],
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

/-- `get?` as a (proof-free) `getElem?` on the compact array. Lets `get?` lemmas reason about
the underlying `Array` operations without carrying `Node.get`'s in-bounds proof. -/
theorem get?_eq_getElem? (n : Node α) (j : UInt32) :
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
        rcases lt_or_gt_uint32 (Ne.symm hji) with hgt | hlt
        · -- i < j : the index shifts up by one
          rw [arrayIndex_setBit_of_gt _ _ _ hi hj hgt hpres, Array.getElem?_insertIdx hsize,
              if_neg (by have := arrayIndex_le_of_le n.positionsMask i j hi hj (uint32_le_of_lt hgt); omega),
              if_neg (by have := arrayIndex_le_of_le n.positionsMask i j hi hj (uint32_le_of_lt hgt); omega),
              Nat.add_sub_cancel]
        · -- j < i : the index is below the insertion point, unchanged
          rw [arrayIndex_setBit_of_le _ _ _ hi hj (uint32_le_of_lt hlt),
              Array.getElem?_insertIdx_of_lt hsize (arrayIndex_lt_of_lt _ j i hj hi hbj hlt)]
      · rw [if_neg hbj, if_neg hbj]

/-- The per-slot accumulator step of `Node.join`, named so the `get?` fold invariant can refer
to it. Definitionally equal to the body of `Node.join`. -/
def joinStepCore (combine : α → α → Option α) (a b : Node α) (acc : Node α) (i : Nat) : Node α :=
  match h1 : testBit a.positionsMask (UInt32.ofNat i), h2 : testBit b.positionsMask (UInt32.ofNat i) with
  | true, true => match combine (a.get (UInt32.ofNat i) h1) (b.get (UInt32.ofNat i) h2) with
                  | some v => acc.insert (UInt32.ofNat i) v
                  | none => acc
  | true, false => acc.insert (UInt32.ofNat i) (a.get (UInt32.ofNat i) h1)
  | false, true => acc.insert (UInt32.ofNat i) (b.get (UInt32.ofNat i) h2)
  | false, false => acc

theorem join_eq_fold (combine : α → α → Option α) (a b : Node α) :
    Node.join combine a b
      = Nat.fold 32 (fun i _ acc => joinStepCore combine a b acc i)
          (Node.emptyWithCapacity (popCount (a.positionsMask ||| b.positionsMask))) := rfl

/-- `get?` of one join step at a *fresh* accumulator slot: the visited slot `i` gets the merged
value `optJoin combine (a? i) (b? i)`, every other slot is unchanged. `hfresh` (slot `i` absent in
`acc`) is what the fold supplies — it processes slots in increasing order. -/
theorem joinStepCore_get? (combine : α → α → Option α) (a b acc : Node α) (i : Nat) (j : UInt32)
    (hi : (UInt32.ofNat i) < 32) (hj : j < 32) (hfresh : acc.get? (UInt32.ofNat i) = none) :
    (joinStepCore combine a b acc i).get? j
      = if j = UInt32.ofNat i then optJoin combine (a.get? (UInt32.ofNat i)) (b.get? (UInt32.ofNat i))
        else acc.get? j := by
  unfold joinStepCore
  split
  · rename_i h1 h2
    rw [show a.get? (UInt32.ofNat i) = some (a.get (UInt32.ofNat i) h1) from by
          unfold Node.get?; rw [dif_pos h1],
        show b.get? (UInt32.ofNat i) = some (b.get (UInt32.ofNat i) h2) from by
          unfold Node.get?; rw [dif_pos h2]]
    split
    · rename_i v hv
      by_cases hjk : j = UInt32.ofNat i
      · rw [get?_insert _ _ _ _ hi hj, if_pos hjk, if_pos hjk]; simp only [optJoin]; rw [hv]
      · rw [get?_insert _ _ _ _ hi hj, if_neg hjk, if_neg hjk]
    · rename_i hv
      by_cases hjk : j = UInt32.ofNat i
      · rw [if_pos hjk, hjk, hfresh]; simp only [optJoin]; rw [hv]
      · rw [if_neg hjk]
  · rename_i h1 h2
    rw [show a.get? (UInt32.ofNat i) = some (a.get (UInt32.ofNat i) h1) from by
          unfold Node.get?; rw [dif_pos h1],
        show b.get? (UInt32.ofNat i) = none from by unfold Node.get?; rw [dif_neg (by simp [h2])]]
    simp only [optJoin]
    by_cases hjk : j = UInt32.ofNat i
    · rw [get?_insert _ _ _ _ hi hj, if_pos hjk]
    · rw [get?_insert _ _ _ _ hi hj, if_neg hjk]
  · rename_i h1 h2
    rw [show a.get? (UInt32.ofNat i) = none from by unfold Node.get?; rw [dif_neg (by simp [h1])],
        show b.get? (UInt32.ofNat i) = some (b.get (UInt32.ofNat i) h2) from by
          unfold Node.get?; rw [dif_pos h2]]
    simp only [optJoin]
    by_cases hjk : j = UInt32.ofNat i
    · rw [get?_insert _ _ _ _ hi hj, if_pos hjk]
    · rw [get?_insert _ _ _ _ hi hj, if_neg hjk]
  · rename_i h1 h2
    rw [show a.get? (UInt32.ofNat i) = none from by unfold Node.get?; rw [dif_neg (by simp [h1])],
        show b.get? (UInt32.ofNat i) = none from by unfold Node.get?; rw [dif_neg (by simp [h2])]]
    by_cases hjk : j = UInt32.ofNat i
    · rw [if_pos hjk, hjk, hfresh]; simp only [optJoin]
    · rw [if_neg hjk]

/-- `get?` of a `Node.join`: a value-level merge of the two lookups. A `Nat.fold` invariant —
after processing slots `0..m`, slot `j < m` holds `optJoin combine (a? j) (b? j)`, each step
filling the fresh slot `m` (`joinStepCore_get?`). -/
theorem get?_join (combine : α → α → Option α) (a b : Node α) (j : UInt32) (hj : j < 32) :
    (Node.join combine a b).get? j = optJoin combine (a.get? j) (b.get? j) := by
  have hjn : j.toNat < 32 := by
    have h := UInt32.lt_iff_toNat_lt.mp hj; rwa [show (32 : UInt32).toNat = 32 from by decide] at h
  rw [join_eq_fold]
  suffices H : ∀ m, m ≤ 32 → ∀ (j' : UInt32), j' < 32 →
      (Nat.fold m (fun i _ acc => joinStepCore combine a b acc i)
          (Node.emptyWithCapacity (popCount (a.positionsMask ||| b.positionsMask)))).get? j'
        = if j'.toNat < m then optJoin combine (a.get? j') (b.get? j') else none by
    rw [H 32 (Nat.le_refl _) j hj, if_pos hjn]
  intro m
  induction m with
  | zero =>
    intro _ j' _
    rw [Nat.fold_zero, if_neg (by omega)]
    unfold Node.get?; rw [dif_neg (by simp [Node.emptyWithCapacity, testBit_zero])]
  | succ k ih =>
    intro hk j' hj'
    have hk' : k ≤ 32 := Nat.le_of_succ_le hk
    have hks : k < 32 := hk
    have hiun : (UInt32.ofNat k).toNat = k :=
      UInt32.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hks (by decide))
    have hiu : (UInt32.ofNat k) < 32 := by
      rw [UInt32.lt_iff_toNat_lt, hiun, show (32 : UInt32).toNat = 32 from by decide]; exact hks
    have hfresh : (Nat.fold k (fun i _ acc => joinStepCore combine a b acc i)
        (Node.emptyWithCapacity (popCount (a.positionsMask ||| b.positionsMask)))).get?
          (UInt32.ofNat k) = none := by
      rw [ih hk' (UInt32.ofNat k) hiu, if_neg (by omega)]
    rw [Nat.fold_succ, joinStepCore_get? combine a b _ k j' hiu hj' hfresh, ih hk' j' hj']
    by_cases hjk : j' = UInt32.ofNat k
    · rw [if_pos hjk, hjk, if_pos (by omega)]
    · rw [if_neg hjk]
      have hjne : j'.toNat ≠ k := fun h => hjk (by rw [← hiun] at h; exact UInt32.toNat_inj.mp h)
      by_cases hlt : j'.toNat < k
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]

/-- One join step expressed via `optJoin`: it inserts the merged value (or leaves `acc` when the
merge prunes). The bridge from `Node.join`'s mask-driven `match` to the value-level `optJoin`.
States the result with `Option.elim` (not `match`) so `split` targets `joinStepCore`'s matcher. -/
theorem joinStepCore_eq (combine : α → α → Option α) (a b acc : Node α) (i : Nat) :
    joinStepCore combine a b acc i
      = (optJoin combine (a.get? (UInt32.ofNat i)) (b.get? (UInt32.ofNat i))).elim acc
          (fun v => acc.insert (UInt32.ofNat i) v) := by
  unfold joinStepCore
  split
  · rename_i h1 h2
    rw [show a.get? (UInt32.ofNat i) = some (a.get (UInt32.ofNat i) h1) from by
          unfold Node.get?; rw [dif_pos h1],
        show b.get? (UInt32.ofNat i) = some (b.get (UInt32.ofNat i) h2) from by
          unfold Node.get?; rw [dif_pos h2]]
    simp only [optJoin]
    cases combine (a.get (UInt32.ofNat i) h1) (b.get (UInt32.ofNat i) h2) <;> rfl
  · rename_i h1 h2
    rw [show a.get? (UInt32.ofNat i) = some (a.get (UInt32.ofNat i) h1) from by
          unfold Node.get?; rw [dif_pos h1],
        show b.get? (UInt32.ofNat i) = none from by unfold Node.get?; rw [dif_neg (by simp [h2])]]
    rfl
  · rename_i h1 h2
    rw [show a.get? (UInt32.ofNat i) = none from by unfold Node.get?; rw [dif_neg (by simp [h1])],
        show b.get? (UInt32.ofNat i) = some (b.get (UInt32.ofNat i) h2) from by
          unfold Node.get?; rw [dif_pos h2]]
    rfl
  · rename_i h1 h2
    rw [show a.get? (UInt32.ofNat i) = none from by unfold Node.get?; rw [dif_neg (by simp [h1])],
        show b.get? (UInt32.ofNat i) = none from by unfold Node.get?; rw [dif_neg (by simp [h2])]]
    rfl

/-- Associativity of `Node.join` for a combine that merges associatively at every slot. The two
sides are `Nat.fold`s over the same 32 slots; by `get?_join` their per-slot inserts agree (the
hypothesis `hassoc` is exactly the value-level associativity at each slot), so `fold_step_congr`
closes it — no node extensionality required. -/
theorem join_assoc (combine : α → α → Option α) (a b d : Node α)
    (hassoc : ∀ s, s < 32 → optJoin combine (optJoin combine (a.get? s) (b.get? s)) (d.get? s)
                          = optJoin combine (a.get? s) (optJoin combine (b.get? s) (d.get? s))) :
    Node.join combine (Node.join combine a b) d = Node.join combine a (Node.join combine b d) := by
  rw [join_eq_fold combine (Node.join combine a b) d, join_eq_fold combine a (Node.join combine b d)]
  refine fold_step_congr_lt _ _ _ _ ?_ 32 ?_
  · -- capacity seeds are just allocation hints; both equal the empty node as values
    unfold Node.emptyWithCapacity
    simp only [Array.emptyWithCapacity_eq]
  · intro acc i hi32
    have hi : (UInt32.ofNat i) < 32 := by
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hi32 (by decide)),
          show (32 : UInt32).toNat = 32 from by decide]; exact hi32
    rw [joinStepCore_eq combine (Node.join combine a b) d acc i,
        joinStepCore_eq combine a (Node.join combine b d) acc i,
        get?_join combine a b _ hi, get?_join combine b d _ hi, hassoc (UInt32.ofNat i) hi]

/-- Joining (with a total, never-pruning combine) onto a non-empty node stays non-empty: the
present slot of `a` survives in the result (`get?_join`). Backs the leaf `isEmpty_join` law for
maps. -/
theorem isEmpty_join_left (c : α → α → α) (a b : Node α) (hne : Node.isEmpty a = false) :
    Node.isEmpty (Node.join (fun x y => some (c x y)) a b) = false := by
  obtain ⟨s, hs, hsome⟩ := exists_get?_of_isEmpty_false a hne
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
  have htb : testBit (Node.join (fun x y => some (c x y)) a b).positionsMask s = true := by
    rw [testBit_eq_isSome_get?, get?_join _ _ _ _ hs, hx]
    cases b.get? s <;> simp [optJoin]
  show ((Node.join (fun x y => some (c x y)) a b).positionsMask == 0) = false
  apply beq_eq_false_iff_ne.mpr
  intro h0
  rw [h0, testBit_zero] at htb
  exact absurd htb (by simp)

/-- The value-level merge of a *total* (never-pruning) combine is associative when the combine is.
The per-slot obligation of `join_assoc` for maps. -/
theorem optJoin_someC_assoc (c : α → α → α) (hc : ∀ x y z, c (c x y) z = c x (c y z))
    (oa ob od : Option α) :
    optJoin (fun x y => some (c x y)) (optJoin (fun x y => some (c x y)) oa ob) od
      = optJoin (fun x y => some (c x y)) oa (optJoin (fun x y => some (c x y)) ob od) := by
  rcases oa with _ | x <;> rcases ob with _ | y <;> rcases od with _ | z <;> simp only [optJoin]
  rw [hc]

/-! ### `get?` characterization of `meet`

The `meet` analogue of the `join` `get?` block above. `optMeet` is the value-level intersection:
a slot survives only if present on *both* sides (and the `combine` does not prune it). `get?_meet`
reads off a `meet` result slot-by-slot, backing the `meet`-associativity proof. -/

/-- Value-level merge underlying `Node.meet`: present on *both* sides ↦ `combine`; otherwise drop. -/
def optMeet (combine : α → α → Option α) : Option α → Option α → Option α
  | some x, some y => combine x y
  | _,      _      => none

/-- The per-slot accumulator step of `Node.meet`, named so the `get?` fold invariant can refer
to it. Definitionally equal to the body of `Node.meet`. -/
def meetStepCore (combine : α → α → Option α) (a b : Node α) (acc : Node α) (i : Nat) : Node α :=
  match h1 : testBit a.positionsMask (UInt32.ofNat i), h2 : testBit b.positionsMask (UInt32.ofNat i) with
  | true, true => match combine (a.get (UInt32.ofNat i) h1) (b.get (UInt32.ofNat i) h2) with
                  | some v => acc.insert (UInt32.ofNat i) v
                  | none => acc
  | true, false => acc
  | false, true => acc
  | false, false => acc

theorem meet_eq_fold (combine : α → α → Option α) (a b : Node α) :
    Node.meet combine a b
      = Nat.fold 32 (fun i _ acc => meetStepCore combine a b acc i)
          (Node.emptyWithCapacity (popCount (a.positionsMask &&& b.positionsMask))) := rfl

/-- `get?` of one meet step at a *fresh* accumulator slot: the visited slot `i` gets the merged
value `optMeet combine (a? i) (b? i)`, every other slot is unchanged. `hfresh` (slot `i` absent in
`acc`) is what the fold supplies — it processes slots in increasing order. -/
theorem meetStepCore_get? (combine : α → α → Option α) (a b acc : Node α) (i : Nat) (j : UInt32)
    (hi : (UInt32.ofNat i) < 32) (hj : j < 32) (hfresh : acc.get? (UInt32.ofNat i) = none) :
    (meetStepCore combine a b acc i).get? j
      = if j = UInt32.ofNat i then optMeet combine (a.get? (UInt32.ofNat i)) (b.get? (UInt32.ofNat i))
        else acc.get? j := by
  unfold meetStepCore
  split
  · rename_i h1 h2
    rw [show a.get? (UInt32.ofNat i) = some (a.get (UInt32.ofNat i) h1) from by
          unfold Node.get?; rw [dif_pos h1],
        show b.get? (UInt32.ofNat i) = some (b.get (UInt32.ofNat i) h2) from by
          unfold Node.get?; rw [dif_pos h2]]
    split
    · rename_i v hv
      by_cases hjk : j = UInt32.ofNat i
      · rw [get?_insert _ _ _ _ hi hj, if_pos hjk, if_pos hjk]; simp only [optMeet]; rw [hv]
      · rw [get?_insert _ _ _ _ hi hj, if_neg hjk, if_neg hjk]
    · rename_i hv
      by_cases hjk : j = UInt32.ofNat i
      · rw [if_pos hjk, hjk, hfresh]; simp only [optMeet]; rw [hv]
      · rw [if_neg hjk]
  · rename_i h1 h2
    -- slot present only in `a`: dropped, so `acc` is unchanged and the merged value is `none`
    rw [show b.get? (UInt32.ofNat i) = none from by unfold Node.get?; rw [dif_neg (by simp [h2])]]
    by_cases hjk : j = UInt32.ofNat i
    · rw [if_pos hjk, hjk, hfresh]; cases a.get? (UInt32.ofNat i) <;> rfl
    · rw [if_neg hjk]
  · rename_i h1 h2
    -- slot present only in `b`: dropped
    rw [show a.get? (UInt32.ofNat i) = none from by unfold Node.get?; rw [dif_neg (by simp [h1])]]
    by_cases hjk : j = UInt32.ofNat i
    · rw [if_pos hjk, hjk, hfresh]; simp only [optMeet]
    · rw [if_neg hjk]
  · rename_i h1 h2
    -- slot absent in both: dropped
    rw [show a.get? (UInt32.ofNat i) = none from by unfold Node.get?; rw [dif_neg (by simp [h1])]]
    by_cases hjk : j = UInt32.ofNat i
    · rw [if_pos hjk, hjk, hfresh]; simp only [optMeet]
    · rw [if_neg hjk]

/-- `get?` of a `Node.meet`: a value-level intersection of the two lookups. A `Nat.fold` invariant —
after processing slots `0..m`, slot `j < m` holds `optMeet combine (a? j) (b? j)`, each step
filling the fresh slot `m` (`meetStepCore_get?`). -/
theorem get?_meet (combine : α → α → Option α) (a b : Node α) (j : UInt32) (hj : j < 32) :
    (Node.meet combine a b).get? j = optMeet combine (a.get? j) (b.get? j) := by
  have hjn : j.toNat < 32 := by
    have h := UInt32.lt_iff_toNat_lt.mp hj; rwa [show (32 : UInt32).toNat = 32 from by decide] at h
  rw [meet_eq_fold]
  suffices H : ∀ m, m ≤ 32 → ∀ (j' : UInt32), j' < 32 →
      (Nat.fold m (fun i _ acc => meetStepCore combine a b acc i)
          (Node.emptyWithCapacity (popCount (a.positionsMask &&& b.positionsMask)))).get? j'
        = if j'.toNat < m then optMeet combine (a.get? j') (b.get? j') else none by
    rw [H 32 (Nat.le_refl _) j hj, if_pos hjn]
  intro m
  induction m with
  | zero =>
    intro _ j' _
    rw [Nat.fold_zero, if_neg (by omega)]
    unfold Node.get?; rw [dif_neg (by simp [Node.emptyWithCapacity, testBit_zero])]
  | succ k ih =>
    intro hk j' hj'
    have hk' : k ≤ 32 := Nat.le_of_succ_le hk
    have hks : k < 32 := hk
    have hiun : (UInt32.ofNat k).toNat = k :=
      UInt32.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hks (by decide))
    have hiu : (UInt32.ofNat k) < 32 := by
      rw [UInt32.lt_iff_toNat_lt, hiun, show (32 : UInt32).toNat = 32 from by decide]; exact hks
    have hfresh : (Nat.fold k (fun i _ acc => meetStepCore combine a b acc i)
        (Node.emptyWithCapacity (popCount (a.positionsMask &&& b.positionsMask)))).get?
          (UInt32.ofNat k) = none := by
      rw [ih hk' (UInt32.ofNat k) hiu, if_neg (by omega)]
    rw [Nat.fold_succ, meetStepCore_get? combine a b _ k j' hiu hj' hfresh, ih hk' j' hj']
    by_cases hjk : j' = UInt32.ofNat k
    · rw [if_pos hjk, hjk, if_pos (by omega)]
    · rw [if_neg hjk]
      have hjne : j'.toNat ≠ k := fun h => hjk (by rw [← hiun] at h; exact UInt32.toNat_inj.mp h)
      by_cases hlt : j'.toNat < k
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]

/-- A node with all slots absent (`get? = none` everywhere on in-range slots) is empty. The
contrapositive of `exists_get?_of_isEmpty_false`. -/
theorem isEmpty_of_get?_eq_none (n : Node α) (h : ∀ i, i < 32 → n.get? i = none) :
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

/-- `get?` of a singleton: the lone slot reads its value, every other slot is `none`. Backs the
slot-0 reasoning in `Tree`'s lift/spine bridge lemmas. -/
theorem get?_singleton (i : UInt32) (a : α) (j : UInt32) (hi : i < 32) (hj : j < 32) :
    (Node.singleton i a).get? j = if j = i then some a else none := by
  rw [get?_eq_getElem?]
  show (if testBit (setBit 0 i) j then (#[a])[arrayIndex (setBit 0 i) j]? else none)
      = if j = i then some a else none
  rw [testBit_setBit 0 i j hi hj, testBit_zero, Bool.false_or]
  by_cases hji : j = i
  · subst hji
    rw [arrayIndex_setBit_self, show arrayIndex (0 : UInt32) j = 0 from Nat.le_zero.mp (arrayIndex_le 0 j)]
    simp
  · rw [if_neg hji, beq_eq_false_iff_ne.mpr (fun hc => hji hc.symm)]
    simp

/-- A single-slot update depends on the leaf only through its current value at that slot, so two
callbacks agreeing on `n.get? i` give the same result. -/
theorem alter_congr (n : Node α) (i : UInt32) (f g : Option α → Option α)
    (h : f (n.get? i) = g (n.get? i)) : n.alter i f = n.alter i g := by
  unfold Node.alter
  split <;> rename_i hp
  · rw [show n.get? i = some (n.get i hp) from by unfold Node.get?; rw [dif_pos hp]] at h
    rw [h]
  · rw [show n.get? i = none from by unfold Node.get?; rw [dif_neg (by rw [hp]; simp)]] at h
    rw [h]

/-- When the callback yields a value, `alter` coincides with `insert` of that value (it only ever
inspects the current slot, which `insert` overwrites unconditionally). Lets the spine/lift bridges
reuse `get?_insert` for `alter`-built nodes whose callback never prunes. -/
theorem alter_eq_insert (n : Node α) (i : UInt32) (f : Option α → Option α) (w : α)
    (h : f (n.get? i) = some w) : n.alter i f = n.insert i w :=
  alter_congr n i f (fun _ => some w) (by rw [h])

/-- `get?` of an `alter` whose callback yields a value: slot `i` reads that value, every other slot
is unchanged (a corollary of `alter_eq_insert` + `get?_insert`). -/
theorem get?_alter_of_some (n : Node α) (i : UInt32) (f : Option α → Option α) (w : α)
    (hfw : f (n.get? i) = some w) (j : UInt32) (hi : i < 32) (hj : j < 32) :
    (n.alter i f).get? j = if j = i then some w else n.get? j := by
  rw [alter_eq_insert n i f w hfw, get?_insert n i w j hi hj]

end Node

/-! ## Tests -/

section Tests
open Node

private def n0 : Node Nat := Node.empty
private def nA : Node Nat := (Node.singleton 1 10).insert 4 40 |>.insert 31 310
private def nB : Node Nat := (Node.singleton 4 99).insert 7 70

#guard n0.isEmpty
#guard !nA.isEmpty
#guard nA.size == 3
#guard nA.get? 1 == some 10
#guard nA.get? 4 == some 40
#guard nA.get? 31 == some 310
#guard nA.get? 2 == none
#guard nA.get? 0 == none

-- insert at slot 0 (lowest) and check ordering is preserved structurally
#guard (Node.singleton 5 50 |>.insert 0 0 |>.get? 0) == some 0
#guard (Node.singleton 5 50 |>.insert 0 0 |>.get? 5) == some 50

-- overwrite keeps size and replaces value
#guard (nA.insert 4 400 |>.get? 4) == some 400
#guard (nA.insert 4 400).size == 3

-- erase then re-query; erasing an absent slot is a no-op
#guard (nA.erase 4 |>.get? 4) == none
#guard (nA.erase 4).size == 2
#guard nA.erase 2 == nA

-- modify only touches present slots
#guard (nA.modify 1 (· + 5) |>.get? 1) == some 15
#guard nA.modify 2 (· + 5) == nA

-- join: slot 4 collides (sum), others copied through
#guard (Node.join (fun x y => some (x + y)) nA nB |>.get? 1) == some 10
#guard (Node.join (fun x y => some (x + y)) nA nB |>.get? 4) == some 139
#guard (Node.join (fun x y => some (x + y)) nA nB |>.get? 7) == some 70
#guard (Node.join (fun x y => some (x + y)) nA nB).size == 4

-- meet: only the shared slot 4 survives
#guard (Node.meet (fun x y => some (x + y)) nA nB |>.get? 4) == some 139
#guard (Node.meet (fun x y => some (x + y)) nA nB).size == 1
#guard (Node.meet (fun _ _ => none) nA nB).isEmpty           -- pruned to empty

-- restricts: subset of slots + predicate on shared values
#guard Node.restricts (fun _ _ => true) (Node.singleton 4 40) nA
#guard !Node.restricts (fun _ _ => true) nA (Node.singleton 4 40)   -- nA has more slots
#guard Node.restricts (fun x y => x ≤ y) (Node.singleton 4 40) nA
#guard !Node.restricts (fun x y => x < y) (Node.singleton 4 40) nA  -- 40 < 40 fails
#guard Node.restricts (fun _ _ => true) Node.empty nA              -- empty restricts all

-- foldl visits slots ascending
#guard nA.foldl (fun acc i a => acc ++ [(i.toNat, a)]) [] == [(1, 10), (4, 40), (31, 310)]

-- the `elements_compact` invariant is a field every node carries, so it is available on
-- operation results too — here, on a `join` output — by construction, no side condition
example : (Node.join (fun x y => some (x + y)) nA nB).elements.size
        = popCount (Node.join (fun x y => some (x + y)) nA nB).positionsMask :=
  (Node.join (fun x y => some (x + y)) nA nB).elements_compact

end Tests

end NatCol
