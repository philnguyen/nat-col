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
