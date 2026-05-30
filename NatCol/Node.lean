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

/-- The empty node (no slots present). -/
def empty : Node α := ⟨0, #[], by simp [show popCount 0 = 0 from rfl]⟩

/-- A node with a single child at slot `i`. -/
def singleton (i : UInt32) (a : α) : Node α :=
  ⟨setBit 0 i, #[a], by
    rw [popCount_setBit 0 i (testBit_zero i)]; simp [show popCount 0 = 0 from rfl]⟩

/-- Has no present slots. -/
def isEmpty (n : Node α) : Bool := n.positionsMask == 0

/-- Number of present slots. -/
def size (n : Node α) : Nat := popCount n.positionsMask

/-- The child at slot `i`, if present. -/
def get? (n : Node α) (i : UInt32) : Option α :=
  if testBit n.positionsMask i then n.elements[arrayIndex n.positionsMask i]? else none

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
    match f n.elements[arrayIndex n.positionsMask i]? with
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
  Prod.fst <| (List.range 32).foldl (fun (st : β × Nat) i =>
    let iu := UInt32.ofNat i
    if testBit n.positionsMask iu then
      match n.elements[st.2]? with
      | some a => (f st.1 iu a, st.2 + 1)
      | none   => st
    else st) (init, 0)

/-- Union of two nodes. Slots in exactly one side are reused as-is; slots in both are
merged with `combine` (a `none` result drops the slot).

The result is assembled by `insert`ing present slots into `Node.empty` in ascending order.
Each `insert` of a fresh, larger slot appends to the element array (its compact index is the
current size) — identical data to a plain `push` — but routes through the
compactness-preserving `alter`, so the result is compact by construction with no extra
proof. -/
def join (combine : α → α → Option α) (a b : Node α) : Node α :=
  let step := fun (st : Node α × Nat × Nat) i =>
    let (acc, ja, jb) := st
    let iu := UInt32.ofNat i
    match testBit a.positionsMask iu, testBit b.positionsMask iu with
    | true, true =>
      match a.elements[ja]?, b.elements[jb]? with
      | some x, some y =>
        match combine x y with
        | some v => (acc.insert iu v, ja + 1, jb + 1)
        | none   => (acc, ja + 1, jb + 1)
      | _, _ => (acc, ja + 1, jb + 1)
    | true, false =>
      match a.elements[ja]? with
      | some x => (acc.insert iu x, ja + 1, jb)
      | none   => (acc, ja + 1, jb)
    | false, true =>
      match b.elements[jb]? with
      | some y => (acc.insert iu y, ja, jb + 1)
      | none   => (acc, ja, jb + 1)
    | false, false => (acc, ja, jb)
  ((List.range 32).foldl step (Node.empty, 0, 0)).1

/-- Intersection of two nodes. Only slots present in both survive, merged with
`combine`; a `none` result (empty intersection) drops the slot. As with `join`, the result
is built from `Node.empty` by ascending `insert`, so it is compact by construction. -/
def meet (combine : α → α → Option α) (a b : Node α) : Node α :=
  let step := fun (st : Node α × Nat × Nat) i =>
    let (acc, ja, jb) := st
    let iu := UInt32.ofNat i
    match testBit a.positionsMask iu, testBit b.positionsMask iu with
    | true, true =>
      match a.elements[ja]?, b.elements[jb]? with
      | some x, some y =>
        match combine x y with
        | some v => (acc.insert iu v, ja + 1, jb + 1)
        | none   => (acc, ja + 1, jb + 1)
      | _, _ => (acc, ja + 1, jb + 1)
    | true, false => (acc, ja + 1, jb)
    | false, true => (acc, ja, jb + 1)
    | false, false => (acc, ja, jb)
  ((List.range 32).foldl step (Node.empty, 0, 0)).1

/-- `a` restricts `b`: every slot of `a` is present in `b`, and `rel` holds on every
shared child. -/
def restricts (rel : α → α → Bool) (a b : Node α) : Bool :=
  if (a.positionsMask &&& b.positionsMask) != a.positionsMask then false
  else
    let step := fun (st : Bool × Nat × Nat) i =>
      let (ok, ja, jb) := st
      let iu := UInt32.ofNat i
      match testBit a.positionsMask iu, testBit b.positionsMask iu with
      | true, true =>
        match a.elements[ja]?, b.elements[jb]? with
        | some x, some y => (ok && rel x y, ja + 1, jb + 1)
        | _, _ => (ok, ja + 1, jb + 1)
      | true, false => (ok, ja + 1, jb)
      | false, true => (ok, ja, jb + 1)
      | false, false => (ok, ja, jb)
    (((List.range 32).foldl step (true, 0, 0))).1

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
