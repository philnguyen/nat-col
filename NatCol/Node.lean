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

/-- A sparse array of up to 32 children, addressed by a 5-bit slot index. -/
structure Node (α : Type u) where
  positionsMask : UInt32
  elements : Array α
deriving BEq, Repr

/-- The derived structural `BEq` decides propositional equality: it compares the two fields
with their own (lawful) `BEq`s. Needed so that maps — whose leaves are `Node α` — inherit
`LawfulBEq`. -/
instance {α : Type u} [BEq α] [LawfulBEq α] : LawfulBEq (Node α) where
  eq_of_beq {a b} h := by
    obtain ⟨ma, ea⟩ := a
    obtain ⟨mb, eb⟩ := b
    -- the derived `==` on constructors reduces to a conjunction of the field comparisons
    have h' : (ma == mb && ea == eb) = true := h
    rw [Bool.and_eq_true] at h'
    rw [eq_of_beq h'.1, eq_of_beq h'.2]
  rfl {a} := by
    obtain ⟨m, e⟩ := a
    show (m == m && e == e) = true
    rw [Bool.and_eq_true]
    exact ⟨BEq.rfl, BEq.rfl⟩

namespace Node

/-- The empty node (no slots present). -/
def empty : Node α := ⟨0, #[]⟩

/-- A node with a single child at slot `i`. -/
def singleton (i : UInt32) (a : α) : Node α := ⟨setBit 0 i, #[a]⟩

/-- Has no present slots. -/
def isEmpty (n : Node α) : Bool := n.positionsMask == 0

/-- Number of present slots. -/
def size (n : Node α) : Nat := popCount n.positionsMask

/-- The child at slot `i`, if present. -/
def get? (n : Node α) (i : UInt32) : Option α :=
  if testBit n.positionsMask i then n.elements[arrayIndex n.positionsMask i]? else none

/-- General single-slot update: `f` sees the current value at slot `i` (if any) and
returns the new value (`none` removes the slot). -/
def alter (n : Node α) (i : UInt32) (f : Option α → Option α) : Node α :=
  let present := testBit n.positionsMask i
  let idx := arrayIndex n.positionsMask i
  let cur := if present then n.elements[idx]? else none
  match present, f cur with
  | true,  some a => ⟨n.positionsMask, n.elements.set! idx a⟩
  | true,  none   => ⟨clearBit n.positionsMask i, n.elements.eraseIdx! idx⟩
  | false, some a => ⟨setBit n.positionsMask i, n.elements.insertIdx! idx a⟩
  | false, none   => n

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
merged with `combine` (a `none` result drops the slot). -/
def join (combine : α → α → Option α) (a b : Node α) : Node α :=
  let step := fun (st : UInt32 × Array α × Nat × Nat) i =>
    let (mask, elems, ja, jb) := st
    let iu := UInt32.ofNat i
    match testBit a.positionsMask iu, testBit b.positionsMask iu with
    | true, true =>
      match a.elements[ja]?, b.elements[jb]? with
      | some x, some y =>
        match combine x y with
        | some v => (setBit mask iu, elems.push v, ja + 1, jb + 1)
        | none   => (mask, elems, ja + 1, jb + 1)
      | _, _ => (mask, elems, ja + 1, jb + 1)
    | true, false =>
      match a.elements[ja]? with
      | some x => (setBit mask iu, elems.push x, ja + 1, jb)
      | none   => (mask, elems, ja + 1, jb)
    | false, true =>
      match b.elements[jb]? with
      | some y => (setBit mask iu, elems.push y, ja, jb + 1)
      | none   => (mask, elems, ja, jb + 1)
    | false, false => (mask, elems, ja, jb)
  let (mask, elems, _, _) := (List.range 32).foldl step ((0 : UInt32), (#[] : Array α), 0, 0)
  ⟨mask, elems⟩

/-- Intersection of two nodes. Only slots present in both survive, merged with
`combine`; a `none` result (empty intersection) drops the slot. -/
def meet (combine : α → α → Option α) (a b : Node α) : Node α :=
  let step := fun (st : UInt32 × Array α × Nat × Nat) i =>
    let (mask, elems, ja, jb) := st
    let iu := UInt32.ofNat i
    match testBit a.positionsMask iu, testBit b.positionsMask iu with
    | true, true =>
      match a.elements[ja]?, b.elements[jb]? with
      | some x, some y =>
        match combine x y with
        | some v => (setBit mask iu, elems.push v, ja + 1, jb + 1)
        | none   => (mask, elems, ja + 1, jb + 1)
      | _, _ => (mask, elems, ja + 1, jb + 1)
    | true, false => (mask, elems, ja + 1, jb)
    | false, true => (mask, elems, ja, jb + 1)
    | false, false => (mask, elems, ja, jb)
  let (mask, elems, _, _) := (List.range 32).foldl step ((0 : UInt32), (#[] : Array α), 0, 0)
  ⟨mask, elems⟩

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

end Tests

end NatCol
