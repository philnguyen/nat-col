import Std.Tactic.BVDecide

/-!
# Bit utilities

Low-level `UInt32`/`Nat` helpers shared by the trie. Keys are decomposed into 5-bit
chunks (base-32 digits); each trie level dispatches on one chunk. A `Node`'s sparse
slots are addressed by a 32-bit `positionsMask`, and present children are stored
compactly using the standard HAMT index trick (popcount of the mask below a slot).

The `popCount`/`setBit`/`clearBit`/`arrayIndex` lemmas at the bottom are what let the
`Node` compactness invariant (`elements.size = popCount positionsMask`) be maintained by
every operation. They are discharged by `bv_decide` on the `UInt32`-valued core
`popCountAux`, then bridged to the `Nat`-valued `popCount`.
-/

namespace NatCol

/-- Population-count core: the classic SWAR bit-twiddling algorithm — counts bits within
each pair, folds the partial sums up through 4-bit and 8-bit groups, then sums the four
byte counts with one multiply, all in a fixed handful of shifts/masks rather than a
32-iteration loop. Kept `UInt32`-valued (no `.toNat`) so `bv_decide` can reason about it. -/
def popCountAux (x : UInt32) : UInt32 :=
  let x : UInt32 := x - ((x >>> 1) &&& (0x55555555 : UInt32))
  let x : UInt32 := (x &&& (0x33333333 : UInt32)) + ((x >>> 2) &&& (0x33333333 : UInt32))
  let x : UInt32 := (x + (x >>> 4)) &&& (0x0F0F0F0F : UInt32)
  (x * (0x01010101 : UInt32)) >>> 24

/-- Number of set bits in `x` (population count). -/
def popCount (x : UInt32) : Nat := (popCountAux x).toNat

#guard popCount 0 == 0
#guard popCount 1 == 1
#guard popCount 0xFFFFFFFF == 32
#guard popCount 0b10110 == 3
#guard popCount 0x80000000 == 1      -- high bit only
#guard popCount 0xAAAAAAAA == 16     -- alternating bits (even positions)
#guard popCount 0x55555555 == 16     -- alternating bits (odd positions)
#guard popCount 0x0F0F0F0F == 16     -- exercises the byte-fold step

/-- Is bit `i` of `x` set? `i` is expected in `0..31`. -/
def testBit (x i : UInt32) : Bool := (x >>> i) &&& 1 == 1

#guard testBit 0b100 2
#guard !testBit 0b100 1

/-- Set bit `i` of `x`. -/
def setBit (x i : UInt32) : UInt32 := x ||| (1 <<< i)

/-- Clear bit `i` of `x`. -/
def clearBit (x i : UInt32) : UInt32 := x &&& ~~~(1 <<< i)

#guard setBit 0 3 == 0b1000
#guard clearBit 0b1010 3 == 0b10
#guard testBit (setBit 0 7) 7
#guard !testBit (clearBit (setBit 0 7) 7) 7

/-- Mask of all bits strictly below `i`, i.e. `2^i - 1`. -/
def lowerMask (i : UInt32) : UInt32 := (1 <<< i) - 1

#guard lowerMask 0 == 0
#guard lowerMask 1 == 1
#guard lowerMask 5 == 0b11111

/-- Compact array index for slot `i` in a node whose present slots are `mask`:
the number of present slots strictly below `i`. -/
def arrayIndex (mask i : UInt32) : Nat := popCount (mask &&& lowerMask i)

#guard arrayIndex 0b10110 1 == 0
#guard arrayIndex 0b10110 2 == 1
#guard arrayIndex 0b10110 4 == 2

/-! ### Lemmas backing the `Node` compactness invariant

`bv_decide` proves the increments over the `UInt32`-valued `popCountAux`; the `Nat`-valued
statements follow by `.toNat`, using that a popcount never exceeds 32 (so `+1` can't
overflow). The `setBit`/`clearBit` defs need no `i < 32` hypothesis: `<<<` shifts modulo
the width, so `1 <<< i` always sets exactly one bit. -/

/-- A population count never exceeds 32. -/
private theorem popCountAux_le (x : UInt32) : popCountAux x ≤ 32 := by unfold popCountAux; bv_decide

private theorem popCountAux_toNat_le (x : UInt32) : (popCountAux x).toNat ≤ 32 := by
  have h := popCountAux_le x
  rwa [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat] at h

private theorem popCount_le (x : UInt32) : popCount x ≤ 32 := popCountAux_toNat_le x

/-- Setting an unset bit raises the population count by one. -/
theorem popCount_setBit (m i : UInt32) (h : testBit m i = false) :
    popCount (setBit m i) = popCount m + 1 := by
  have key : popCountAux (setBit m i) = popCountAux m + 1 := by
    unfold popCountAux setBit testBit at *; bv_decide
  have hb := popCountAux_toNat_le m
  show (popCountAux (setBit m i)).toNat = (popCountAux m).toNat + 1
  rw [key, UInt32.toNat_add, show ((1 : UInt32).toNat) = 1 from rfl,
      show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_eq_of_lt (by omega)]

/-- Clearing a set bit lowers the population count by one. -/
theorem popCount_clearBit (m i : UInt32) (h : testBit m i = true) :
    popCount (clearBit m i) + 1 = popCount m := by
  have key : popCountAux (clearBit m i) + 1 = popCountAux m := by
    unfold popCountAux clearBit testBit at *; bv_decide
  have hb := popCountAux_toNat_le (clearBit m i)
  show (popCountAux (clearBit m i)).toNat + 1 = (popCountAux m).toNat
  have e : (popCountAux (clearBit m i) + 1).toNat = (popCountAux m).toNat := by rw [key]
  rw [UInt32.toNat_add, show ((1 : UInt32).toNat) = 1 from rfl,
      show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_eq_of_lt (by omega)] at e
  exact e

/-- The compact index of any slot is at most the node's size. -/
theorem arrayIndex_le (m i : UInt32) : arrayIndex m i ≤ popCount m := by
  have key : popCountAux (m &&& lowerMask i) ≤ popCountAux m := by
    unfold popCountAux lowerMask; bv_decide
  show (popCountAux (m &&& lowerMask i)).toNat ≤ (popCountAux m).toNat
  exact UInt32.le_iff_toNat_le.mp key

/-- The compact index of a *present* slot is strictly below the node's size (so it is a
valid array position). -/
theorem arrayIndex_lt (m i : UInt32) (h : testBit m i = true) :
    arrayIndex m i < popCount m := by
  have key : popCountAux (m &&& lowerMask i) < popCountAux m := by
    unfold popCountAux lowerMask testBit at *; bv_decide
  show (popCountAux (m &&& lowerMask i)).toNat < (popCountAux m).toNat
  exact UInt32.lt_iff_toNat_lt.mp key

/-- No bit of `0` is set. -/
theorem testBit_zero (i : UInt32) : testBit 0 i = false := by unfold testBit; bv_decide

/-- The 5-bit chunk of `k` at the given `level` (0 = least significant chunk). -/
def chunk (k : Nat) (level : Nat) : UInt32 := UInt32.ofNat ((k >>> (5 * level)) &&& 31)

#guard chunk 42 0 == 10   -- 42 = 0b101010 -> low 5 bits 01010 = 10
#guard chunk 42 1 == 1    -- next chunk = 1
#guard chunk 31 0 == 31
#guard chunk 32 0 == 0
#guard chunk 32 1 == 1

/-- Minimal trie height able to hold key `k`: the index of `k`'s highest non-zero
chunk. A tree of `height h` holds exactly keys `< 32^(h+1)`. -/
def requiredHeight (k : Nat) : Nat :=
  if k < 32 then 0 else 1 + requiredHeight (k / 32)
termination_by k
decreasing_by omega

#guard requiredHeight 0 == 0
#guard requiredHeight 31 == 0
#guard requiredHeight 32 == 1
#guard requiredHeight 1023 == 1
#guard requiredHeight 1024 == 2
#guard requiredHeight 1048575 == 3   -- 32^4 - 1
#guard requiredHeight 1048576 == 4   -- 32^4

/-! ### Mask lemmas backing the `NatCollection` canonical-shape invariant

The collection layer keeps each trie *canonical*, in particular height-minimal: the top
node has a slot ≥ 1 set, encoded as `2 ≤ positionsMask`. These `bv_decide`-discharged facts
about `setBit` and that bound feed the `Node`/`Tree`/`Collection` proofs. -/

/-- A `UInt32` that is neither `0` nor `1` is at least `2`. -/
theorem two_le_of_ne (m : UInt32) (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by bv_decide

/-- Setting a bit never zeroes a mask. -/
theorem setBit_ne_zero (m i : UInt32) : setBit m i ≠ 0 := by unfold setBit; bv_decide

/-- Setting an already-set bit is a no-op (so `insert` leaves the mask unchanged when the
slot is already present). -/
theorem setBit_eq_of_testBit (m i : UInt32) (h : testBit m i = true) : setBit m i = m := by
  unfold setBit testBit at *; bv_decide

end NatCol
