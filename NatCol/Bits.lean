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

/-- Split a population count at the top bit (slot 31): the count below 31 plus the top bit.
Lets `Node.ext`'s forward element-extraction reach the full size at the `m = 32` boundary (where
`UInt32`'s `lowerMask` would wrap). -/
theorem popCount_split31 (m : UInt32) :
    popCount m = popCount (m &&& lowerMask 31) + (if testBit m 31 = true then 1 else 0) := by
  by_cases h31 : testBit m 31 = true
  · rw [if_pos h31]
    have key : popCountAux m = popCountAux (m &&& lowerMask 31) + 1 := by
      unfold popCountAux lowerMask testBit at *; bv_decide
    have hb := popCountAux_toNat_le (m &&& lowerMask 31)
    show (popCountAux m).toNat = (popCountAux (m &&& lowerMask 31)).toNat + 1
    rw [key, UInt32.toNat_add, show ((1 : UInt32).toNat) = 1 from rfl,
        show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h31]
    simp only [Bool.not_eq_true] at h31
    have key : popCountAux m = popCountAux (m &&& lowerMask 31) := by
      unfold popCountAux lowerMask testBit at *; bv_decide
    show (popCountAux m).toNat = (popCountAux (m &&& lowerMask 31)).toNat + 0
    rw [key, Nat.add_zero]

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

/-! ### Compact-index movement under `setBit`

These feed `Node.get?_insert`: inserting at slot `i` either overwrites in place (slot present)
or `insertIdx`s a fresh value, and these `bv_decide`-discharged popcount facts pin down how the
compact index `arrayIndex` of each other slot moves. All require slots `< 32` because `UInt32`
shifts are taken modulo the width (so `testBit`/`setBit`/`lowerMask` are periodic above bit 31). -/

/-- `setBit m i` reads exactly slot `i` on top of `m` (for in-range slots). -/
theorem testBit_setBit (m i j : UInt32) (hi : i < 32) (hj : j < 32) :
    testBit (setBit m i) j = (testBit m j || (i == j)) := by
  unfold testBit setBit; bv_decide

/-- Setting bit `i` does not move the compact index of slot `i` (no bit *below* `i` changes). -/
theorem arrayIndex_setBit_self (m i : UInt32) : arrayIndex (setBit m i) i = arrayIndex m i := by
  unfold arrayIndex
  rw [show (setBit m i) &&& lowerMask i = m &&& lowerMask i from by unfold setBit lowerMask; bv_decide]

/-- Setting bit `i` does not move the compact index of any slot `j ≤ i`. -/
theorem arrayIndex_setBit_of_le (m i j : UInt32) (hi : i < 32) (hj : j < 32) (hji : j ≤ i) :
    arrayIndex (setBit m i) j = arrayIndex m j := by
  have key : (setBit m i) &&& lowerMask j = m &&& lowerMask j := by unfold setBit lowerMask; bv_decide
  unfold arrayIndex; rw [key]

/-- Setting a previously-unset bit `i` raises the compact index of every slot `j > i` by one. -/
theorem arrayIndex_setBit_of_gt (m i j : UInt32) (hi : i < 32) (hj : j < 32)
    (hij : i < j) (habs : testBit m i = false) :
    arrayIndex (setBit m i) j = arrayIndex m j + 1 := by
  have key : popCountAux ((setBit m i) &&& lowerMask j) = popCountAux (m &&& lowerMask j) + 1 := by
    unfold popCountAux setBit lowerMask testBit at *; bv_decide
  have hb := popCountAux_toNat_le (m &&& lowerMask j)
  show (popCountAux ((setBit m i) &&& lowerMask j)).toNat = (popCountAux (m &&& lowerMask j)).toNat + 1
  rw [key, UInt32.toNat_add, show ((1 : UInt32).toNat) = 1 from rfl,
      show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_eq_of_lt (by omega)]

/-- The compact index is strictly monotone on present slots. -/
theorem arrayIndex_lt_of_lt (m a b : UInt32) (ha : a < 32) (hb : b < 32)
    (h1 : testBit m a = true) (h2 : a < b) : arrayIndex m a < arrayIndex m b := by
  have key : popCountAux (m &&& lowerMask a) < popCountAux (m &&& lowerMask b) := by
    unfold popCountAux lowerMask testBit at *; bv_decide
  show (popCountAux (m &&& lowerMask a)).toNat < (popCountAux (m &&& lowerMask b)).toNat
  exact UInt32.lt_iff_toNat_lt.mp key

/-- The compact index is (non-strictly) monotone in the slot. -/
theorem arrayIndex_le_of_le (m a b : UInt32) (ha : a < 32) (hb : b < 32) (h : a ≤ b) :
    arrayIndex m a ≤ arrayIndex m b := by
  have key : popCountAux (m &&& lowerMask a) ≤ popCountAux (m &&& lowerMask b) := by
    unfold popCountAux lowerMask; bv_decide
  show (popCountAux (m &&& lowerMask a)).toNat ≤ (popCountAux (m &&& lowerMask b)).toNat
  exact UInt32.le_iff_toNat_le.mp key

/-- Strict `UInt32` order entails `≤`. -/
theorem uint32_le_of_lt {a b : UInt32} (h : a < b) : a ≤ b :=
  UInt32.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt32.lt_iff_toNat_lt.mp h))

/-- Distinct `UInt32`s are strictly comparable one way or the other. -/
theorem lt_or_gt_uint32 {a b : UInt32} (h : a ≠ b) : a < b ∨ a > b := by
  rcases Nat.lt_trichotomy a.toNat b.toNat with hlt | heq | hgt
  · exact Or.inl (UInt32.lt_iff_toNat_lt.mpr hlt)
  · exact absurd (UInt32.toNat_inj.mp heq) h
  · exact Or.inr (UInt32.lt_iff_toNat_lt.mpr hgt)

/-- Moving the slot up by one raises the compact index by the (just-passed) bit. Backs the
forward element-extraction in `Node.ext`. -/
theorem arrayIndex_succ (m i : UInt32) (hi : i < 31) :
    arrayIndex m (i + 1) = arrayIndex m i + (if testBit m i = true then 1 else 0) := by
  by_cases h : testBit m i = true
  · rw [if_pos h]
    have key : popCountAux (m &&& lowerMask (i + 1)) = popCountAux (m &&& lowerMask i) + 1 := by
      unfold popCountAux lowerMask testBit at *; bv_decide
    have hb := popCountAux_toNat_le (m &&& lowerMask i)
    show (popCountAux (m &&& lowerMask (i + 1))).toNat = (popCountAux (m &&& lowerMask i)).toNat + 1
    rw [key, UInt32.toNat_add, show ((1 : UInt32).toNat) = 1 from rfl,
        show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h]; simp only [Bool.not_eq_true] at h
    have key : popCountAux (m &&& lowerMask (i + 1)) = popCountAux (m &&& lowerMask i) := by
      unfold popCountAux lowerMask testBit at *; bv_decide
    show (popCountAux (m &&& lowerMask (i + 1))).toNat = (popCountAux (m &&& lowerMask i)).toNat + 0
    rw [key, Nat.add_zero]

/-- The compact index is injective on present slots. -/
theorem arrayIndex_inj (m a b : UInt32) (ha : a < 32) (hb : b < 32)
    (hpa : testBit m a = true) (hpb : testBit m b = true) (hab : a ≠ b) :
    arrayIndex m a ≠ arrayIndex m b := by
  rcases lt_or_gt_uint32 hab with h | h
  · exact Nat.ne_of_lt (arrayIndex_lt_of_lt m a b ha hb hpa h)
  · exact Nat.ne_of_gt (arrayIndex_lt_of_lt m b a hb ha hpb h)

/-- Bit extensionality: two masks agreeing on every bit are equal. A `UInt32` has exactly 32
bits, so it suffices to know they agree at slots `0..31`; `bv_decide` then closes `a = b` from
those 32 concrete bit equalities. Backs `Node.ext` (a node's mask is recovered from which slots
its `get?` reports present). -/
theorem eq_of_testBit_eq {a b : UInt32} (h : ∀ i, i < 32 → testBit a i = testBit b i) : a = b := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide); have h5 := h 5 (by decide)
  have h6 := h 6 (by decide); have h7 := h 7 (by decide); have h8 := h 8 (by decide)
  have h9 := h 9 (by decide); have h10 := h 10 (by decide); have h11 := h 11 (by decide)
  have h12 := h 12 (by decide); have h13 := h 13 (by decide); have h14 := h 14 (by decide)
  have h15 := h 15 (by decide); have h16 := h 16 (by decide); have h17 := h 17 (by decide)
  have h18 := h 18 (by decide); have h19 := h 19 (by decide); have h20 := h 20 (by decide)
  have h21 := h 21 (by decide); have h22 := h 22 (by decide); have h23 := h 23 (by decide)
  have h24 := h 24 (by decide); have h25 := h 25 (by decide); have h26 := h 26 (by decide)
  have h27 := h 27 (by decide); have h28 := h 28 (by decide); have h29 := h 29 (by decide)
  have h30 := h 30 (by decide); have h31 := h 31 (by decide)
  clear h
  unfold testBit at *
  bv_decide

/-- `testBit` distributes over bitwise-or. -/
theorem testBit_or (a b i : UInt32) : testBit (a ||| b) i = (testBit a i || testBit b i) := by
  unfold testBit; bv_decide

/-- A 5-bit chunk is always a valid slot index (`< 32`). -/
theorem chunk_lt (k level : Nat) : chunk k level < 32 := by
  have hle : (k >>> (5 * level)) &&& 31 ≤ 31 := Nat.and_le_right
  have hlt : (k >>> (5 * level)) &&& 31 < UInt32.size := Nat.lt_of_le_of_lt hle (by decide)
  have e2 : (32 : UInt32).toNat = 32 := by decide
  rw [chunk, UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hlt, e2]
  omega

end NatCol
