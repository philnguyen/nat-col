import Std.Tactic.BVDecide

/-!
# Bit utilities

Low-level `UInt32`/`Nat` helpers shared by the trie. A `Node`'s sparse slots are
addressed by a 32-bit `positionsMask`, and present children are stored compactly
using the standard HAMT index trick (popcount of the mask below a slot).

The `popCount`/`setBit`/`clearBit`/`arrayIndex` lemmas at the bottom are what let the
`Node` compactness invariant (`elements.size = popCount positionsMask`) be maintained by
every operation. They are discharged by `bv_decide` on the `UInt32`-valued core
`popCountAux`, then bridged to the `Nat`-valued `popCount`.
-/

namespace NatCol

----------------------------------------------------------------------------------------------------
-- Implementation
----------------------------------------------------------------------------------------------------

/-- Population-count core: the classic SWAR bit-twiddling algorithm — counts bits within
each pair, folds the partial sums up through 4-bit and 8-bit groups, then sums the four
byte counts with one multiply, all in a fixed handful of shifts/masks rather than a
32-iteration loop. Kept `UInt32`-valued (no `.toNat`) so `bv_decide` can reason about it. -/
@[inline] def popCountAux (x : UInt32) : UInt32 :=
  let x : UInt32 := x - ((x >>> 1) &&& (0x55555555 : UInt32))
  let x : UInt32 := (x &&& (0x33333333 : UInt32)) + ((x >>> 2) &&& (0x33333333 : UInt32))
  let x : UInt32 := (x + (x >>> 4)) &&& (0x0F0F0F0F : UInt32)
  (x * (0x01010101 : UInt32)) >>> 24

@[inline] def popCount (x : UInt32) : Nat := (popCountAux x).toNat

#guard popCount 0 == 0
#guard popCount 1 == 1
#guard popCount 0xFFFFFFFF == 32
#guard popCount 0b10110 == 3
#guard popCount 0x80000000 == 1      -- high bit only
#guard popCount 0xAAAAAAAA == 16     -- alternating bits (even positions)
#guard popCount 0x55555555 == 16     -- alternating bits (odd positions)
#guard popCount 0x0F0F0F0F == 16     -- exercises the byte-fold step

/-- Is bit `i` of `x` set? `i` is expected in `0..31`. -/
@[inline] def testBit (x i : UInt32) : Bool := (x >>> i) &&& 1 == 1

#guard testBit 0b100 2
#guard !testBit 0b100 1

/-- Set bit `i` of `x`. -/
@[inline] def setBit (x i : UInt32) : UInt32 := x ||| (1 <<< i)

/-- Clear bit `i` of `x`. -/
@[inline] def clearBit (x i : UInt32) : UInt32 := x &&& ~~~(1 <<< i)

#guard setBit 0 3 == 0b1000
#guard clearBit 0b1010 3 == 0b10
#guard testBit (setBit 0 7) 7
#guard !testBit (clearBit (setBit 0 7) 7) 7

/-- Mask of all bits strictly below `i`, i.e. `2^i - 1`. -/
@[inline] def lowerMask (i : UInt32) : UInt32 := (1 <<< i) - 1

#guard lowerMask 0 == 0
#guard lowerMask 1 == 1
#guard lowerMask 5 == 0b11111

/-- Compact array index for slot `i` in a node whose present slots are `mask`:
the number of present slots strictly below `i`. -/
@[inline] def arrayIndex (mask i : UInt32) : Nat := popCount (mask &&& lowerMask i)

#guard arrayIndex 0b10110 1 == 0
#guard arrayIndex 0b10110 2 == 1
#guard arrayIndex 0b10110 4 == 2

/-- The 5-bit chunk of `k` at the given `level` (0 = least significant chunk). -/
@[inline] def chunk (k : Nat) (level : Nat) : UInt32 := UInt32.ofNat ((k >>> (5 * level)) &&& 31)

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

/-- Index of the lowest set bit of `m` (count of trailing zeros). The lowest set bit is isolated
by `m &&& (0 - m)` (a power of two); subtracting one yields a mask of exactly that many low bits,
whose population count is the bit's index. Only meaningful for `m ≠ 0`. Used to enumerate a node's
present slots in ascending order without scanning all 32. -/
@[inline] def lowestSetIdx (m : UInt32) : UInt32 := popCountAux ((m &&& (0 - m)) - 1)

/-- Clear the lowest set bit of `m`. Standard `m &&& (m - 1)` trick; pairs with `lowestSetIdx`
to step through present slots. -/
@[inline] def clearLowest (m : UInt32) : UInt32 := m &&& (m - 1)

#guard lowestSetIdx 0b10110 == 1
#guard lowestSetIdx 0b1000 == 3
#guard lowestSetIdx 1 == 0
#guard lowestSetIdx 0x80000000 == 31
#guard clearLowest 0b10110 == 0b10100
#guard clearLowest 1 == 0

----------------------------------------------------------------------------------------------------
-- Theorems
----------------------------------------------------------------------------------------------------

/-! ### Lemmas backing the `Node` compactness invariant

`bv_decide` proves the increments over the `UInt32`-valued `popCountAux`; the `Nat`-valued
statements follow by `.toNat`, using that a popcount never exceeds 32 (so `+1` can't
overflow). The `setBit`/`clearBit` defs need no `i < 32` hypothesis: `<<<` shifts modulo
the width, so `1 <<< i` always sets exactly one bit. -/

private theorem popCountAux_le (x : UInt32) : popCountAux x ≤ 32 := by unfold popCountAux; bv_decide

private theorem popCountAux_toNat_le (x : UInt32) : (popCountAux x).toNat ≤ 32 := by
  have h := popCountAux_le x
  rwa [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat] at h

private theorem popCount_le (x : UInt32) : popCount x ≤ 32 := popCountAux_toNat_le x

/-! ### Lemmas backing the present-slot bit-scan (`lowestSetIdx`/`clearLowest`)

These drive the `Node.join`/`meet` merge loop, which steps through present slots via the lowest
set bit instead of scanning all 32. Each is a fixed-width fact about `UInt32`, discharged by
`bv_decide` (the SWAR `popCountAux` inside `lowestSetIdx` is itself just shifts/masks/one multiply,
which `bv_decide` bit-blasts). -/

/-- Clearing the lowest set bit strictly decreases the value — the merge loop's termination. -/
theorem clearLowest_lt (m : UInt32) (hm : m ≠ 0) : clearLowest m < m := by
  unfold clearLowest; bv_decide

/-- The lowest-set-bit index is a valid slot (`< 32`) when `m` is nonzero. -/
theorem lowestSetIdx_lt (m : UInt32) (hm : m ≠ 0) : lowestSetIdx m < 32 := by
  unfold lowestSetIdx popCountAux; bv_decide

/-- The lowest-set-bit index does name a set bit when `m` is nonzero. -/
theorem testBit_lowestSetIdx (m : UInt32) (hm : m ≠ 0) : testBit m (lowestSetIdx m) = true := by
  unfold testBit lowestSetIdx popCountAux; bv_decide

/-- `clearLowest` clears the lowest-set-bit slot. -/
theorem testBit_clearLowest_self (m : UInt32) (hm : m ≠ 0) :
    testBit (clearLowest m) (lowestSetIdx m) = false := by
  unfold testBit clearLowest lowestSetIdx popCountAux; bv_decide

/-- `clearLowest` leaves every (in-range) slot other than the lowest-set-bit one untouched. The
`s < 32` guard rules out `UInt32`'s mod-32 shift aliasing; all real slots are 5-bit `chunk`s. -/
theorem testBit_clearLowest_of_ne (m s : UInt32) (hs : s < 32) (h : s ≠ lowestSetIdx m) :
    testBit (clearLowest m) s = testBit m s := by
  unfold testBit clearLowest lowestSetIdx popCountAux at *; bv_decide

/-- `clearLowest` only ever clears bits: a slot set in `clearLowest m` was set in `m`. -/
theorem testBit_of_clearLowest (m s : UInt32) (h : testBit (clearLowest m) s = true) :
    testBit m s = true := by
  unfold testBit clearLowest at *; bv_decide

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

/-! ### Mask lemmas backing the `NatCollection` canonical-shape invariant

The collection layer keeps each trie *canonical*, in particular height-minimal: the top
node has a slot ≥ 1 set, encoded as `2 ≤ positionsMask`. These `bv_decide`-discharged facts
about `setBit` and that bound feed the `Node`/`Tree`/`Collection` proofs. -/

theorem two_le_of_ne (m : UInt32) (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by bv_decide

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

theorem uint32_le_of_lt {a b : UInt32} (h : a < b) : a ≤ b :=
  UInt32.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt32.lt_iff_toNat_lt.mp h))

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

theorem testBit_or (a b i : UInt32) : testBit (a ||| b) i = (testBit a i || testBit b i) := by
  unfold testBit; bv_decide

theorem testBit_and (a b i : UInt32) : testBit (a &&& b) i = (testBit a i && testBit b i) := by
  unfold testBit; bv_decide

/-- A mask that is height-minimal (`2 ≤ m`) has a set bit above slot 0 — that high bit is what
forces the height in the canonical-shape invariant. -/
theorem exists_high_bit (m : UInt32) (h : 2 ≤ m) :
    ∃ s, 1 ≤ s ∧ s < 32 ∧ testBit m s = true := by
  rcases Classical.em (∃ s, 1 ≤ s ∧ s < 32 ∧ testBit m s = true) with hyes | hno
  · exact hyes
  · exfalso
    have hbits : ∀ s, 1 ≤ s → s < 32 → testBit m s = false := by
      intro s h1 h2
      cases hb : testBit m s with
      | false => rfl
      | true => exact absurd ⟨s, h1, h2, hb⟩ hno
    have hm1 : m = m &&& 1 := by
      apply eq_of_testBit_eq
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        rw [show testBit (m &&& 1) 0 = (testBit m 0 && testBit (1:UInt32) 0) from by unfold testBit; bv_decide,
            show testBit (1:UInt32) 0 = true from by decide]
        simp
      · have h1i : 1 ≤ i := by revert hi0; bv_decide
        rw [hbits i h1i hi,
            show testBit (m &&& 1) i = (testBit m i && testBit (1:UInt32) i) from by unfold testBit; bv_decide,
            hbits i h1i hi]
        simp
    have hcon : (2:UInt32) ≤ m → m = m &&& 1 → False := by intro h2 he; rw [he] at h2; bv_decide
    exact hcon h hm1

/-- A 5-bit chunk is always a valid slot index (`< 32`). -/
theorem chunk_lt (k level : Nat) : chunk k level < 32 := by
  have hle : (k >>> (5 * level)) &&& 31 ≤ 31 := Nat.and_le_right
  have hlt : (k >>> (5 * level)) &&& 31 < UInt32.size := Nat.lt_of_le_of_lt hle (by decide)
  have e2 : (32 : UInt32).toNat = 32 := by decide
  rw [chunk, UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hlt, e2]
  omega

/-! ### `chunk` and `requiredHeight` as arithmetic

The bitwise `chunk`/`requiredHeight` definitions are restated as base-32 `div`/`mod` so the
trie-extensionality (`Tree.ext`) and `get?`-characterization proofs can probe keys and bound
chunk levels with ordinary `Nat` arithmetic (`omega` + the `Nat.*_div_*` lemmas). -/

/-- `0 < 32^n` (kept around so the `div`/`mod` rewrites below have their positivity side goal). -/
private theorem pow32_pos (n : Nat) : 0 < 32^n := Nat.pow_pos (by decide)

/-- The 5-bit chunk at `level` is the base-32 digit: divide out the lower levels, take mod 32. -/
theorem chunk_eq_div_mod (k level : Nat) : chunk k level = UInt32.ofNat ((k / 32^level) % 32) := by
  unfold chunk
  congr 1
  rw [Nat.shiftRight_eq_div_pow, show (31 : Nat) = 2^5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.pow_mul, show (2:Nat)^5 = 32 from rfl]

/-- `requiredHeight` is below `h` exactly when the key fits in a height-`h` tree (`< 32^(h+1)`). -/
theorem requiredHeight_le_iff_lt_pow : ∀ (h k : Nat), requiredHeight k ≤ h ↔ k < 32^(h+1) := by
  intro h
  induction h with
  | zero =>
    intro k
    rw [requiredHeight]
    by_cases hk : k < 32
    · simp only [if_pos hk]; exact ⟨fun _ => hk, fun _ => Nat.le_refl 0⟩
    · simp only [if_neg hk]
      constructor
      · intro h; omega
      · intro h; omega
  | succ h ih =>
    intro k
    rw [requiredHeight]
    by_cases hk : k < 32
    · have : k < 32^(h+2) := Nat.lt_of_lt_of_le hk (Nat.le_trans (by decide : (32:Nat) ≤ 32^1)
        (Nat.pow_le_pow_right (by decide) (by omega)))
      simp only [if_pos hk]; exact ⟨fun _ => this, fun _ => Nat.zero_le _⟩
    · simp only [if_neg hk]
      rw [show ∀ a, (1 + a ≤ h + 1) ↔ (a ≤ h) from fun a => by omega, ih (k/32),
          show (32:Nat)^(h+1+1) = 32^(h+1) * 32 from by rw [Nat.pow_succ]]
      exact Nat.div_lt_iff_lt_mul (by decide)

theorem requiredHeight_le_of_lt_pow {k h : Nat} (hk : k < 32^(h+1)) : requiredHeight k ≤ h :=
  (requiredHeight_le_iff_lt_pow h k).mpr hk

theorem lt_pow_of_requiredHeight_le {k h : Nat} (hk : requiredHeight k ≤ h) : k < 32^(h+1) :=
  (requiredHeight_le_iff_lt_pow h k).mp hk

/-- A key smaller than `32^j` has a zero chunk at level `j` (no bits reach that window). -/
theorem chunk_eq_zero_of_lt {k j : Nat} (hk : k < 32^j) : chunk k j = 0 := by
  rw [chunk_eq_div_mod, Nat.div_eq_of_lt hk]
  rfl

/-- Chunks above the required height are zero. -/
theorem chunk_eq_zero_of_requiredHeight_lt {k h j : Nat} (hk : requiredHeight k ≤ h) (hj : h < j) :
    chunk k j = 0 :=
  chunk_eq_zero_of_lt (Nat.lt_of_lt_of_le (lt_pow_of_requiredHeight_le hk)
    (Nat.pow_le_pow_right (by decide) (by omega)))

/-- At its own required height (`> 0`), a key's chunk is non-zero — that is what makes the height
minimal. -/
theorem chunk_ne_zero_of_requiredHeight_eq {k h : Nat} (hk : requiredHeight k = h + 1) :
    chunk k (h + 1) ≠ 0 := by
  have hge : ¬ k < 32^(h+1) := fun hlt => by
    have := requiredHeight_le_of_lt_pow hlt; omega
  have hlt : k < 32^(h+2) := lt_pow_of_requiredHeight_le (by omega)
  rw [chunk_eq_div_mod]
  have hq1 : 1 ≤ k / 32^(h+1) := (Nat.one_le_div_iff (pow32_pos _)).mpr (Nat.le_of_not_lt hge)
  have hq2 : k / 32^(h+1) < 32 := by
    rw [Nat.div_lt_iff_lt_mul (pow32_pos _), Nat.mul_comm, ← Nat.pow_succ]; exact hlt
  rw [Nat.mod_eq_of_lt hq2]
  intro hzero
  have : k / 32^(h+1) = 0 := by
    have h0 : (UInt32.ofNat (k / 32^(h+1))).toNat = (0 : UInt32).toNat := by rw [hzero]
    rwa [UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hq2 (by decide)),
        show ((0:UInt32).toNat) = 0 from rfl] at h0
  omega

theorem chunk_toNat_zero (i : UInt32) (hi : i < 32) : chunk i.toNat 0 = i := by
  have hlt : i.toNat < 32 := by
    have := UInt32.lt_iff_toNat_lt.mp hi; rwa [show (32:UInt32).toNat = 32 from by decide] at this
  rw [chunk_eq_div_mod, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hlt]
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hlt (by decide))]

/-- Probe key for slot `s` at level `h+1`, carrying lower bits `k'`: its top chunk reads `s`. -/
theorem chunk_probe_high (s : UInt32) (k' h : Nat) (hk' : k' < 32^(h+1)) (hs : s < 32) :
    chunk (k' + s.toNat * 32^(h+1)) (h+1) = s := by
  have hslt : s.toNat < 32 := by
    have := UInt32.lt_iff_toNat_lt.mp hs; rwa [show (32:UInt32).toNat = 32 from by decide] at this
  rw [chunk_eq_div_mod, Nat.add_mul_div_right _ _ (pow32_pos _), Nat.div_eq_of_lt hk',
      Nat.zero_add, Nat.mod_eq_of_lt hslt]
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hslt (by decide))]

theorem chunk_probe_low (s : UInt32) (k' h j : Nat) (hj : j ≤ h) :
    chunk (k' + s.toNat * 32^(h+1)) j = chunk k' j := by
  rw [chunk_eq_div_mod, chunk_eq_div_mod]
  congr 1
  have e1 : s.toNat * 32^(h+1) = (s.toNat * 32^(h+1-j)) * 32^j := by
    rw [Nat.mul_assoc, ← Nat.pow_add, show (h+1-j)+j = h+1 from by omega]
  have e2 : s.toNat * 32^(h+1-j) = (s.toNat * 32^(h-j)) * 32 := by
    rw [show h+1-j = h-j+1 from by omega, Nat.pow_succ, Nat.mul_assoc]
  rw [e1, Nat.add_mul_div_right _ _ (pow32_pos j), e2, Nat.add_mul_mod_self_right]

/-- Reducing a key modulo `32^(h+1)` leaves its chunks `0..h` unchanged: those chunks read the
low `h+1` base-32 digits, which the reduction preserves. Lets a lookup at height `h` ignore a
key's high digits (used in the forward direction of `restrictsEq_iff`). -/
theorem chunk_mod_pow (k h j : Nat) (hj : j ≤ h) : chunk (k % 32^(h+1)) j = chunk k j := by
  rw [chunk_eq_div_mod, chunk_eq_div_mod]
  congr 1
  have hsplit : (32 : Nat)^(h+1) = 32^j * 32^(h+1-j) := by rw [← Nat.pow_add]; congr 1; omega
  have hdvd : (32 : Nat) ∣ 32^(h+1-j) :=
    ⟨32^(h-j), by rw [show h+1-j = (h-j)+1 from by omega, Nat.pow_succ, Nat.mul_comm]⟩
  rw [hsplit, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdvd]

theorem requiredHeight_probe_le (s : UInt32) (k' h : Nat) (hk' : k' < 32^(h+1)) (hs : s < 32) :
    requiredHeight (k' + s.toNat * 32^(h+1)) ≤ h + 1 := by
  have hslt : s.toNat < 32 := by
    have := UInt32.lt_iff_toNat_lt.mp hs; rwa [show (32:UInt32).toNat = 32 from by decide] at this
  apply requiredHeight_le_of_lt_pow
  rw [show (32:Nat)^(h+1+1) = 32^(h+1) * 32 from by rw [Nat.pow_succ]]
  calc k' + s.toNat * 32^(h+1) < 32^(h+1) + s.toNat * 32^(h+1) := by omega
    _ = (1 + s.toNat) * 32^(h+1) := by rw [Nat.add_mul, Nat.one_mul]
    _ = 32^(h+1) * (1 + s.toNat) := by rw [Nat.mul_comm]
    _ ≤ 32^(h+1) * 32 := Nat.mul_le_mul (Nat.le_refl _) (by omega)

private theorem digit_eq_of_chunk_eq {j k i : Nat} (h : chunk j i = chunk k i) :
    j / 32^i % 32 = k / 32^i % 32 := by
  rw [chunk_eq_div_mod, chunk_eq_div_mod] at h
  have hj : j / 32^i % 32 < 32 := Nat.mod_lt _ (by decide)
  have hk : k / 32^i % 32 < 32 := Nat.mod_lt _ (by decide)
  have h' := congrArg UInt32.toNat h
  rwa [UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hj (by decide)),
       UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hk (by decide))] at h'

/-- Two keys whose chunks agree on every level `0..h`, both small enough for a height-`h` tree,
are equal. The bridge from a `get?`-after-`insert` lookup matching at the inserted key (where the
lookup paths coincide chunk-by-chunk) back to key equality. -/
theorem eq_of_chunk_eq : (h : Nat) → (j k : Nat) → requiredHeight j ≤ h → requiredHeight k ≤ h →
    (∀ i, i ≤ h → chunk j i = chunk k i) → j = k
  | 0, j, k, hj, hk, hc => by
      have hjlt : j < 32 := by
        rcases Nat.lt_or_ge j 32 with h' | h'
        · exact h'
        · rw [requiredHeight, if_neg (show ¬ j < 32 by omega)] at hj; omega
      have hklt : k < 32 := by
        rcases Nat.lt_or_ge k 32 with h' | h'
        · exact h'
        · rw [requiredHeight, if_neg (show ¬ k < 32 by omega)] at hk; omega
      have hd := digit_eq_of_chunk_eq (hc 0 (Nat.le_refl 0))
      rwa [Nat.pow_zero, Nat.div_one, Nat.div_one, Nat.mod_eq_of_lt hjlt, Nat.mod_eq_of_lt hklt] at hd
  | h + 1, j, k, hj, hk, hc => by
      have hmod : j % 32 = k % 32 := by
        have hd := digit_eq_of_chunk_eq (hc 0 (Nat.zero_le _))
        rwa [Nat.pow_zero, Nat.div_one, Nat.div_one] at hd
      have hdiv : j / 32 = k / 32 := by
        refine eq_of_chunk_eq h (j / 32) (k / 32) ?_ ?_ ?_
        · apply requiredHeight_le_of_lt_pow
          have hjp : j < 32^(h+1) * 32 := by
            have h1 := lt_pow_of_requiredHeight_le hj; rwa [Nat.pow_succ] at h1
          exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hjp
        · apply requiredHeight_le_of_lt_pow
          have hkp : k < 32^(h+1) * 32 := by
            have h1 := lt_pow_of_requiredHeight_le hk; rwa [Nat.pow_succ] at h1
          exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hkp
        · intro i hi
          have e : ∀ a : Nat, chunk (a / 32) i = chunk a (i + 1) := by
            intro a
            rw [chunk_eq_div_mod, chunk_eq_div_mod, Nat.div_div_eq_div_mul,
                show (32 : Nat) * 32^i = 32^(i+1) from by rw [Nat.mul_comm, ← Nat.pow_succ]]
          rw [e j, e k]
          exact hc (i + 1) (by omega)
      omega

end NatCol
