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
@[inline] private def popCountAux (x : UInt32) : UInt32 :=
  let x : UInt32 := x - ((x >>> 1) &&& (0x55555555 : UInt32))
  let x : UInt32 := (x &&& (0x33333333 : UInt32)) + ((x >>> 2) &&& (0x33333333 : UInt32))
  let x : UInt32 := (x + (x >>> 4)) &&& (0x0F0F0F0F : UInt32)
  (x * (0x01010101 : UInt32)) >>> 24

@[inline] def popCount (x : UInt32) : Nat := (popCountAux x).toNat

#guard popCount 0 = 0
#guard popCount 1 = 1
#guard popCount 0xFFFFFFFF = 32
#guard popCount 0b10110 = 3
#guard popCount 0x80000000 = 1      -- high bit only
#guard popCount 0xAAAAAAAA = 16     -- alternating bits (even positions)
#guard popCount 0x55555555 = 16     -- alternating bits (odd positions)
#guard popCount 0x0F0F0F0F = 16     -- exercises the byte-fold step

/-- Is bit `i` of `x` set? `i` is expected in `0..31`. -/
@[inline] def testBit (x i : UInt32) : Bool := (x >>> i) &&& 1 == 1

#guard testBit 0b100 2
#guard !testBit 0b100 1

/-- Set bit `i` of `x`. -/
@[inline] def setBit (x i : UInt32) : UInt32 := x ||| (1 <<< i)

/-- Clear bit `i` of `x`. -/
@[inline] def clearBit (x i : UInt32) : UInt32 := x &&& ~~~(1 <<< i)

#guard setBit 0 3 = 0b1000
#guard clearBit 0b1010 3 = 0b10
#guard testBit (setBit 0 7) 7
#guard !testBit (clearBit (setBit 0 7) 7) 7

/-- Mask of all bits strictly below `i`, i.e. `2^i - 1`. -/
@[inline] def lowerMask (i : UInt32) : UInt32 := (1 <<< i) - 1

#guard lowerMask 0 = 0
#guard lowerMask 1 = 1
#guard lowerMask 5 = 0b11111

/-- Compact array index for slot `i` in a node whose present slots are `mask`:
the number of present slots strictly below `i`. -/
@[inline] def arrayIndex (mask i : UInt32) : Nat := popCount (mask &&& lowerMask i)

#guard arrayIndex 0b10110 1 = 0
#guard arrayIndex 0b10110 2 = 1
#guard arrayIndex 0b10110 4 = 2

/-- The 5-bit chunk of `k` at the given `level` (0 = least significant chunk). -/
@[inline] def chunk (k : Nat) (level : Nat) : UInt32 := UInt32.ofNat ((k >>> (5 * level)) &&& 31)

#guard chunk 42 0 = 10   -- 42 = 0b101010 -> low 5 bits 01010 = 10
#guard chunk 42 1 = 1    -- next chunk = 1
#guard chunk 31 0 = 31
#guard chunk 32 0 = 0
#guard chunk 32 1 = 1

/-- Minimal trie height able to hold key `k`: the index of `k`'s highest non-zero
chunk. A tree of `height h` holds exactly keys `< 32^(h+1)`. -/
def requiredHeight (k : Nat) : Nat :=
  if k < 32 then 0 else 1 + requiredHeight (k / 32)
termination_by k
decreasing_by omega

#guard requiredHeight 0 = 0
#guard requiredHeight 31 = 0
#guard requiredHeight 32 = 1
#guard requiredHeight 1023 = 1
#guard requiredHeight 1024 = 2
#guard requiredHeight 1048575 = 3   -- 32^4 - 1
#guard requiredHeight 1048576 = 4   -- 32^4

/-- Index of the lowest set bit of `m` (count of trailing zeros). The lowest set bit is isolated
by `m &&& (0 - m)` (a power of two); subtracting one yields a mask of exactly that many low bits,
whose population count is the bit's index. Only meaningful for `m ≠ 0`. Used to enumerate a node's
present slots in ascending order without scanning all 32. -/
@[inline] def lowestSetIdx (m : UInt32) : UInt32 := popCountAux ((m &&& (0 - m)) - 1)

/-- Clear the lowest set bit of `m`. Standard `m &&& (m - 1)` trick; pairs with `lowestSetIdx`
to step through present slots. -/
@[inline] def clearLowest (m : UInt32) : UInt32 := m &&& (m - 1)

#guard lowestSetIdx 0b10110 = 1
#guard lowestSetIdx 0b1000 = 3
#guard lowestSetIdx 1 = 0
#guard lowestSetIdx 0x80000000 = 31
#guard clearLowest 0b10110 = 0b10100
#guard clearLowest 1 = 0

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

/-- A `popCount`-bounded `UInt32` increments without wraparound, so `.toNat` distributes over the
`+ 1`. Every popcount increment below is a `UInt32` equation closed by `bv_decide`; this lemma is
the shared bridge back to the `Nat`-valued `popCount`, naming the "no overflow because `≤ 32`"
argument once instead of re-deriving it at each call site. -/
private theorem toNat_add_one_of_le {x : UInt32} (h : x.toNat ≤ 32) : (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add, show ((1 : UInt32).toNat) = 1 from rfl,
      show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_eq_of_lt (by omega)]

/-- The standard route from a `bv_decide`-proven `popCountAux` increment to the `Nat`-valued
`popCount` statement. Also covers the `arrayIndex` increments — `arrayIndex` is definitionally a
`popCount`. -/
private theorem popCount_eq_succ_of_aux {a b : UInt32} (key : popCountAux a = popCountAux b + 1) :
    popCount a = popCount b + 1 := by
  show (popCountAux a).toNat = (popCountAux b).toNat + 1
  rw [key]; exact toNat_add_one_of_le (popCountAux_toNat_le b)

/-! ### Lemmas backing the present-slot bit-scan (`lowestSetIdx`/`clearLowest`)

These drive the `Node.join`/`meet` merge loop, which steps through present slots via the lowest
set bit instead of scanning all 32. Each is a fixed-width fact about `UInt32`, discharged by
`bv_decide` (the SWAR `popCountAux` inside `lowestSetIdx` is itself just shifts/masks/one multiply,
which `bv_decide` bit-blasts). -/

/-- Clearing the lowest set bit strictly decreases the value — the merge loop's termination. -/
theorem clearLowest_lt (m : UInt32) (hm : m ≠ 0) : clearLowest m < m := by
  unfold clearLowest; bv_decide

/-- `clearLowest_lt` on `.toNat`, matching the `termination_by m.toNat` measure every
present-slot scan loop uses; their `decreasing_by` is exactly this lemma. -/
theorem toNat_clearLowest_lt (m : UInt32) (hm : m ≠ 0) : (clearLowest m).toNat < m.toNat :=
  UInt32.lt_iff_toNat_lt.mp (clearLowest_lt m hm)

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

/-- Clearing the lowest set bit lowers the population count by one — the per-step size fact of the
present-slot fold (`mergeKids` appends one child per cleared bit). -/
theorem popCount_clearLowest (m : UInt32) (hm : m ≠ 0) :
    popCount (clearLowest m) + 1 = popCount m :=
  (popCount_eq_succ_of_aux (by unfold popCountAux clearLowest at *; bv_decide)).symm

/-- Setting an unset bit raises the population count by one. -/
theorem popCount_setBit (m i : UInt32) (h : testBit m i = false) :
    popCount (setBit m i) = popCount m + 1 :=
  popCount_eq_succ_of_aux (by unfold popCountAux setBit testBit at *; bv_decide)

/-- Split a population count at the top bit (slot 31): the count below 31 plus the top bit.
Lets `Node.ext`'s forward element-extraction reach the full size at the `m = 32` boundary (where
`UInt32`'s `lowerMask` would wrap). -/
theorem popCount_split31 (m : UInt32) :
    popCount m = popCount (m &&& lowerMask 31) + (if testBit m 31 = true then 1 else 0) := by
  by_cases h31 : testBit m 31 = true
  · rw [if_pos h31]
    exact popCount_eq_succ_of_aux (by unfold popCountAux lowerMask testBit at *; bv_decide)
  · rw [if_neg h31, Nat.add_zero]
    simp only [Bool.not_eq_true] at h31
    exact congrArg UInt32.toNat (by unfold popCountAux lowerMask testBit at *; bv_decide)

/-- Clearing a set bit lowers the population count by one. -/
theorem popCount_clearBit (m i : UInt32) (h : testBit m i = true) :
    popCount (clearBit m i) + 1 = popCount m :=
  (popCount_eq_succ_of_aux (by unfold popCountAux clearBit testBit at *; bv_decide)).symm

/-- A nonzero mask has at least one set slot. -/
theorem one_le_popCount_of_ne_zero (m : UInt32) (h : m ≠ 0) : 1 ≤ popCount m := by
  have key : (1 : UInt32) ≤ popCountAux m := by revert h; unfold popCountAux; bv_decide
  show (1 : Nat) ≤ (popCountAux m).toNat
  exact UInt32.le_iff_toNat_le.mp key

/-- Population count is monotone under `|||`: a union of masks covers at least one operand. Bounds
the merged child count for the union of two `bin`s below by either side's (so it stays `≥ 2`). -/
theorem popCount_or_left (a b : UInt32) : popCount a ≤ popCount (a ||| b) := by
  have key : popCountAux a ≤ popCountAux (a ||| b) := by unfold popCountAux; bv_decide
  show (popCountAux a).toNat ≤ (popCountAux (a ||| b)).toNat
  exact UInt32.le_iff_toNat_le.mp key

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

/-- The lowest set bit sits at compact index `0` (nothing is below it). The base of the
present-slot fold's indexing: the first child appended lands at position `0`. -/
theorem arrayIndex_lowestSetIdx (m : UInt32) (hm : m ≠ 0) :
    arrayIndex m (lowestSetIdx m) = 0 := by
  have key : popCountAux (m &&& lowerMask (lowestSetIdx m)) = 0 := by
    unfold lowestSetIdx lowerMask popCountAux at *; bv_decide
  show (popCountAux (m &&& lowerMask (lowestSetIdx m))).toNat = 0
  rw [key]; rfl

/-- Clearing the lowest set bit drops every other set slot's compact index by one (the just-removed
lowest bit no longer counts below it). The fold's inductive index shift. -/
theorem arrayIndex_clearLowest_of_ne (m c : UInt32) (hc : c < 32)
    (htb : testBit m c = true) (hne : c ≠ lowestSetIdx m) :
    arrayIndex m c = arrayIndex (clearLowest m) c + 1 :=
  popCount_eq_succ_of_aux
    (by unfold lowestSetIdx clearLowest lowerMask testBit popCountAux at *; bv_decide)

/-- No bit of `0` is set. -/
theorem testBit_zero (i : UInt32) : testBit 0 i = false := by unfold testBit; bv_decide

/-! ### Mask lemmas backing the `NatCollection` canonical-shape invariant

The collection layer keeps each trie *canonical* — in particular no empty leaves. These
`bv_decide`-discharged facts about `setBit` feed the `Node`/`PTree` proofs. -/

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
    arrayIndex (setBit m i) j = arrayIndex m j + 1 :=
  popCount_eq_succ_of_aux (by unfold popCountAux setBit lowerMask testBit at *; bv_decide)

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

/-- Moving the slot up by one raises the compact index by the (just-passed) bit. Backs the
forward element-extraction in `Node.ext`. -/
theorem arrayIndex_succ (m i : UInt32) (hi : i < 31) :
    arrayIndex m (i + 1) = arrayIndex m i + (if testBit m i = true then 1 else 0) := by
  by_cases h : testBit m i = true
  · rw [if_pos h]
    exact popCount_eq_succ_of_aux (by unfold popCountAux lowerMask testBit at *; bv_decide)
  · rw [if_neg h, Nat.add_zero]; simp only [Bool.not_eq_true] at h
    exact congrArg UInt32.toNat (by unfold popCountAux lowerMask testBit at *; bv_decide)

/-- The compact index is injective on present slots. -/
theorem arrayIndex_inj (m a b : UInt32) (ha : a < 32) (hb : b < 32)
    (hpa : testBit m a = true) (hpb : testBit m b = true) (hab : a ≠ b) :
    arrayIndex m a ≠ arrayIndex m b := by
  rcases UInt32.lt_or_lt_of_ne hab with h | h
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

/-! ### Lemmas backing the intersection re-compression (`compactify`/`finalize`)

These feed `PTree`'s `meet`: after an intersection thins a branch, `compactify` drops the empty
children lowest-first and recomputes the surviving mask, which needs that the running accumulator's
bits stay strictly below the unprocessed mask (`lowestSetIdx` is the minimum) and that a mask whose
bits all sit below a slot indexes its full population there. -/

/-- `lowestSetIdx` is the *minimum* set slot: every present bit sits at or above it. Proved via the
strict monotonicity of the compact index — a bit below the lowest would index before slot 0. -/
theorem lowestSetIdx_le_of_testBit (m c : UInt32) (hc : c < 32) (h : testBit m c = true) :
    lowestSetIdx m ≤ c := by
  have hm : m ≠ 0 := by intro h0; rw [h0, testBit_zero] at h; exact absurd h (by decide)
  rcases Nat.lt_or_ge c.toNat (lowestSetIdx m).toNat with hlt | hge
  · exfalso
    have hlt' : c < lowestSetIdx m := UInt32.lt_iff_toNat_lt.mpr hlt
    have hcontra := arrayIndex_lt_of_lt m c (lowestSetIdx m) hc (lowestSetIdx_lt m hm) h hlt'
    rw [arrayIndex_lowestSetIdx m hm] at hcontra
    omega
  · exact UInt32.le_iff_toNat_le.mpr hge

/-- A slot below `i` is set in the low-mask `lowerMask i` (for in-range `i`). -/
private theorem testBit_lowerMask_lt (i c : UInt32) (hi : i < 32) (hlt : c < i) :
    testBit (lowerMask i) c = true := by
  unfold testBit lowerMask; bv_decide

/-- When every set bit of `m` lies strictly below slot `i`, `arrayIndex m i` counts all of `m`. -/
theorem arrayIndex_eq_popCount_of_below (m i : UInt32) (hi : i < 32)
    (h : ∀ c, c < 32 → testBit m c = true → c < i) : arrayIndex m i = popCount m := by
  have hand : m &&& lowerMask i = m := by
    apply eq_of_testBit_eq
    intro c hc
    rw [testBit_and]
    by_cases hb : testBit m c = true
    · rw [hb, testBit_lowerMask_lt i c hi (h c hc hb)]; rfl
    · simp only [Bool.not_eq_true] at hb; rw [hb]; rfl
  unfold arrayIndex; rw [hand]

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
private theorem chunk_eq_div_mod (k level : Nat) : chunk k level = UInt32.ofNat ((k / 32^level) % 32) := by
  unfold chunk
  congr 1
  rw [Nat.shiftRight_eq_div_pow, show (31 : Nat) = 2^5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.pow_mul, show (2:Nat)^5 = 32 from rfl]

/-- `requiredHeight` is below `h` exactly when the key fits in a height-`h` tree (`< 32^(h+1)`). -/
private theorem requiredHeight_le_iff_lt_pow : ∀ (h k : Nat), requiredHeight k ≤ h ↔ k < 32^(h+1) := by
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
  have hlt : i.toNat < 32 := UInt32.lt_iff_toNat_lt.mp hi
  rw [chunk_eq_div_mod, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hlt]
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hlt (by decide))]

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
