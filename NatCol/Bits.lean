/-!
# Bit utilities

Low-level `UInt32`/`Nat` helpers shared by the trie. Keys are decomposed into 5-bit
chunks (base-32 digits); each trie level dispatches on one chunk. A `Node`'s sparse
slots are addressed by a 32-bit `positionsMask`, and present children are stored
compactly using the standard HAMT index trick (popcount of the mask below a slot).
-/

namespace NatCol

/-- Number of set bits in `x` (population count), via the classic SWAR bit-twiddling
algorithm: counts bits within each pair, then folds the partial sums up through 4-bit
and 8-bit groups, and finally sums the four byte counts with one multiply — all in a
fixed handful of shifts/masks rather than a 32-iteration loop. -/
def popCount (x : UInt32) : Nat :=
  let x : UInt32 := x - ((x >>> 1) &&& (0x55555555 : UInt32))
  let x : UInt32 := (x &&& (0x33333333 : UInt32)) + ((x >>> 2) &&& (0x33333333 : UInt32))
  let x : UInt32 := (x + (x >>> 4)) &&& (0x0F0F0F0F : UInt32)
  ((x * (0x01010101 : UInt32)) >>> 24).toNat

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

end NatCol
