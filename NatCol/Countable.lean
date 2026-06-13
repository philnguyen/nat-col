/-!
# `Countable`: invertible encodings into `Nat`

A `Countable α` packages an injection `toNat : α → Nat` together with its partial inverse
`ofNat? : Nat → Option α`, related by the single law `ofNat? n = some a ↔ toNat a = n`. That one
equivalence yields the round trip (`ofNat?_toNat`), decode faithfulness (`toNat_ofNat?`) and
injectivity (`toNat_inj`) — everything `IndexedSet`/`IndexedMap` need to key a `NatSet`/`NatMap`
by the encoding with zero per-element storage: keys live only as trie positions and are decoded
on the way out.

All instances below are *order-preserving* (`toNat` is monotone), so the ordered queries of the
indexed collections (`min?`/`max?`/`succ?`/`split`/`range`…) mean the natural order of the key
type. An instance is free to break this — the indexed collections' ordered theorems are stated
in encoding order — but it then answers those queries in its own encoding order.
-/

namespace NatCol
----------------------------------------------------------------------------------------------------
-- Implementation
----------------------------------------------------------------------------------------------------

/-- An invertible encoding of `α` into `Nat`: an injection `toNat` with its partial inverse
`ofNat?`. The single law `ofNat?_eq_some_iff` pins `ofNat?` as *exactly* the partial inverse —
it succeeds precisely on the image of `toNat` — and already implies injectivity (`toNat_inj`). -/
class Countable (α : Type u) where
  /-- The encoding: an injection into `Nat` (injectivity follows from the law). -/
  toNat : α → Nat
  /-- The decoding: succeeds exactly on the image of `toNat`. -/
  ofNat? : Nat → Option α
  /-- `ofNat?` is exactly the partial inverse of `toNat`. -/
  ofNat?_eq_some_iff : ∀ {n : Nat} {a : α}, ofNat? n = some a ↔ toNat a = n

namespace Countable

/-- Build a `Countable` from an encoding bounded by `size` with a total decode below the bound —
the shape of every fixed-width scalar (`UInt8`…`USize`, `Fin n`, `Bool`). Callers supply the
bound, the section (`toNat_ofNatLT`) and injectivity; the dite decode and its law come for
free. -/
@[reducible] def ofBounded {α : Type u} (size : Nat) (toNat : α → Nat)
    (ofNatLT : (n : Nat) → n < size → α)
    (toNat_lt : ∀ a, toNat a < size)
    (toNat_ofNatLT : ∀ n h, toNat (ofNatLT n h) = n)
    (inj : ∀ {a b}, toNat a = toNat b → a = b) : Countable α where
  toNat := toNat
  ofNat? n := if h : n < size then some (ofNatLT n h) else none
  ofNat?_eq_some_iff := by
    intro n a
    constructor
    · intro h
      by_cases hlt : n < size
      · rw [dif_pos hlt] at h
        injection h with h
        rw [← h, toNat_ofNatLT]
      · rw [dif_neg hlt] at h
        exact absurd h (by simp)
    · intro h
      subst h
      rw [dif_pos (toNat_lt a)]
      exact congrArg some (inj (toNat_ofNatLT (toNat a) (toNat_lt a)))

end Countable

/-- `Nat` encodes as itself. -/
instance : Countable Nat where
  toNat := id
  ofNat? := some
  ofNat?_eq_some_iff := ⟨fun h => (Option.some.inj h).symm, fun h => by subst h; rfl⟩

/-- `Bool` encodes as `{0, 1}`. -/
instance : Countable Bool :=
  .ofBounded 2 Bool.toNat (fun n _ => n == 1)
    (fun a => by cases a <;> decide)
    (fun n h => by
      match n, h with
      | 0, _ => rfl
      | 1, _ => rfl)
    (fun {a b} h => by cases a <;> cases b <;> first | rfl | exact absurd h (by decide))

/-- `Fin n` encodes as its value. -/
instance {n : Nat} : Countable (Fin n) :=
  .ofBounded n Fin.val Fin.mk (fun a => a.isLt) (fun _ _ => rfl)
    (fun h => Fin.eq_of_val_eq h)

/-- `UInt8` encodes as its value. -/
instance : Countable UInt8 :=
  .ofBounded UInt8.size UInt8.toNat UInt8.ofNatLT (fun a => a.toNat_lt_size)
    (fun _ _ => UInt8.toNat_ofNatLT) (fun h => UInt8.toNat_inj.mp h)

/-- `UInt16` encodes as its value. -/
instance : Countable UInt16 :=
  .ofBounded UInt16.size UInt16.toNat UInt16.ofNatLT (fun a => a.toNat_lt_size)
    (fun _ _ => UInt16.toNat_ofNatLT) (fun h => UInt16.toNat_inj.mp h)

/-- `UInt32` encodes as its value. -/
instance : Countable UInt32 :=
  .ofBounded UInt32.size UInt32.toNat UInt32.ofNatLT (fun a => a.toNat_lt_size)
    (fun _ _ => UInt32.toNat_ofNatLT) (fun h => UInt32.toNat_inj.mp h)

/-- `UInt64` encodes as its value. -/
instance : Countable UInt64 :=
  .ofBounded UInt64.size UInt64.toNat UInt64.ofNatLT (fun a => a.toNat_lt_size)
    (fun _ _ => UInt64.toNat_ofNatLT) (fun h => UInt64.toNat_inj.mp h)

/-- `USize` encodes as its value. -/
instance : Countable USize :=
  .ofBounded USize.size USize.toNat USize.ofNatLT (fun a => a.toNat_lt_size)
    (fun _ _ => USize.toNat_ofNatLT) (fun h => USize.toNat_inj.mp h)

/-- `Char` encodes as its code point. The decode guards on Unicode validity, so the surrogate
gap `[0xD800, 0xDFFF]` and everything past `0x10FFFF` read back `none`. -/
instance : Countable Char where
  toNat c := c.toNat
  ofNat? n := if h : n.isValidChar then some (Char.ofNatAux n h) else none
  ofNat?_eq_some_iff := by
    intro n a
    constructor
    · intro h
      by_cases hv : n.isValidChar
      · rw [dif_pos hv] at h
        injection h with h
        rw [← h]
        rfl
      · rw [dif_neg hv] at h
        exact absurd h (by simp)
    · intro h
      subst h
      have hv : (Char.toNat a).isValidChar := a.valid
      rw [dif_pos hv]
      exact congrArg some (Char.ext rfl)

/-! ## Tests -/

section Tests

-- Nat: the identity encoding
#guard Countable.toNat (42 : Nat) = 42
#guard (Countable.ofNat? 42 : Option Nat) = some 42

-- Bool: {0, 1}, everything else decodes to none
#guard Countable.toNat false = 0
#guard Countable.toNat true = 1
#guard (Countable.ofNat? 0 : Option Bool) = some false
#guard (Countable.ofNat? 1 : Option Bool) = some true
#guard (Countable.ofNat? 2 : Option Bool) = none

-- Fin: values below the bound round-trip, the bound itself does not decode
#guard Countable.toNat (3 : Fin 5) = 3
#guard (Countable.ofNat? 4 : Option (Fin 5)) = some 4
#guard (Countable.ofNat? 5 : Option (Fin 5)) = none

-- UInt8/UInt64: full range round-trips, one past the top decodes to none
#guard Countable.toNat (255 : UInt8) = 255
#guard (Countable.ofNat? 255 : Option UInt8) = some 255
#guard (Countable.ofNat? 256 : Option UInt8) = none
#guard Countable.toNat (18446744073709551615 : UInt64) = 18446744073709551615
#guard (Countable.ofNat? 18446744073709551615 : Option UInt64) = some 18446744073709551615
#guard (Countable.ofNat? 18446744073709551616 : Option UInt64) = none

-- Char: code points round-trip; the surrogate gap and beyond-Unicode decode to none
#guard Countable.toNat 'A' = 65
#guard (Countable.ofNat? 65 : Option Char) = some 'A'
#guard ((Countable.ofNat? 0xD7FF : Option Char).map Countable.toNat) = some 0xD7FF
#guard (Countable.ofNat? 0xD800 : Option Char) = none
#guard (Countable.ofNat? 0xDFFF : Option Char) = none
#guard ((Countable.ofNat? 0xE000 : Option Char).map Countable.toNat) = some 0xE000
#guard ((Countable.ofNat? 0x10FFFF : Option Char).map Countable.toNat) = some 0x10FFFF
#guard (Countable.ofNat? 0x110000 : Option Char) = none

end Tests

----------------------------------------------------------------------------------------------------
-- Theorems
----------------------------------------------------------------------------------------------------

namespace Countable

variable {α : Type u} [Countable α]

/-- The round trip: decoding an encoding recovers the value. -/
@[simp] theorem ofNat?_toNat (a : α) : ofNat? (toNat a) = some a :=
  ofNat?_eq_some_iff.mpr rfl

/-- Decode faithfulness: a successful decode names the encoding it came from. -/
theorem toNat_ofNat? {n : Nat} {a : α} (h : ofNat? n = some a) : toNat a = n :=
  ofNat?_eq_some_iff.mp h

/-- The encoding is injective. -/
theorem toNat_inj {a b : α} (h : toNat a = toNat b) : a = b := by
  have ha : ofNat? (toNat b) = some a := by rw [← h]; exact ofNat?_toNat a
  rw [ofNat?_toNat b] at ha
  exact (Option.some.inj ha).symm

/-- Decoding seam: a decoded `some` answer pins the raw key to `toNat` of the result. This is
the workhorse behind every `IndexedSet`/`IndexedMap` ordered-query theorem whose hypothesis is
a decoded raw answer. -/
theorem bind_ofNat?_eq_some {o : Option Nat} {a : α} (h : o.bind (ofNat? (α := α)) = some a) :
    o = some (toNat a) := by
  cases o with
  | none => exact absurd h (by simp)
  | some n =>
    replace h : ofNat? n = some a := h
    rw [toNat_ofNat? h]

/-- Decoding seam: when every raw key the answer could carry is in `toNat`'s image (the
well-formedness invariant of `IndexedSet`/`IndexedMap`), a decoded `none` answer means the raw
answer was already `none`. -/
theorem bind_ofNat?_eq_none {o : Option Nat} (h : o.bind (ofNat? (α := α)) = none)
    (hwf : ∀ n, o = some n → ∃ a : α, toNat a = n) : o = none := by
  cases o with
  | none => rfl
  | some n =>
    obtain ⟨a, ha⟩ := hwf n rfl
    replace h : ofNat? n = none := h
    rw [ofNat?_eq_some_iff.mpr ha] at h
    exact absurd h (by simp)

end Countable

end NatCol
