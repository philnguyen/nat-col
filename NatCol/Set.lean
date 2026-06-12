import NatCol.Collection

/-!
# `NatSet`: a set of `Nat`

`NatSet` instantiates the generic trie with `UInt32` leaves: a leaf is itself a 32-element
bitset of the low 5 bits, so leaves carry no boxed payload (the value type is `Unit`).
Lattice operations bottom out in plain bitwise `|||` / `&&&` at the leaf.

`NatSet` is a `def` (not an `abbrev`) so that dot-notation resolves to these wrappers
(e.g. single-argument `s.insert 42`) rather than to the underlying `NatCollection`.
-/

namespace NatCol
----------------------------------------------------------------------------------------------------
-- Implementation
----------------------------------------------------------------------------------------------------

/-- A set of natural numbers. -/
def NatSet : Type := NatCollection UInt32

namespace NatSet

instance : BEq NatSet := inferInstanceAs (BEq (NatCollection UInt32))
instance : LawfulBEq NatSet := inferInstanceAs (LawfulBEq (NatCollection UInt32))
instance : DecidableEq NatSet := inferInstanceAs (DecidableEq (NatCollection UInt32))
instance : Hashable NatSet := inferInstanceAs (Hashable (NatCollection UInt32))
instance : LawfulHashable NatSet where
  hash_eq _ _ h := by rw [eq_of_beq h]
instance : EmptyCollection NatSet := ⟨NatCollection.empty⟩

/-- The empty set. -/
def empty : NatSet := ∅
def isEmpty : NatSet → Bool := NatCollection.isEmpty
def size : NatSet → Nat := NatCollection.size
def contains : NatSet → Nat → Bool := NatCollection.contains
def insert (s : NatSet) (k : Nat) : NatSet := NatCollection.insert s k ()
def erase : NatSet → Nat → NatSet := NatCollection.erase

/-- The least element, `none` on the empty set. O(depth) — an ordered query a hash set answers
only by scanning all n elements. -/
def min? : NatSet → Option Nat := NatCollection.minKey?
/-- The greatest element, `none` on the empty set. O(depth). -/
def max? : NatSet → Option Nat := NatCollection.maxKey?
/-- The least element strictly greater than `k` (successor), `none` if there is none. O(depth). -/
def succ? (s : NatSet) (k : Nat) : Option Nat := (NatCollection.entryGT? s k).map Prod.fst
/-- The greatest element strictly less than `k` (predecessor), `none` if there is none.
O(depth). -/
def pred? (s : NatSet) (k : Nat) : Option Nat := (NatCollection.entryLT? s k).map Prod.fst
/-- The least element `≥ k`: `k` itself when present, else the successor. -/
def succEq? (s : NatSet) (k : Nat) : Option Nat := (NatCollection.entryGE? s k).map Prod.fst
/-- The greatest element `≤ k`: `k` itself when present, else the predecessor. -/
def predEq? (s : NatSet) (k : Nat) : Option Nat := (NatCollection.entryLE? s k).map Prod.fst
/-- The least element together with the set without it, `none` on the empty set (the
priority-queue step). -/
def popMin? (s : NatSet) : Option (Nat × NatSet) :=
  (NatCollection.popMinEntry? s).map (fun e => (e.1.1, e.2))
/-- The greatest element together with the set without it, `none` on the empty set. -/
def popMax? (s : NatSet) : Option (Nat × NatSet) :=
  (NatCollection.popMaxEntry? s).map (fun e => (e.1.1, e.2))

/-- Union. -/
def union (s t : NatSet) : NatSet := NatCollection.join (fun _ _ => ()) s t
/-- Intersection. -/
def inter (s t : NatSet) : NatSet := NatCollection.meet (fun _ _ => ()) s t
/-- Difference: the elements of `s` not in `t` — a structural merge walk, not a per-element
probe: subtrees of `s` that cannot meet `t` are kept whole (and shared) in O(1), aligned leaves
subtract with one `AND NOT`, and the result is canonical (the height shrinks when the deep keys
are removed). -/
def diff (s t : NatSet) : NatSet := NatCollection.diff s t
/-- Symmetric difference: the elements in exactly one of `s`, `t` — a structural merge where
shared leaves cancel with one `XOR` and equal subtrees cancel entirely; one-sided subtrees are
carried over whole (shared). Equals `(s \ t) ∪ (t \ s)` in one pass. -/
def symmDiff (s t : NatSet) : NatSet := NatCollection.symmDiff s t
/-- Split at `k`: `(elements < k, elements ≥ k)` — two structural prunes along `k`'s routed
path; both parts are canonical and share every off-path subtree with `s`. An ordered operation a
hash set can only do by scanning all n elements. -/
def split (s : NatSet) (k : Nat) : NatSet × NatSet := NatCollection.split s k
/-- The elements in the inclusive range `[lo, hi]` — a double structural prune along the two
bounds' paths; everything strictly inside the window is shared, not copied. -/
def range (s : NatSet) (lo hi : Nat) : NatSet := NatCollection.range s lo hi
/-- Subset test. -/
def subset (s t : NatSet) : Bool := NatCollection.restricts (fun _ _ => true) s t
/-- Whether `s` and `t` share no element — the intersection's structural walk without building
the intersection: prefix-disjoint subtrees answer in O(1), aligned leaves compare with one `AND`,
and the first shared element short-circuits the rest. -/
def isDisjoint (s t : NatSet) : Bool := NatCollection.isDisjoint s t

instance : Union NatSet := ⟨union⟩
instance : Inter NatSet := ⟨inter⟩
instance : SDiff NatSet := ⟨diff⟩

-- `subset` is `Bool`-valued, so phrase `s ⊆ t` as `subset … = true` and make it
-- decidable, keeping it usable in `#guard` / `decide`.
instance : HasSubset NatSet := ⟨fun s t => s.subset t = true⟩
instance (s t : NatSet) : Decidable (s ⊆ t) := inferInstanceAs (Decidable (s.subset t = true))

-- `k ∈ s` reduces to the `Bool` `contains`, so it stays decidable (usable in `#guard` / `decide`);
-- `k ∉ s` is `¬ k ∈ s`, available automatically.
instance : Membership Nat NatSet := ⟨fun s k => s.contains k = true⟩
instance (k : Nat) (s : NatSet) : Decidable (k ∈ s) :=
  inferInstanceAs (Decidable (s.contains k = true))

/-- Elements in ascending order. -/
def toList (s : NatSet) : List Nat := (NatCollection.toList s).map Prod.fst
/-- Build a set from a list of elements. -/
def ofList (l : List Nat) : NatSet := l.foldl (fun s k => s.insert k) empty

/-- `repr` renders the `ofList` of the ascending element list — valid Lean that rebuilds the
set. -/
instance : Repr NatSet where
  reprPrec s prec := Repr.addAppParen ("NatSet.ofList " ++ repr s.toList) prec

/-- `toString` displays the elements in ascending order as `{e₁, e₂, …}`. -/
instance : ToString NatSet where
  toString s := "{" ++ String.intercalate ", " (s.toList.map toString) ++ "}"

/-- Fold `f` over elements in ascending order, starting from `init`. -/
def fold {β : Type w} (f : β → Nat → β) (init : β) (s : NatSet) : β :=
  NatCollection.fold (fun acc k _ => f acc k) init s

/-- Monadic fold over elements in ascending order, threading the accumulator through `m`. The
monadic companion of `fold` (recovered by instantiating `m := Id`). -/
def foldM {β : Type w} {m : Type w → Type w'} [Monad m] (f : β → Nat → m β) (init : β) (s : NatSet) :
    m β :=
  NatCollection.foldM (fun acc k _ => f acc k) init s

/-- Whether every element satisfies `p`, short-circuiting at the first that fails (vacuously true on
the empty set). Same value as `s.fold (fun acc k => acc && p k) true`, but stops at the first
failing element. -/
def all (p : Nat → Bool) (s : NatSet) : Bool := NatCollection.all (fun k _ => p k) s

/-- Whether some element satisfies `p`, short-circuiting at the first that holds (vacuously false on
the empty set). Same value as `s.fold (fun acc k => acc || p k) false`. -/
def any (p : Nat → Bool) (s : NatSet) : Bool := NatCollection.any (fun k _ => p k) s

/-- Keep only the elements satisfying `p`. The result is canonical, so it equals the set built
directly from the surviving elements (and its height shrinks when the deep keys are removed). -/
def filter (p : Nat → Bool) (s : NatSet) : NatSet := NatCollection.filter (fun k _ => p k) s

/-- Split `s` by `p`: the first component keeps the elements satisfying `p`, the second the rest.
Two structural `filter` passes, so both parts are canonical. -/
def partition (p : Nat → Bool) (s : NatSet) : NatSet × NatSet :=
  NatCollection.partition (fun k _ => p k) s

/-- Monadic `all`: whether every element satisfies the monadic predicate `p`, threading effects in
ascending order and short-circuiting at the first failure. The monadic companion of `all`. -/
def allM {m : Type → Type w} [Monad m] (p : Nat → m Bool) (s : NatSet) : m Bool :=
  NatCollection.allM (fun k _ => p k) s

/-- Monadic `any`: whether some element satisfies `p`, short-circuiting at the first success. -/
def anyM {m : Type → Type w} [Monad m] (p : Nat → m Bool) (s : NatSet) : m Bool :=
  NatCollection.anyM (fun k _ => p k) s

/-- Monadic `filter`: keep the elements for which `p` returns `true`, running `p` on every element
in ascending order and threading its effects through `m`. The result is canonical — rebuilt from
the survivors (see `NatCollection.filterM`) — so it equals the pure `filter` when `p` is
effect-free. -/
def filterM {m : Type → Type w} [Monad m] (p : Nat → m Bool) (s : NatSet) : m NatSet :=
  NatCollection.filterM (fun k _ => p k) s

end NatSet

/-! ## Tests -/

section Tests

-- membership / size on a few common and edge keys (0, within a leaf, across leaves)
#guard NatSet.empty.isEmpty
#guard (∅ : NatSet).size = 0
#guard 42 ∉ (∅ : NatSet)
#guard (NatSet.empty.insert 42).size = 1
#guard 42 ∈ (NatSet.empty.insert 42)
#guard 43 ∉ (NatSet.empty.insert 42)
#guard 0 ∈ (NatSet.empty.insert 0)
#guard 32 ∉ (NatSet.empty.insert 0)              -- 0 and 32 differ only above the first chunk

-- idempotent insert, coherent size and equality
#guard (NatSet.empty.insert 42 |>.insert 42) = NatSet.empty.insert 42
#guard (NatSet.empty.insert 42 |>.insert 42).size = 1
#guard (NatSet.empty.insert 1 |>.insert 2 |>.insert 3).size = 3

-- ordering of toList is ascending regardless of insertion order
#guard (NatSet.empty.insert 42 |>.insert 34 |>.toList) = [34, 42]
#guard (NatSet.empty.insert 5 |>.insert 1000 |>.insert 0 |>.toList) = [0, 5, 1000]

-- erase undoes insert; erasing an absent key is a no-op; erase back to empty is canonical
#guard (NatSet.empty.insert 42 |>.erase 42) = (∅ : NatSet)
#guard (NatSet.empty.insert 42 |>.erase 42).isEmpty
#guard (NatSet.empty.insert 42 |>.erase 99) = NatSet.empty.insert 42
#guard (NatSet.empty.insert 5 |>.insert 1000 |>.erase 1000) = NatSet.empty.insert 5

-- isDisjoint: no shared element; agrees with the (allocating) `∩`-then-isEmpty route
#guard (NatSet.ofList [1, 2]).isDisjoint (NatSet.ofList [3, 4])
#guard (NatSet.ofList [1, 3, 5]).isDisjoint (NatSet.ofList [2, 4, 6])    -- interleaved, shared leaf
#guard !((NatSet.ofList [1, 5000]).isDisjoint (NatSet.ofList [5000]))    -- deep shared element
#guard (∅ : NatSet).isDisjoint (∅ : NatSet)
#guard (∅ : NatSet).isDisjoint (NatSet.ofList [1])
#guard
  let a := NatSet.ofList [1, 32, 1000, 5000]
  let b := NatSet.ofList [2, 33, 1001]
  a.isDisjoint b == (a ∩ b).isEmpty

-- diff (structural merge): list oracle, deep keys kept whole, right operand untouched
#guard ((NatSet.ofList [1, 2, 3, 5000]) \ (NatSet.ofList [2, 5000])).toList = [1, 3]
#guard
  let a := NatSet.ofList [0, 31, 32, 1000, 1000000]
  let b := NatSet.ofList [31, 1000000, 7]
  (a \ b).toList = a.toList.filter (fun k => !(b.contains k))

-- symmDiff: elements in exactly one operand; cancellation, identities, involution, oracle
#guard (NatSet.ofList [1, 2, 3]).symmDiff (NatSet.ofList [2, 3, 4]) = NatSet.ofList [1, 4]
#guard
  let a := NatSet.ofList [1, 2, 3]
  a.symmDiff a = (∅ : NatSet)                                       -- total cancellation → nil
#guard
  let a := NatSet.ofList [5, 1000, 32]
  a.symmDiff ∅ = a && (∅ : NatSet).symmDiff a = a                   -- identities
#guard
  let a := NatSet.ofList [1, 32, 5000]
  let b := NatSet.ofList [2, 32, 999999]
  a.symmDiff b = b.symmDiff a                                       -- commutative
    && a.symmDiff b = (a \ b) ∪ (b \ a)                             -- decomposition oracle
    && (a.symmDiff b).symmDiff b = a                                -- involution
#guard (NatSet.ofList [1, 5000]).symmDiff (NatSet.ofList [5000]) = NatSet.ofList [1]
  -- deep cancel: the height collapses canonically

-- split/range: structural prunes at key bounds
#guard (NatSet.ofList [1, 5, 9, 5000]).split 6 = (NatSet.ofList [1, 5], NatSet.ofList [9, 5000])
#guard (NatSet.ofList [1, 5, 9]).split 5 = (NatSet.ofList [1], NatSet.ofList [5, 9])
  -- the pivot lands in the ≥ part
#guard (∅ : NatSet).split 5 = (∅, ∅)
#guard
  let s := NatSet.ofList [3, 31, 32, 1000, 1000000]
  let parts := s.split 32
  parts.1 ∪ parts.2 = s && parts.1.isDisjoint parts.2              -- split is a partition
#guard (NatSet.ofList [1, 5, 9, 31, 32, 5000]).range 5 32 = NatSet.ofList [5, 9, 31, 32]
#guard (NatSet.ofList [1, 5, 9]).range 9 9 = NatSet.ofList [9]     -- degenerate window
#guard (NatSet.ofList [1, 5, 9]).range 6 8 = (∅ : NatSet)          -- empty window
#guard (NatSet.ofList [1, 5, 9]).range 0 100 = NatSet.ofList [1, 5, 9]

-- ordered queries: min/max, successor/predecessor (strict and inclusive), pop
#guard (∅ : NatSet).min? = none
#guard (∅ : NatSet).max? = none
#guard (NatSet.ofList [5, 1, 9]).min? = some 1
#guard (NatSet.ofList [5, 1, 9]).max? = some 9
#guard (NatSet.ofList [1, 9223372036854775807]).min? = some 1                  -- deep sparse keys
#guard (NatSet.ofList [1, 9223372036854775807]).max? = some 9223372036854775807
#guard (NatSet.ofList [10, 20, 30]).succ? 10 = some 20
#guard (NatSet.ofList [10, 20, 30]).succ? 0 = some 10
#guard (NatSet.ofList [10, 20, 30]).succ? 30 = none
#guard (NatSet.ofList [10, 20, 30]).pred? 30 = some 20
#guard (NatSet.ofList [10, 20, 30]).pred? 10 = none
#guard (NatSet.ofList [10, 20, 30]).succEq? 20 = some 20
#guard (NatSet.ofList [10, 20, 30]).succEq? 21 = some 30
#guard (NatSet.ofList [10, 20, 30]).predEq? 20 = some 20
#guard (NatSet.ofList [10, 20, 30]).predEq? 19 = some 10
#guard (NatSet.ofList [31, 32]).succ? 31 = some 32          -- across the leaf seam (slot 31 → 0)
#guard (NatSet.ofList [5, 1000000]).succ? 5 = some 1000000  -- across a compressed path
#guard (NatSet.ofList [3, 1, 2]).popMin? = some (1, NatSet.ofList [2, 3])
#guard (NatSet.ofList [7, 5000]).popMax? = some (5000, NatSet.ofList [7])      -- collapses canonically
#guard (∅ : NatSet).popMin? = none

-- popMin? drains in ascending order: collecting the popped elements recovers `toList`
private def drainMin : Nat → NatSet → List Nat
  | 0, _ => []
  | fuel + 1, s =>
    match s.popMin? with
    | none => []
    | some (k, rest) => k :: drainMin fuel rest
#guard drainMin 10 (NatSet.ofList [5, 1, 1000, 32]) = [1, 5, 32, 1000]
#guard drainMin 10 (NatSet.ofList [5, 1, 1000, 32]) = (NatSet.ofList [5, 1, 1000, 32]).toList

-- ofList / toList round trip (deduplicated, sorted)
#guard (NatSet.ofList [3, 1, 2, 1, 3]).toList = [1, 2, 3]
#guard (NatSet.ofList [100, 2000, 30000]).size = 3

-- fold visits elements in ascending order, regardless of insertion order or height
#guard (NatSet.ofList [3, 1, 2]).fold (fun acc k => acc + k) 0 = 6
#guard (NatSet.ofList [3, 1, 2]).fold (fun acc k => acc ++ [k]) [] = [1, 2, 3]
#guard (∅ : NatSet).fold (fun acc k => acc + k) 0 = 0
#guard (NatSet.ofList [1, 1000, 5]).fold (fun acc k => acc ++ [k]) [] = [1, 5, 1000]  -- mixed heights

-- foldM in `Id` reproduces `fold`; in a real monad it threads effects — `Except` short-circuits at
-- the first element ≥ 100, and `StateM` records the ascending visit order (here across heights).
#guard Id.run ((NatSet.ofList [3, 1, 2]).foldM (fun acc k => pure (acc + k)) 0) = 6
#guard (match ((NatSet.ofList [1, 200, 5, 300]).foldM
          (fun acc k => if k ≥ 100 then throw k else pure (acc + k)) 0 : Except Nat Nat) with
        | .error e => e | .ok _ => 0) = 200        -- stops at the first element ≥ 100
#guard ((NatSet.ofList [1, 5, 1000]).foldM (m := StateM (List Nat))
          (fun (_ : Unit) k => modify (· ++ [k])) () |>.run []).2 = [1, 5, 1000]

-- all / any over elements, short-circuiting. The result is independent of where the scan stops, so
-- it must agree with the naive `fold`-based `&&` / `||` (which always visits every element).
#guard (NatSet.ofList [2, 4, 6]).all (fun k => k % 2 == 0)
#guard !(NatSet.ofList [2, 4, 5, 6]).all (fun k => k % 2 == 0)        -- 5 fails mid-scan
#guard (NatSet.ofList [1, 3, 4, 5]).any (fun k => k % 2 == 0)         -- 4 holds mid-scan
#guard !(NatSet.ofList [1, 3, 5]).any (fun k => k % 2 == 0)
#guard (∅ : NatSet).all (fun _ => false)                             -- vacuously true
#guard !(∅ : NatSet).any (fun _ => true)                             -- vacuously false
#guard (NatSet.ofList [2, 4, 5000]).all (fun k => k % 2 == 0)         -- mixed heights, all even
#guard (NatSet.ofList [1, 3, 5000]).any (fun k => k % 2 == 0)         -- mixed heights, 5000 even
-- headline: short-circuit `all`/`any` agree in value with the naive `fold` computations
#guard (NatSet.ofList [2, 4, 5, 6]).all (fun k => k % 2 == 0)
        = (NatSet.ofList [2, 4, 5, 6]).fold (fun acc k => acc && (k % 2 == 0)) true
#guard (NatSet.ofList [1, 3, 4, 5]).any (fun k => k % 2 == 0)
        = (NatSet.ofList [1, 3, 4, 5]).fold (fun acc k => acc || (k % 2 == 0)) false
#guard (NatSet.ofList [2, 4, 5000]).all (fun k => k % 2 == 0)
        = (NatSet.ofList [2, 4, 5000]).fold (fun acc k => acc && (k % 2 == 0)) true
#guard (∅ : NatSet).any (fun k => k % 2 == 0)
        = (∅ : NatSet).fold (fun acc k => acc || (k % 2 == 0)) false

-- filter keeps exactly the elements satisfying the predicate. The result is canonical, so it is
-- *equal* (not merely same-elements) to the set built directly from the survivors.
#guard (NatSet.ofList [1, 2, 3, 4, 5, 6]).filter (fun k => k % 2 == 0) = NatSet.ofList [2, 4, 6]
#guard ((NatSet.ofList [1, 2, 3, 4, 5, 6]).filter (fun k => k % 2 == 0)).toList = [2, 4, 6]
#guard (NatSet.ofList [1, 2, 3]).filter (fun _ => true) = NatSet.ofList [1, 2, 3]   -- keep all
#guard (NatSet.ofList [1, 2, 3]).filter (fun _ => false) = (∅ : NatSet)             -- drop all
#guard (∅ : NatSet).filter (fun _ => true) = (∅ : NatSet)                           -- empty
-- filtering away the deep keys shrinks the height back to canonical (mixed-height input)
#guard (NatSet.ofList [1, 2, 5000]).filter (fun k => k ≤ 99) = NatSet.ofList [1, 2]
#guard hash ((NatSet.ofList [1, 2, 5000]).filter (fun k => k ≤ 99)) = hash (NatSet.ofList [1, 2])
-- filter agrees with `List.filter` through `toList` (order preserved, mixed heights)
#guard ((NatSet.ofList [1, 40, 99, 5000]).filter (fun k => k % 2 == 1)).toList
        = ((NatSet.ofList [1, 40, 99, 5000]).toList.filter (fun k => k % 2 == 1))

-- monadic allM / anyM / filterM: in `Id` they reproduce the pure ops; in a real monad they thread
-- effects in ascending order. `StateM` records the visit order, which also exposes short-circuiting.
#guard Id.run ((NatSet.ofList [2, 4, 6]).allM (fun k => pure (k % 2 == 0)))
#guard !Id.run ((NatSet.ofList [2, 5, 6]).anyM (fun k => pure (k > 100)))
#guard Id.run ((NatSet.ofList [1, 2, 3]).filterM (fun k => pure (k % 2 == 1))) = NatSet.ofList [1, 3]
-- allM stops at the first failure (5 is odd), so 6 is never visited (the StateM log ends at 5)
#guard Id.run (((NatSet.ofList [2, 4, 5, 6]).allM (m := StateM (List Nat))
          (fun k => do modify (· ++ [k]); pure (k % 2 == 0))).run []) = (false, [2, 4, 5])
-- anyM stops at the first success (4 is even), so 5 and 6 are never visited
#guard Id.run (((NatSet.ofList [1, 3, 4, 5, 6]).anyM (m := StateM (List Nat))
          (fun k => do modify (· ++ [k]); pure (k % 2 == 0))).run []) = (true, [1, 3, 4])
-- allM / anyM agree in value with the pure all / any
#guard Id.run ((NatSet.ofList [2, 4, 5, 6]).allM (fun k => pure (k % 2 == 0)))
        = (NatSet.ofList [2, 4, 5, 6]).all (fun k => k % 2 == 0)
#guard Id.run ((NatSet.ofList [1, 3, 4, 5]).anyM (fun k => pure (k % 2 == 0)))
        = (NatSet.ofList [1, 3, 4, 5]).any (fun k => k % 2 == 0)
-- filterM in `Id` agrees with the pure filter; it visits every element in ascending order; and in
-- `Except` a throwing predicate short-circuits at the first offending element (300 is never seen).
#guard Id.run ((NatSet.ofList [1, 2, 3, 4, 5, 6]).filterM (fun k => pure (k % 2 == 0)))
        = (NatSet.ofList [1, 2, 3, 4, 5, 6]).filter (fun k => k % 2 == 0)
#guard (((NatSet.ofList [1, 5, 1000]).filterM (m := StateM (List Nat))
          (fun k => do modify (· ++ [k]); pure true)).run []).2 = [1, 5, 1000]
#guard (match ((NatSet.ofList [1, 200, 5, 300]).filterM
          (fun k => if k ≥ 100 then throw k else pure (k % 2 == 0)) : Except Nat NatSet) with
        | .error e => e | .ok _ => 0) = 200

-- union (via the `∪` notation)
#guard ((NatSet.ofList [1, 2]) ∪ (NatSet.ofList [2, 3])).toList = [1, 2, 3]
#guard (NatSet.ofList [1, 2]) ∪ ∅ = NatSet.ofList [1, 2]               -- right identity
#guard (∅ : NatSet) ∪ (NatSet.ofList [1, 2]) = NatSet.ofList [1, 2]    -- left identity
#guard (NatSet.ofList [1, 2]) ∪ (NatSet.ofList [1, 2]) = NatSet.ofList [1, 2]  -- idempotent
#guard ((NatSet.ofList [1, 1000]) ∪ (NatSet.ofList [2, 5])).toList = [1, 2, 5, 1000]  -- mixed heights

-- intersection (via the `∩` notation)
#guard ((NatSet.ofList [1, 2, 3]) ∩ (NatSet.ofList [2, 3, 4])).toList = [2, 3]
#guard (NatSet.ofList [1, 2]) ∩ ∅ = (∅ : NatSet)                       -- right annihilator
#guard (∅ : NatSet) ∩ (NatSet.ofList [1, 2]) = (∅ : NatSet)            -- left annihilator
#guard (NatSet.ofList [1, 2]) ∩ (NatSet.ofList [1, 2]) = NatSet.ofList [1, 2]  -- idempotent
#guard (NatSet.ofList [1, 2]) ∩ (NatSet.ofList [3, 4]) = (∅ : NatSet)  -- disjoint -> empty
#guard ((NatSet.ofList [1, 1000]) ∩ (NatSet.ofList [1000, 2])).toList = [1000]  -- mixed heights, shrinks

-- subset (via the `⊆` notation)
#guard (∅ : NatSet) ⊆ (NatSet.ofList [1, 2])                               -- empty restricts all
#guard (NatSet.ofList [1, 2]) ⊆ (NatSet.ofList [1, 2, 3])
#guard (NatSet.ofList [1, 2]) ⊆ (NatSet.ofList [1, 2])                      -- reflexive
#guard ¬ ((NatSet.ofList [1, 2, 3]) ⊆ (NatSet.ofList [1, 2]))
#guard ¬ ((NatSet.ofList [1, 1000]) ⊆ (NatSet.ofList [1, 2]))               -- taller -> not subset

-- difference (via the `\` notation) keeps the left side's elements absent from the right. The
-- result is canonical, so it is *equal* to the set built directly from the survivors.
#guard ((NatSet.ofList [1, 2, 3]) \ (NatSet.ofList [2, 4])).toList = [1, 3]
#guard (NatSet.ofList [1, 2]) \ ∅ = NatSet.ofList [1, 2]                     -- right identity
#guard (∅ : NatSet) \ (NatSet.ofList [1, 2]) = (∅ : NatSet)                  -- empty minus anything
#guard (NatSet.ofList [1, 2]) \ (NatSet.ofList [1, 2]) = (∅ : NatSet)        -- self-difference
#guard (NatSet.ofList [1, 2]) \ (NatSet.ofList [3, 4]) = NatSet.ofList [1, 2]  -- disjoint: unchanged
-- removing the deep key shrinks the height back to canonical (mixed-height operands)
#guard (NatSet.ofList [1, 5000]) \ (NatSet.ofList [5000, 7000]) = NatSet.ofList [1]
#guard hash ((NatSet.ofList [1, 5000]) \ (NatSet.ofList [5000])) = hash (NatSet.ofList [1])

-- partition: `.1` keeps the elements satisfying `p`, `.2` the rest; both parts canonical
#guard (NatSet.ofList [1, 2, 3, 4]).partition (fun k => k % 2 == 0)
        = (NatSet.ofList [2, 4], NatSet.ofList [1, 3])
#guard (NatSet.ofList [1, 2, 5000]).partition (fun k => k ≤ 99)
        = (NatSet.ofList [1, 2], NatSet.ofList [5000])                       -- mixed heights split
#guard (∅ : NatSet).partition (fun _ => true) = (∅, ∅)

/-! ### Cross-height operands: descend the taller tree's spine, both directions

`1,2,3` need height 0 (`< 32`), `40,50` height 1 (`< 1024`), `5000` height 2 (`< 32768`), so these
exercise `join`/`meet`/`restricts` where the operands differ in height by one and two levels, with
the taller tree on either side, plus the disjoint-spine case. -/

-- union: result lives at the taller height; taller operand on either side
#guard ((NatSet.ofList [1, 2]) ∪ (NatSet.ofList [1, 5000])).toList = [1, 2, 5000]   -- rhs taller (d=2)
#guard ((NatSet.ofList [1, 5000]) ∪ (NatSet.ofList [1, 2])).toList = [1, 2, 5000]   -- lhs taller (d=2)
#guard ((NatSet.ofList [40]) ∪ (NatSet.ofList [5000])).toList = [40, 5000]          -- disjoint spines
#guard (NatSet.ofList [1, 2]) ∪ (NatSet.ofList [1, 5000]) = (NatSet.ofList [1, 5000]) ∪ (NatSet.ofList [1, 2])

-- intersection: result lives at the smaller height; taller operand on either side
#guard ((NatSet.ofList [1, 2, 5000]) ∩ (NatSet.ofList [1, 3])).toList = [1]         -- lhs taller (d=2)
#guard ((NatSet.ofList [1, 3]) ∩ (NatSet.ofList [1, 2, 5000])).toList = [1]         -- rhs taller (d=2)
#guard ((NatSet.ofList [40]) ∩ (NatSet.ofList [5000])) = (∅ : NatSet)                -- disjoint spines

-- subset: rhs taller can still hold; lhs taller never does
#guard (NatSet.ofList [1]) ⊆ (NatSet.ofList [1, 5000])                               -- rhs taller, holds
#guard ¬ ((NatSet.ofList [1, 5000]) ⊆ (NatSet.ofList [1]))                           -- lhs taller, fails
#guard ¬ ((NatSet.ofList [2]) ⊆ (NatSet.ofList [1, 5000]))                           -- rhs taller, key absent

/-! ### Lattice laws across operations, on concrete (mixed-height) instances -/

private def a : NatSet := NatSet.ofList [1, 2, 40, 1000]
private def b : NatSet := NatSet.ofList [2, 3, 40, 50]
private def c : NatSet := NatSet.ofList [3, 40, 2000]

-- commutativity
#guard a ∪ b = b ∪ a
#guard a ∩ b = b ∩ a
-- associativity
#guard (a ∪ b) ∪ c = a ∪ (b ∪ c)
#guard (a ∩ b) ∩ c = a ∩ (b ∩ c)
-- idempotence
#guard a ∪ a = a
#guard a ∩ a = a
-- absorption
#guard a ∪ (a ∩ b) = a
#guard a ∩ (a ∪ b) = a
-- inclusion–exclusion on sizes
#guard (a ∪ b).size + (a ∩ b).size = a.size + b.size
-- difference complements intersection inside the left operand
#guard (a \ b) ∪ (a ∩ b) = a
#guard (a \ b) ∩ b = (∅ : NatSet)
#guard (a \ b).size + (a ∩ b).size = a.size
-- partition splits a set into disjoint parts recombining to the original
#guard (a.partition (fun k => k % 2 == 0)).1 ∪ (a.partition (fun k => k % 2 == 0)).2 = a
#guard (a.partition (fun k => k % 2 == 0)).1 ∩ (a.partition (fun k => k % 2 == 0)).2 = (∅ : NatSet)
-- union ⊇ each side; inter ⊆ each side
#guard a ⊆ (a ∪ b)
#guard b ⊆ (a ∪ b)
#guard (a ∩ b) ⊆ a
#guard (a ∩ b) ⊆ b
-- subset is transitive and antisymmetric (concretely)
#guard (NatSet.ofList [40]) ⊆ a ∧ a ⊆ (a ∪ b) ∧ (NatSet.ofList [40]) ⊆ (a ∪ b)
#guard a ⊆ b → b ⊆ a → a = b  -- antisymmetry

/-! ### Height growth then shrink round-trips back to a canonical value -/

-- inserting a deep key then erasing it returns the original (canonical) set
#guard (a.insert 1000000 |>.erase 1000000) = a
-- union with a tall singleton then intersecting it away shrinks back
#guard (a ∪ (NatSet.ofList [5000000])) ∩ a = a
-- building the same set two ways compares equal regardless of height history
#guard NatSet.ofList [1, 2, 40, 1000] = (NatSet.empty.insert 1000 |>.insert 40 |>.insert 2 |>.insert 1)

/-! ### Small stress test -/

private def big : NatSet := NatSet.ofList (List.range 100)

#guard big.size = 100
#guard 0 ∈ big ∧ 99 ∈ big ∧ 100 ∉ big
#guard big.toList = List.range 100
-- erasing every even number leaves the 50 odds, in order
private def odds : NatSet := (List.range 100).foldl (fun s k => if k % 2 == 0 then s.erase k else s) big
#guard odds.size = 50
#guard odds.toList = ((List.range 100).filter (fun k => k % 2 == 1))
#guard odds ⊆ big
#guard big ∩ odds = odds
#guard big ∪ odds = big

-- lawful structural equality, decidable propositional equality, and a hash that respects it
example : LawfulBEq NatSet := inferInstance
example : LawfulHashable NatSet := inferInstance
example : DecidableEq NatSet := inferInstance
-- with `DecidableEq`, `#guard` can take propositional `=` directly (decided via `beq`)
#guard NatSet.ofList [1, 2, 3] = NatSet.ofList [3, 2, 1, 2]
#guard ¬ (NatSet.ofList [1, 2] = NatSet.ofList [1, 2, 3])
-- the same set built two ways is `==` and hashes equally (canonical form)
#guard (NatSet.ofList [1, 2, 3] == NatSet.ofList [3, 2, 1, 2]) = true
#guard hash (NatSet.ofList [1, 2, 3]) = hash (NatSet.ofList [3, 2, 1, 2])
-- mixed heights collapse to the same canonical value, so hashes still agree
#guard hash (NatSet.ofList [1, 1000] |>.erase 1000) = hash (NatSet.ofList [1])

-- printing: `toString` braces the ascending elements; `repr` is valid Lean rebuilding the set
#guard toString (NatSet.ofList [40, 1, 2]) = "{1, 2, 40}"
#guard toString (∅ : NatSet) = "{}"
#guard reprStr (NatSet.ofList [2, 1]) = "NatSet.ofList [1, 2]"
#guard reprStr (∅ : NatSet) = "NatSet.ofList []"

end Tests

----------------------------------------------------------------------------------------------------
-- Theorems
----------------------------------------------------------------------------------------------------

namespace NatSet

/-- The empty set is a left identity of `∪` (union). -/
@[simp, grind =]
theorem union_empty_left (s : NatSet) : NatSet.empty ∪ s = s :=
  NatCollection.join_empty_left (fun _ _ => ()) s

/-- The empty set is a right identity of `∪` (union). -/
@[simp, grind =]
theorem union_empty_right (s : NatSet) : s ∪ NatSet.empty = s :=
  NatCollection.join_empty_right (fun _ _ => ()) s

/-- Union is commutative. (The set `combine` is constantly `()`, so flipping it is a no-op and the
flip law `NatCollection.join_comm` gives unconditional commutativity.) -/
theorem union_comm (s t : NatSet) : s ∪ t = t ∪ s :=
  NatCollection.join_comm (fun _ _ => ()) s t

/-- Union is associative. (The set `combine` is constantly `()`, which is trivially associative, so
`NatCollection.join_assoc` applies with no side condition.) -/
theorem union_assoc (s t u : NatSet) : (s ∪ t) ∪ u = s ∪ (t ∪ u) :=
  NatCollection.join_assoc (fun _ _ => ()) (fun _ _ _ => rfl) s t u

/-- The empty set is a left annihilator of `∩` (intersection). -/
@[simp, grind =]
theorem inter_empty_left (s : NatSet) : NatSet.empty ∩ s = NatSet.empty :=
  NatCollection.meet_empty_left (fun _ _ => ()) s

/-- The empty set is a right annihilator of `∩` (intersection). -/
@[simp, grind =]
theorem inter_empty_right (s : NatSet) : s ∩ NatSet.empty = NatSet.empty :=
  NatCollection.meet_empty_right (fun _ _ => ()) s

/-- Intersection is commutative. (The set `combine` is constantly `()`, so flipping it is a no-op
and the flip law `NatCollection.meet_comm` gives unconditional commutativity.) -/
theorem inter_comm (s t : NatSet) : s ∩ t = t ∩ s :=
  NatCollection.meet_comm (fun _ _ => ()) s t

/-- Intersection is associative. (The set `combine` is constantly `()`, which is trivially
associative, so `NatCollection.meet_assoc` applies with no side condition.) -/
theorem inter_assoc (s t u : NatSet) : (s ∩ t) ∩ u = s ∩ (t ∩ u) :=
  NatCollection.meet_assoc (fun _ _ => ()) (fun _ _ _ => rfl) s t u

/-- The empty set is a subset of (restricts) every set. -/
@[simp]
theorem subset_empty_left (s : NatSet) : NatSet.empty ⊆ s :=
  NatCollection.restricts_empty_left (fun _ _ => true) s

/-- Subset is reflexive: every set is a subset of itself. -/
@[simp]
theorem subset_refl (s : NatSet) : s ⊆ s :=
  NatCollection.restricts_refl (fun _ _ => true) (fun _ => rfl) s

/-- Intersection is a lower bound: `s ∩ t ⊆ s`. -/
theorem inter_subset_left (s t : NatSet) : s ∩ t ⊆ s :=
  NatCollection.meet_restricts_left (fun _ _ => true) (fun _ => rfl) (fun _ _ => ()) (fun _ _ => rfl) s t

/-- Intersection is a lower bound: `s ∩ t ⊆ t`. -/
theorem inter_subset_right (s t : NatSet) : s ∩ t ⊆ t :=
  NatCollection.meet_restricts_right (fun _ _ => true) (fun _ => rfl) (fun _ _ => ()) (fun _ _ => rfl) s t

/-- Intersection is the greatest lower bound: any set below both `s` and `t` is below `s ∩ t`.
Together with `inter_subset_left`/`inter_subset_right`, this makes `s ∩ t` the infimum of `s`, `t`
for `⊆`. -/
theorem subset_inter {s t u : NatSet} (h₁ : u ⊆ s) (h₂ : u ⊆ t) : u ⊆ s ∩ t :=
  NatCollection.meet_glb (fun _ _ => true) (fun _ => rfl) (fun _ _ => ()) (fun _ _ _ _ _ => rfl) u s t h₁ h₂

/-- Union is an upper bound: `s ⊆ s ∪ t`. -/
theorem subset_union_left (s t : NatSet) : s ⊆ s ∪ t :=
  NatCollection.restricts_join_left (fun _ _ => true) (fun _ => rfl) (fun _ _ => ()) (fun _ _ => rfl) s t

/-- Union is an upper bound: `t ⊆ s ∪ t`. -/
theorem subset_union_right (s t : NatSet) : t ⊆ s ∪ t :=
  NatCollection.restricts_join_right (fun _ _ => true) (fun _ => rfl) (fun _ _ => ()) (fun _ _ => rfl) s t

/-- Union is the least upper bound: any set containing both `s` and `t` contains `s ∪ t`. Together
with `subset_union_left`/`subset_union_right`, this makes `s ∪ t` the supremum of `s`, `t` for `⊆`. -/
theorem union_subset {s t u : NatSet} (h₁ : s ⊆ u) (h₂ : t ⊆ u) : s ∪ t ⊆ u :=
  NatCollection.join_lub (fun _ _ => true) (fun _ => rfl) (fun _ _ => ()) (fun _ _ _ _ _ => rfl) s t u h₁ h₂

/-- Subset is transitive: `s ⊆ t` and `t ⊆ u` give `s ⊆ u`. The set predicate `fun _ _ => true`
is trivially reflexive and transitive, so no side conditions are needed. -/
theorem subset_trans {s t u : NatSet} (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u :=
  NatCollection.restricts_trans (fun _ _ => true) (fun _ => rfl) (fun _ _ _ _ _ => rfl) s t u hst htu

/-- Subset is anti-symmetric: `s ⊆ t` and `t ⊆ s` force `s = t`. The set predicate
`fun _ _ => true` is trivially reflexive and (since `Unit` is a subsingleton) anti-symmetric, so
no side conditions are needed. -/
theorem subset_antisymm {s t : NatSet} (hst : s ⊆ t) (hts : t ⊆ s) : s = t :=
  NatCollection.restricts_antisymm (fun _ _ => true) (fun _ => rfl) (fun _ _ _ _ => rfl) s t hst hts

/-- A freshly-inserted element is a member: `k ∈ s.insert k`. -/
@[simp]
theorem mem_insert_self (s : NatSet) (k : Nat) : k ∈ s.insert k := by
  show NatCollection.contains (NatCollection.insert s k ()) k = true
  rw [NatCollection.contains_eq, NatCollection.get?_insert s k () k]
  simp

/-- Inserting an element already in the set returns the same set. -/
theorem insert_of_mem {s : NatSet} {k : Nat} (h : k ∈ s) : s.insert k = s := by
  have hk : NatCollection.get? s k = some () := by
    have hb : (NatCollection.get? s k).isSome = true := by
      rw [← NatCollection.contains_eq]; exact h
    cases hg : NatCollection.get? s k with
    | none => rw [hg] at hb; exact absurd hb (by decide)
    | some u => exact congrArg some (Subsingleton.elim u ())
  apply NatCollection.ext_get?
  intro j
  show NatCollection.get? (NatCollection.insert s k ()) j = NatCollection.get? s j
  rw [NatCollection.get?_insert s k () j]
  by_cases hj : j = k
  · rw [if_pos hj, hj, hk]
  · rw [if_neg hj]

/-- The union of a set with itself is the set. -/
@[simp]
theorem union_self (s : NatSet) : s ∪ s = s := by
  apply NatCollection.ext_get?
  intro k
  show NatCollection.get? (NatCollection.join (fun _ _ => ()) s s) k = NatCollection.get? s k
  rw [NatCollection.get?_join (fun _ _ => ()) s s k]
  cases NatCollection.get? s k with
  | none => rfl
  | some u => cases u; rfl

/-- The intersection of a set with itself is the set. -/
@[simp]
theorem inter_self (s : NatSet) : s ∩ s = s := by
  apply NatCollection.ext_get?
  intro k
  show NatCollection.get? (NatCollection.meet (fun _ _ => ()) s s) k = NatCollection.get? s k
  rw [NatCollection.get?_meet (fun _ _ => ()) s s k]
  cases NatCollection.get? s k with
  | none => rfl
  | some u => cases u; rfl

/-- Intersection distributes over union: `s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u)`. The set `combine` is
constantly `()`, so the distributivity side-condition is trivially `rfl`. -/
theorem inter_union_distrib (s t u : NatSet) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
  NatCollection.meet_join_distrib (fun _ _ => ()) (fun _ _ => ()) (fun _ _ _ => rfl) s t u

/-- Union distributes over intersection: `s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u)`. The set `combine` is
constantly `()`, so every lattice side-condition (idempotence, absorption, distributivity) is
trivially `rfl`. -/
theorem union_inter_distrib (s t u : NatSet) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
  NatCollection.join_meet_distrib (fun _ _ => ()) (fun _ _ => ())
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) s t u

/-- The minimum is a member: a `min? = some k` answer is an element of the set. -/
theorem min?_mem {s : NatSet} {k : Nat} (h : s.min? = some k) : k ∈ s :=
  NatCollection.contains_of_minKey? s k h

/-- The minimum is a lower bound: no element of the set is below `min?`'s answer. -/
theorem min?_le {s : NatSet} {k j : Nat} (h : s.min? = some k) (hj : j ∈ s) : k ≤ j :=
  NatCollection.minKey?_le s k j h hj

/-- The maximum is a member: a `max? = some k` answer is an element of the set. -/
theorem max?_mem {s : NatSet} {k : Nat} (h : s.max? = some k) : k ∈ s :=
  NatCollection.contains_of_maxKey? s k h

/-- The maximum is an upper bound: no element of the set is above `max?`'s answer. -/
theorem le_max? {s : NatSet} {k j : Nat} (h : s.max? = some k) (hj : j ∈ s) : j ≤ k :=
  NatCollection.le_maxKey? s k j h hj

/-- The successor is a member: a `succ? k = some j` answer is an element of the set. -/
theorem succ?_mem {s : NatSet} {k j : Nat} (h : s.succ? k = some j) : j ∈ s := by
  replace h : (NatCollection.entryGT? s k).map Prod.fst = some j := h
  obtain ⟨⟨j', v⟩, hgt, hfst⟩ := Option.map_eq_some_iff.mp h
  have hj : j' = j := hfst
  subst hj
  show NatCollection.contains s j' = true
  rw [NatCollection.contains_eq, NatCollection.get?_of_entryGT? s k j' v hgt]
  rfl

/-- The successor is strictly greater: `succ? k`'s answer lies strictly above `k`. -/
theorem succ?_gt {s : NatSet} {k j : Nat} (h : s.succ? k = some j) : k < j := by
  replace h : (NatCollection.entryGT? s k).map Prod.fst = some j := h
  obtain ⟨⟨j', v⟩, hgt, hfst⟩ := Option.map_eq_some_iff.mp h
  have hj : j' = j := hfst
  subst hj
  exact NatCollection.entryGT?_gt s k j' v hgt

/-- The successor is the *least* element above `k`: any member strictly above `k` is at or above
`succ? k`'s answer. With `succ?_mem` and `succ?_gt`, this pins the successor exactly. -/
theorem succ?_le {s : NatSet} {k j' j : Nat} (h : s.succ? k = some j') (hj : j ∈ s)
    (hk : k < j) : j' ≤ j := by
  replace h : (NatCollection.entryGT? s k).map Prod.fst = some j' := h
  obtain ⟨⟨j'', v⟩, hgt, hfst⟩ := Option.map_eq_some_iff.mp h
  have hj'' : j'' = j' := hfst
  subst hj''
  exact NatCollection.entryGT?_le s k j'' v j hgt hj hk

/-- A `none` from `succ?` is complete: no element of the set lies strictly above `k`. -/
theorem le_of_succ?_eq_none {s : NatSet} {k j : Nat} (h : s.succ? k = none) (hj : j ∈ s) :
    j ≤ k := by
  cases hgt : NatCollection.entryGT? s k with
  | none => exact NatCollection.le_of_entryGT?_eq_none s k hgt j hj
  | some e =>
    replace h : (NatCollection.entryGT? s k).map Prod.fst = none := h
    rw [hgt] at h
    exact absurd h (by simp)

/-- The predecessor is a member: a `pred? k = some j` answer is an element of the set. -/
theorem pred?_mem {s : NatSet} {k j : Nat} (h : s.pred? k = some j) : j ∈ s := by
  replace h : (NatCollection.entryLT? s k).map Prod.fst = some j := h
  obtain ⟨⟨j', v⟩, hlt, hfst⟩ := Option.map_eq_some_iff.mp h
  have hj : j' = j := hfst
  subst hj
  show NatCollection.contains s j' = true
  rw [NatCollection.contains_eq, NatCollection.get?_of_entryLT? s k j' v hlt]
  rfl

/-- The predecessor is strictly less: `pred? k`'s answer lies strictly below `k`. -/
theorem pred?_lt {s : NatSet} {k j : Nat} (h : s.pred? k = some j) : j < k := by
  replace h : (NatCollection.entryLT? s k).map Prod.fst = some j := h
  obtain ⟨⟨j', v⟩, hlt, hfst⟩ := Option.map_eq_some_iff.mp h
  have hj : j' = j := hfst
  subst hj
  exact NatCollection.entryLT?_lt s k j' v hlt

/-- The predecessor is the *greatest* element below `k`: any member strictly below `k` is at or
below `pred? k`'s answer. With `pred?_mem` and `pred?_lt`, this pins the predecessor exactly. -/
theorem le_pred? {s : NatSet} {k j' j : Nat} (h : s.pred? k = some j') (hj : j ∈ s)
    (hk : j < k) : j ≤ j' := by
  replace h : (NatCollection.entryLT? s k).map Prod.fst = some j' := h
  obtain ⟨⟨j'', v⟩, hlt, hfst⟩ := Option.map_eq_some_iff.mp h
  have hj'' : j'' = j' := hfst
  subst hj''
  exact NatCollection.le_entryLT? s k j'' v j hlt hj hk

/-- A `none` from `pred?` is complete: no element of the set lies strictly below `k`. -/
theorem ge_of_pred?_eq_none {s : NatSet} {k j : Nat} (h : s.pred? k = none) (hj : j ∈ s) :
    k ≤ j := by
  cases hlt : NatCollection.entryLT? s k with
  | none => exact NatCollection.ge_of_entryLT?_eq_none s k hlt j hj
  | some e =>
    replace h : (NatCollection.entryLT? s k).map Prod.fst = none := h
    rw [hlt] at h
    exact absurd h (by simp)

/-- `succEq?`'s answer is a member: a `succEq? k = some j` answer is an element of the set. -/
theorem succEq?_mem {s : NatSet} {k j : Nat} (h : s.succEq? k = some j) : j ∈ s := by
  replace h : (NatCollection.entryGE? s k).map Prod.fst = some j := h
  obtain ⟨⟨j', v⟩, hge, hfst⟩ := Option.map_eq_some_iff.mp h
  have hj : j' = j := hfst
  subst hj
  show NatCollection.contains s j' = true
  rw [NatCollection.contains_eq, NatCollection.get?_of_entryGE? s k j' v hge]
  rfl

/-- `succEq?`'s answer is at or above `k` (it is `k` itself exactly when `k ∈ s`). -/
theorem succEq?_ge {s : NatSet} {k j : Nat} (h : s.succEq? k = some j) : k ≤ j := by
  replace h : (NatCollection.entryGE? s k).map Prod.fst = some j := h
  obtain ⟨⟨j', v⟩, hge, hfst⟩ := Option.map_eq_some_iff.mp h
  have hj : j' = j := hfst
  subst hj
  exact NatCollection.entryGE?_ge s k j' v hge

/-- `succEq?` returns the *least* element at or above `k`: any member at or above `k` is at or
above `succEq? k`'s answer. With `succEq?_mem` and `succEq?_ge`, this pins it exactly. -/
theorem succEq?_le {s : NatSet} {k j' j : Nat} (h : s.succEq? k = some j') (hj : j ∈ s)
    (hk : k ≤ j) : j' ≤ j := by
  replace h : (NatCollection.entryGE? s k).map Prod.fst = some j' := h
  obtain ⟨⟨j'', v⟩, hge, hfst⟩ := Option.map_eq_some_iff.mp h
  have hj'' : j'' = j' := hfst
  subst hj''
  exact NatCollection.entryGE?_le s k j'' v j hge hj hk

/-- A `none` from `succEq?` is complete: every element of the set lies strictly below `k`. -/
theorem lt_of_succEq?_eq_none {s : NatSet} {k j : Nat} (h : s.succEq? k = none) (hj : j ∈ s) :
    j < k := by
  cases hge : NatCollection.entryGE? s k with
  | none => exact NatCollection.lt_of_entryGE?_eq_none s k hge j hj
  | some e =>
    replace h : (NatCollection.entryGE? s k).map Prod.fst = none := h
    rw [hge] at h
    exact absurd h (by simp)

/-- `predEq?`'s answer is a member: a `predEq? k = some j` answer is an element of the set. -/
theorem predEq?_mem {s : NatSet} {k j : Nat} (h : s.predEq? k = some j) : j ∈ s := by
  replace h : (NatCollection.entryLE? s k).map Prod.fst = some j := h
  obtain ⟨⟨j', v⟩, hle, hfst⟩ := Option.map_eq_some_iff.mp h
  have hj : j' = j := hfst
  subst hj
  show NatCollection.contains s j' = true
  rw [NatCollection.contains_eq, NatCollection.get?_of_entryLE? s k j' v hle]
  rfl

/-- `predEq?`'s answer is at or below `k` (it is `k` itself exactly when `k ∈ s`). -/
theorem predEq?_le {s : NatSet} {k j : Nat} (h : s.predEq? k = some j) : j ≤ k := by
  replace h : (NatCollection.entryLE? s k).map Prod.fst = some j := h
  obtain ⟨⟨j', v⟩, hle, hfst⟩ := Option.map_eq_some_iff.mp h
  have hj : j' = j := hfst
  subst hj
  exact NatCollection.entryLE?_le s k j' v hle

/-- `predEq?` returns the *greatest* element at or below `k`: any member at or below `k` is at
or below `predEq? k`'s answer. With `predEq?_mem` and `predEq?_le`, this pins it exactly. -/
theorem le_predEq? {s : NatSet} {k j' j : Nat} (h : s.predEq? k = some j') (hj : j ∈ s)
    (hk : j ≤ k) : j ≤ j' := by
  replace h : (NatCollection.entryLE? s k).map Prod.fst = some j' := h
  obtain ⟨⟨j'', v⟩, hle, hfst⟩ := Option.map_eq_some_iff.mp h
  have hj'' : j'' = j' := hfst
  subst hj''
  exact NatCollection.le_entryLE? s k j'' v j hle hj hk

/-- A `none` from `predEq?` is complete: every element of the set lies strictly above `k`. -/
theorem gt_of_predEq?_eq_none {s : NatSet} {k j : Nat} (h : s.predEq? k = none) (hj : j ∈ s) :
    k < j := by
  cases hle : NatCollection.entryLE? s k with
  | none => exact NatCollection.gt_of_entryLE?_eq_none s k hle j hj
  | some e =>
    replace h : (NatCollection.entryLE? s k).map Prod.fst = none := h
    rw [hle] at h
    exact absurd h (by simp)

/-- Membership in `split`'s left part: exactly the members strictly below the split key. -/
theorem mem_split_left {s : NatSet} {k j : Nat} : j ∈ (s.split k).1 ↔ j ∈ s ∧ j < k := by
  show NatCollection.contains (NatCollection.filterLt s k) j = true ↔ _
  rw [NatCollection.contains_eq, NatCollection.get?_filterLt]
  constructor
  · intro h
    by_cases hjk : j < k
    · rw [if_pos hjk] at h
      refine ⟨?_, hjk⟩
      show NatCollection.contains s j = true
      rw [NatCollection.contains_eq]
      exact h
    · rw [if_neg hjk] at h
      simp at h
  · intro h
    obtain ⟨hm, hjk⟩ := h
    rw [if_pos hjk]
    replace hm : NatCollection.contains s j = true := hm
    rw [NatCollection.contains_eq] at hm
    exact hm

/-- Membership in `split`'s right part: exactly the members at or above the split key. -/
theorem mem_split_right {s : NatSet} {k j : Nat} : j ∈ (s.split k).2 ↔ j ∈ s ∧ k ≤ j := by
  show NatCollection.contains (NatCollection.filterGE s k) j = true ↔ _
  rw [NatCollection.contains_eq, NatCollection.get?_filterGE]
  constructor
  · intro h
    by_cases hjk : k ≤ j
    · rw [if_pos hjk] at h
      refine ⟨?_, hjk⟩
      show NatCollection.contains s j = true
      rw [NatCollection.contains_eq]
      exact h
    · rw [if_neg hjk] at h
      simp at h
  · intro h
    obtain ⟨hm, hjk⟩ := h
    rw [if_pos hjk]
    replace hm : NatCollection.contains s j = true := hm
    rw [NatCollection.contains_eq] at hm
    exact hm

/-- Every member of `split`'s left part lies strictly below the split key. -/
theorem lt_of_mem_split_left {s : NatSet} {k j : Nat} (h : j ∈ (s.split k).1) : j < k :=
  (mem_split_left.mp h).2

/-- Every member of `split`'s right part lies at or above the split key. -/
theorem le_of_mem_split_right {s : NatSet} {k j : Nat} (h : j ∈ (s.split k).2) : k ≤ j :=
  (mem_split_right.mp h).2

/-- Membership in `range`: exactly the members within the inclusive window `[lo, hi]`. -/
theorem mem_range {s : NatSet} {lo hi j : Nat} :
    j ∈ s.range lo hi ↔ j ∈ s ∧ lo ≤ j ∧ j ≤ hi := by
  show NatCollection.contains (NatCollection.range s lo hi) j = true ↔ _
  rw [NatCollection.contains_eq, NatCollection.get?_range]
  constructor
  · intro h
    by_cases hin : lo ≤ j ∧ j ≤ hi
    · rw [if_pos hin] at h
      refine ⟨?_, hin.1, hin.2⟩
      show NatCollection.contains s j = true
      rw [NatCollection.contains_eq]
      exact h
    · rw [if_neg hin] at h
      simp at h
  · intro h
    obtain ⟨hm, h1, h2⟩ := h
    rw [if_pos ⟨h1, h2⟩]
    replace hm : NatCollection.contains s j = true := hm
    rw [NatCollection.contains_eq] at hm
    exact hm

/-- Membership after `erase`: `j` survives exactly when it was present and is not the erased
element. -/
theorem mem_erase {s : NatSet} {k j : Nat} : j ∈ s.erase k ↔ j ∈ s ∧ j ≠ k := by
  show NatCollection.contains (NatCollection.erase s k) j = true ↔ _
  rw [NatCollection.contains_erase, Bool.and_eq_true]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, ?_⟩
    intro he
    rw [he] at h2
    simp at h2
  · intro h
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, by simp [h2]⟩

/-- Disjointness characterization: `s.isDisjoint t` holds exactly when the two sets share no
element. -/
theorem isDisjoint_iff {s t : NatSet} : s.isDisjoint t = true ↔ ∀ k, k ∈ s → k ∉ t := by
  show NatCollection.isDisjoint s t = true ↔ _
  rw [NatCollection.isDisjoint_iff]
  constructor
  · intro h k hks hkt
    have hpair := h k
    replace hks : NatCollection.contains s k = true := hks
    replace hkt : NatCollection.contains t k = true := hkt
    rw [hks, hkt] at hpair
    exact absurd hpair (by decide)
  · intro h k
    cases hks : NatCollection.contains s k with
    | false => rw [Bool.false_and]
    | true => cases hkt : NatCollection.contains t k with
      | false => rw [Bool.and_false]
      | true => exact absurd (show k ∈ t from hkt) (h k hks)

/-- Disjointness is symmetric: if `s` is disjoint from `t`, then `t` is disjoint from `s`. -/
theorem isDisjoint_symm {s t : NatSet} (h : s.isDisjoint t = true) : t.isDisjoint s = true :=
  NatCollection.isDisjoint_symm h

/-- No element of `s` lies in `t` when the two sets are disjoint. -/
theorem not_mem_of_isDisjoint {s t : NatSet} {k : Nat} (h : s.isDisjoint t = true)
    (hk : k ∈ s) : k ∉ t :=
  isDisjoint_iff.mp h k hk

/-- `popMin?` pops the minimum: the popped element is `min?`'s answer (so `min?_mem` and
`min?_le` apply to it). -/
theorem popMin?_min {s : NatSet} {k : Nat} {s' : NatSet} (h : s.popMin? = some (k, s')) :
    s.min? = some k := by
  replace h : (NatCollection.popMinEntry? s).map (fun e => (e.1.1, e.2)) = some (k, s') := h
  obtain ⟨⟨⟨k', v⟩, c'⟩, hpop, hpair⟩ := Option.map_eq_some_iff.mp h
  replace hpair : (k', c') = (k, s') := hpair
  injection hpair with hk hc
  subst hk
  show (NatCollection.minEntry? s).map Prod.fst = some k'
  rw [NatCollection.minEntry?_of_popMinEntry? s (k', v) c' hpop]
  rfl

/-- `popMin?`'s rest is the set with the popped element erased. -/
theorem popMin?_erase {s : NatSet} {k : Nat} {s' : NatSet} (h : s.popMin? = some (k, s')) :
    s' = s.erase k := by
  replace h : (NatCollection.popMinEntry? s).map (fun e => (e.1.1, e.2)) = some (k, s') := h
  obtain ⟨⟨⟨k', v⟩, c'⟩, hpop, hpair⟩ := Option.map_eq_some_iff.mp h
  replace hpair : (k', c') = (k, s') := hpair
  injection hpair with hk hc
  subst hk; subst hc
  exact NatCollection.popMinEntry?_erase s (k', v) c' hpop

/-- The membership view of `popMin?`'s rest: the popped minimum is gone, everything else
survives. -/
theorem popMin?_mem {s : NatSet} {k : Nat} {s' : NatSet} (h : s.popMin? = some (k, s'))
    (j : Nat) : j ∈ s' ↔ j ∈ s ∧ j ≠ k := by
  rw [popMin?_erase h]
  exact mem_erase

/-- `popMin?` answers `none` exactly on the empty set (totality: a non-empty set always pops). -/
theorem popMin?_eq_none {s : NatSet} : s.popMin? = none ↔ s = ∅ := by
  constructor
  · intro h
    cases hpop : NatCollection.popMinEntry? s with
    | none => exact (NatCollection.popMinEntry?_eq_none s).mp hpop
    | some e =>
      replace h : (NatCollection.popMinEntry? s).map (fun e => (e.1.1, e.2)) = none := h
      rw [hpop] at h
      exact absurd h (by simp)
  · intro h
    subst h
    show (NatCollection.popMinEntry? (∅ : NatSet)).map (fun e => (e.1.1, e.2)) = none
    rw [(NatCollection.popMinEntry?_eq_none (∅ : NatSet)).mpr rfl]
    rfl

/-- `popMax?` pops the maximum: the popped element is `max?`'s answer (so `max?_mem` and
`le_max?` apply to it). -/
theorem popMax?_max {s : NatSet} {k : Nat} {s' : NatSet} (h : s.popMax? = some (k, s')) :
    s.max? = some k := by
  replace h : (NatCollection.popMaxEntry? s).map (fun e => (e.1.1, e.2)) = some (k, s') := h
  obtain ⟨⟨⟨k', v⟩, c'⟩, hpop, hpair⟩ := Option.map_eq_some_iff.mp h
  replace hpair : (k', c') = (k, s') := hpair
  injection hpair with hk hc
  subst hk
  show (NatCollection.maxEntry? s).map Prod.fst = some k'
  rw [NatCollection.maxEntry?_of_popMaxEntry? s (k', v) c' hpop]
  rfl

/-- `popMax?`'s rest is the set with the popped element erased. -/
theorem popMax?_erase {s : NatSet} {k : Nat} {s' : NatSet} (h : s.popMax? = some (k, s')) :
    s' = s.erase k := by
  replace h : (NatCollection.popMaxEntry? s).map (fun e => (e.1.1, e.2)) = some (k, s') := h
  obtain ⟨⟨⟨k', v⟩, c'⟩, hpop, hpair⟩ := Option.map_eq_some_iff.mp h
  replace hpair : (k', c') = (k, s') := hpair
  injection hpair with hk hc
  subst hk; subst hc
  exact NatCollection.popMaxEntry?_erase s (k', v) c' hpop

/-- The membership view of `popMax?`'s rest: the popped maximum is gone, everything else
survives. -/
theorem popMax?_mem {s : NatSet} {k : Nat} {s' : NatSet} (h : s.popMax? = some (k, s'))
    (j : Nat) : j ∈ s' ↔ j ∈ s ∧ j ≠ k := by
  rw [popMax?_erase h]
  exact mem_erase

/-- `popMax?` answers `none` exactly on the empty set. -/
theorem popMax?_eq_none {s : NatSet} : s.popMax? = none ↔ s = ∅ := by
  constructor
  · intro h
    cases hpop : NatCollection.popMaxEntry? s with
    | none => exact (NatCollection.popMaxEntry?_eq_none s).mp hpop
    | some e =>
      replace h : (NatCollection.popMaxEntry? s).map (fun e => (e.1.1, e.2)) = none := h
      rw [hpop] at h
      exact absurd h (by simp)
  · intro h
    subst h
    show (NatCollection.popMaxEntry? (∅ : NatSet)).map (fun e => (e.1.1, e.2)) = none
    rw [(NatCollection.popMaxEntry?_eq_none (∅ : NatSet)).mpr rfl]
    rfl

end NatSet

end NatCol
