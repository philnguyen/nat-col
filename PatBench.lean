/-
# Path-compression prototype (`pat-bench`)

An **unverified** prototype used to re-validate the memory/speed upside of *path
compression* over `NatSet`'s 32-ary trie on **sparse, large** keys. `NatSet`'s height is
tied to the largest key, so a single 63-bit key builds a chain of ~13 single-child `Node`s
(`docs/DESIGN.md` "Future improvements"). Path compression collapses those chains: a
single-child run creates *no* node at all.

`PSet` below is a 32-way, big-endian Patricia set (the "PSet64" design): keyed internally on
`UInt64` (one `Nat → UInt64` at the API boundary, machine-word shifts during descent), with
nat-col's exact 32-key bitmap leaf, so the comparison isolates the path-compression effect to
the interior. It is validated against `NatSet` by the `#guard`s below, then benchmarked by the
same worker-per-cell harness as `nat-bench`.

This is NOT part of the verified library (`defaultTargets = ["NatCol"]`); it is a throwaway
measurement tool. The recursive set ops are `partial` (no termination proofs — correctness is
established empirically by the `#guard` agreement with `NatSet`). Keys are assumed `< 2⁶⁴`
(the prototype's only simplification; all three bench domains are `< 2⁶³`).

Run:  `lake exe pat-bench`            (default N)
      `lake exe pat-bench 100000`     (override N)
-/
import NatCol

open NatCol   -- NatSet + the public bit helpers: popCount/testBit/setBit/arrayIndex/lowestSetIdx/clearLowest

namespace Pat

----------------------------------------------------------------------------------------------------
-- The path-compressed set
----------------------------------------------------------------------------------------------------

/-- A 32-way big-endian Patricia set over `UInt64` keys.
* `tip prefix bits` — a leaf holding every key with `key >>> 5 == prefix`, the bottom 5 bits
  given by the set positions of `bits` (identical to a `NatSet` height-0 leaf, but the entire
  upper path is compressed into `prefix`). A lone key is a single `tip`, zero interior nodes.
* `bin rep level mask kids` — a path-compressed branch on the 5-bit `chunk` at `level` (always
  `≥ 1`); `kids` holds the present children compactly (`kids.size = popCount mask`). `rep` is an
  arbitrary member key of the subtree, kept so the common prefix `rep >>> 5*(level+1)` and a
  branch point can be recovered in O(1) without descending. -/
inductive PSet where
  | nil
  | tip (pfx : UInt64) (bits : UInt32)
  | bin (rep : UInt64) (level : UInt32) (mask : UInt32) (kids : Array PSet)
  deriving Inhabited

/-- The 5-bit chunk of `k` at `level` (0 = least-significant chunk), as a slot index `0..31`. -/
@[inline] def chunkAt (k : UInt64) (level : UInt32) : UInt32 :=
  ((k >>> (5 * level.toUInt64)) &&& 31).toUInt32

/-- The shift dropping every chunk at or below `level`, leaving the prefix strictly above it. -/
@[inline] def shiftAbove (level : UInt32) : UInt64 := 5 * level.toUInt64 + 5

/-- The bits of `k` strictly above `level` — the common prefix shared by everything under a
`bin` branching at `level`. Guards the word width: a `UInt64` shift count is taken mod 64, so
a shift `≥ 64` would wrap; everything above bit 63 is `0`, so return `0` directly. -/
@[inline] def prefixAbove (k : UInt64) (level : UInt32) : UInt64 :=
  let s := shiftAbove level
  if s ≥ 64 then 0 else k >>> s

/-- The level (highest 5-bit chunk index) at which `a` and `b` first differ. Only meaningful
for `a ≠ b`; computed off the highest differing bit of `a ^^^ b`. -/
@[inline] def branchLevel (a b : UInt64) : UInt32 := (Nat.log2 (a ^^^ b).toNat / 5).toUInt32

/-- An arbitrary member key of a non-empty set (O(1)): a `bin` stores one in `rep`; a `tip`
rebuilds one from its prefix and lowest set bit. -/
@[inline] def repKey : PSet → UInt64
  | .nil            => 0
  | .tip pfx bits   => (pfx <<< 5) ||| (lowestSetIdx bits).toUInt64
  | .bin rep ..      => rep

/-- The branch level of a node from the top: `0` for a leaf, the branch `level` for a `bin`. -/
@[inline] def nodeLevel : PSet → UInt32
  | .nil       => 0
  | .tip ..     => 0
  | .bin _ l .. => l

/-- The singleton set `{k}` — a single `tip`, no interior nodes. -/
@[inline] def singleton (k : UInt64) : PSet := .tip (k >>> 5) (setBit 0 (chunkAt k 0))

/-- Combine two subtrees with **disjoint** prefixes (rep keys `ka ≠ kb`) under a fresh `bin`
branching at their first differing chunk. -/
@[inline] def join (ka : UInt64) (a : PSet) (kb : UInt64) (b : PSet) : PSet :=
  let l := branchLevel ka kb
  let ca := chunkAt ka l
  let cb := chunkAt kb l
  .bin ka l (setBit (setBit 0 ca) cb) (if ca < cb then #[a, b] else #[b, a])

/-- Insert key `k` (already `UInt64`) into a set. Descends by chunk while the prefix matches;
on a prefix mismatch (a divergence at a compressed level) it `join`s a fresh singleton in. -/
partial def insertU (k : UInt64) : PSet → PSet
  | .nil => singleton k
  | .tip pfx bits =>
    if k >>> 5 == pfx then .tip pfx (setBit bits (chunkAt k 0))
    else join k (singleton k) ((pfx <<< 5) ||| (lowestSetIdx bits).toUInt64) (.tip pfx bits)
  | .bin rep l mask kids =>
    if prefixAbove k l == prefixAbove rep l then
      let c := chunkAt k l
      let i := arrayIndex mask c
      if testBit mask c then .bin rep l mask (kids.set! i (insertU k (kids[i]!)))
      else .bin rep l (setBit mask c) (kids.insertIdx! i (singleton k))
    else join k (singleton k) rep (.bin rep l mask kids)

/-- Membership (classic Patricia: route by chunk, verify the prefix only at the leaf). -/
partial def containsU (k : UInt64) : PSet → Bool
  | .nil => false
  | .tip pfx bits => k >>> 5 == pfx && testBit bits (chunkAt k 0)
  | .bin _ l mask kids =>
    let c := chunkAt k l
    if testBit mask c then containsU k (kids[arrayIndex mask c]!) else false

mutual

/-- Union of two path-compressed sets (the known weak spot — rebuilds child arrays at every
shared node, unlike `NatSet.join`'s one-sided-subtree reuse). Aligns by branch level/prefix:
equal level+prefix merges per slot; otherwise the higher-branching `bin` absorbs the other, or
the two are `join`ed if their prefixes are disjoint. -/
partial def unionU : PSet → PSet → PSet
  | .nil, t => t
  | s, .nil => s
  | s, t =>
    let ls := nodeLevel s
    let lt := nodeLevel t
    let ks := repKey s
    let kt := repKey t
    if ls == lt then
      if prefixAbove ks ls == prefixAbove kt ls then
        match s, t with
        | .tip pfx b1, .tip _ b2 => .tip pfx (b1 ||| b2)
        | .bin rep l m1 k1, .bin _ _ m2 k2 =>
          .bin rep l (m1 ||| m2) (mergeKids m1 k1 m2 k2 (m1 ||| m2) (Array.mkEmpty (popCount (m1 ||| m2))))
        | _, _ => join ks s kt t
      else join ks s kt t
    else if ls > lt then
      match s with
      | .bin rep l mask kids => absorb rep l mask kids kt t
      | _ => join ks s kt t          -- unreachable: ls > lt ≥ 0 ⇒ s is a bin
    else
      match t with
      | .bin rep l mask kids => absorb rep l mask kids ks s
      | _ => join ks s kt t          -- unreachable: lt > ls ≥ 0 ⇒ t is a bin

/-- Fold the smaller tree `o` (rep key `ko`) into the `bin` `⟨rep, l, mask, kids⟩` that branches
higher, routing by `o`'s chunk at `l` (or `join`ing if `o` falls outside the bin's prefix). -/
partial def absorb (rep : UInt64) (l mask : UInt32) (kids : Array PSet) (ko : UInt64) (o : PSet) : PSet :=
  if prefixAbove ko l == prefixAbove rep l then
    let c := chunkAt ko l
    let i := arrayIndex mask c
    if testBit mask c then .bin rep l mask (kids.set! i (unionU (kids[i]!) o))
    else .bin rep l (setBit mask c) (kids.insertIdx! i o)
  else join rep (.bin rep l mask kids) ko o

/-- Build the merged child array of two same-level, same-prefix bins by bit-scanning the union
mask in ascending slot order (so push order = compact array index). -/
partial def mergeKids (m1 : UInt32) (k1 : Array PSet) (m2 : UInt32) (k2 : Array PSet)
    (rem : UInt32) (acc : Array PSet) : Array PSet :=
  if rem == 0 then acc
  else
    let c := lowestSetIdx rem
    let inA := testBit m1 c
    let inB := testBit m2 c
    let child :=
      if inA && inB then unionU (k1[arrayIndex m1 c]!) (k2[arrayIndex m2 c]!)
      else if inA then k1[arrayIndex m1 c]!
      else k2[arrayIndex m2 c]!
    mergeKids m1 k1 m2 k2 (clearLowest rem) (acc.push child)

end

/-- Apply `f` to every key in the set, folding through `init` (order unspecified). -/
partial def foldKeys {β : Type} (f : β → Nat → β) : β → PSet → β
  | init, .nil => init
  | init, .tip pfx bits => tipFold f pfx bits init
  | init, .bin _ _ _ kids => kids.foldl (fun acc c => foldKeys f acc c) init
where
  /-- Fold the keys of one `tip` by bit-scanning its bitset. -/
  tipFold {β : Type} (f : β → Nat → β) (pfx : UInt64) (bits : UInt32) (init : β) : β :=
    if bits == 0 then init
    else tipFold f pfx (clearLowest bits) (f init (((pfx <<< 5) ||| (lowestSetIdx bits).toUInt64).toNat))

----------------------------------------------------------------------------------------------------
-- Public API (matching `NatSet`)
----------------------------------------------------------------------------------------------------

@[inline] def PSet.empty : PSet := .nil
@[inline] def PSet.insert (s : PSet) (k : Nat) : PSet := insertU k.toUInt64 s
@[inline] def PSet.contains (s : PSet) (k : Nat) : Bool := containsU k.toUInt64 s
@[inline] def PSet.union (a b : PSet) : PSet := unionU a b

partial def PSet.size : PSet → Nat
  | .nil => 0
  | .tip _ bits => popCount bits
  | .bin _ _ _ kids => kids.foldl (fun acc c => acc + c.size) 0

def PSet.ofList (ks : List Nat) : PSet := ks.foldl (·.insert ·) .nil

/-- `a ⊆ b`: every key of `a` is in `b` (O(|a|) membership checks, matching `NatSet.subset`). -/
def PSet.subset (a b : PSet) : Bool := foldKeys (fun acc k => acc && b.contains k) true a

----------------------------------------------------------------------------------------------------
-- Validation: `PSet` must agree with the verified `NatSet`
----------------------------------------------------------------------------------------------------

private def seqKeys : List Nat := (List.range 1000)
private def sparseKeys : List Nat :=
  [0, 31, 32, 1023, 1024, 42, 1000000, 999999999, 4294967296, 9223372036854775807, 7]
private def evens : List Nat := (List.range 500).map (2 * ·)
private def odds : List Nat := (List.range 500).map (2 * · + 1)

-- size agrees (dense and sparse)
#guard (PSet.ofList seqKeys).size == (NatSet.ofList seqKeys).size
#guard (PSet.ofList sparseKeys).size == (NatSet.ofList sparseKeys).size
-- membership agrees for present keys and for absent keys
#guard sparseKeys.all fun k => (PSet.ofList sparseKeys).contains k == (NatSet.ofList sparseKeys).contains k
#guard [1, 33, 1025, 5, 123456, 8].all fun k =>
  (PSet.ofList sparseKeys).contains k == (NatSet.ofList sparseKeys).contains k
#guard !(PSet.ofList sparseKeys).contains 12345
#guard (PSet.ofList sparseKeys).contains 1000000
-- union agrees (size) and is order/structure independent
#guard ((PSet.ofList evens).union (PSet.ofList odds)).size
        == ((NatSet.ofList evens).union (NatSet.ofList odds)).size
#guard ((PSet.ofList sparseKeys).union (PSet.ofList seqKeys)).size
        == ((NatSet.ofList sparseKeys).union (NatSet.ofList seqKeys)).size
-- idempotent insert / union
#guard ((PSet.empty.insert 42).insert 42).size == 1
#guard ((PSet.ofList sparseKeys).union (PSet.ofList sparseKeys)).size == (PSet.ofList sparseKeys).size
-- subset
#guard (PSet.ofList sparseKeys).subset (PSet.ofList sparseKeys)
#guard (PSet.ofList evens).subset ((PSet.ofList evens).union (PSet.ofList odds))
#guard !(PSet.ofList sparseKeys).subset (PSet.ofList seqKeys)

----------------------------------------------------------------------------------------------------
-- Benchmark harness (a focused copy of `Bench.lean`'s — NatSet vs PSet only)
----------------------------------------------------------------------------------------------------

namespace Bench

/-- Values per benchmark unless overridden on the command line. -/
def defaultN : Nat := 1000000

/-- One step of a 64-bit LCG (Knuth's MMIX constants); `UInt64` arithmetic wraps mod 2⁶⁴. -/
@[inline] def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

private def shuffleSeed : UInt64 := 0xdeadbeefcafef00d
private def randomSeed : UInt64 := 0x9e3779b97f4a7c15

def seqData (n : Nat) : List Nat := (Array.range n).toList

def shuffledData (n : Nat) : List Nat := Id.run do
  let mut a := Array.range n
  let mut s := shuffleSeed
  for i in [0 : n - 1] do
    let hi := n - 1 - i
    s := lcg s
    a := a.swapIfInBounds hi (s.toNat % (hi + 1))
  return a.toList

/-- `n` "large" values, each in `[0, 2⁶³)` — the domain path compression targets. -/
def randomData (n : Nat) : List Nat := Id.run do
  let mut a := Array.mkEmpty n
  let mut s := randomSeed
  for _ in [0 : n] do
    s := lcg s
    a := a.push (s >>> 1).toNat
  return a.toList

def mkData : String → Nat → List Nat
  | "seq", n => seqData n
  | "shuffled", n => shuffledData n
  | "random", n => randomData n
  | _, _ => []

/-- Force `fn ()` *now*, opaquely, so a pure build is timed at exactly this point. -/
@[noinline] def forceIO {α : Type} (fn : Unit → α) : IO α := pure (fn ())
@[noinline] def keepAlive {α : Type u} (_a : α) : IO Unit := pure ()

/-- Resident set size of process `pid` in KB, via `ps` (`0` if unreadable). -/
def rssKB (pid : UInt32) : IO Nat := do
  try
    let out ← IO.Process.output { cmd := "ps", args := #["-o", "rss=", "-p", toString pid] }
    return out.stdout.trimAscii.toNat?.getD 0
  catch _ => return 0

structure Sample where
  nanos : Nat
  deltaKB : Int
  check : Nat
  deriving Inhabited

def measure {α : Type} (build : Unit → α) (probe : α → Nat) : IO Sample := do
  let pid ← IO.Process.getPID
  let m0 ← rssKB pid
  let t0 ← IO.monoNanosNow
  let a ← forceIO build
  let t1 ← IO.monoNanosNow
  let m1 ← rssKB pid
  let c := probe a
  keepAlive a
  return { nanos := t1 - t0, deltaKB := (m1 : Int) - (m0 : Int), check := c }

/-- One pairwise-union pass: `[a,b,c,d] → [a∪b, c∪d]`. -/
private def unionPass {α : Type u} (u : α → α → α) : List α → List α
  | a :: b :: rest => u a b :: unionPass u rest
  | rest => rest

/-- Fold a list of sets pairwise until one remains. -/
private partial def unionAll {α : Type u} (u : α → α → α) (empty : α) : List α → α
  | [] => empty
  | [x] => x
  | xs => unionAll u empty (unionPass u xs)

-- NatSet operations (verified baseline)
def insertNatSet (data : List Nat) : IO Sample :=
  measure (fun _ => NatSet.ofList data) (·.size)
def lookupNatSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => NatSet.ofList data)
  measure (fun _ => data.foldl (fun acc k => if s.contains k then acc + k else acc) 0) id
def unionNatSet (data : List Nat) : IO Sample := do
  let singles ← forceIO (fun _ => data.map (NatSet.empty.insert ·))
  measure (fun _ => unionAll NatSet.union NatSet.empty singles) (·.size)
private def boolCheck (b : Bool) : Nat := if b then 1 else 0
def subsetNatSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => NatSet.ofList data)
  let t ← forceIO (fun _ => NatSet.ofList data)
  measure (fun _ => s.subset t) boolCheck

-- PSet operations (path-compressed prototype)
def insertPSet (data : List Nat) : IO Sample :=
  measure (fun _ => PSet.ofList data) (·.size)
def lookupPSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => PSet.ofList data)
  measure (fun _ => data.foldl (fun acc k => if s.contains k then acc + k else acc) 0) id
def unionPSet (data : List Nat) : IO Sample := do
  let singles ← forceIO (fun _ => data.map (PSet.empty.insert ·))
  measure (fun _ => unionAll PSet.union PSet.empty singles) (·.size)
def subsetPSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => PSet.ofList data)
  let t ← forceIO (fun _ => PSet.ofList data)
  measure (fun _ => s.subset t) boolCheck

def runOne (struct domain op : String) (n : Nat) : IO Sample := do
  let data := mkData domain n
  match op, struct with
  | "insert", "natset" => insertNatSet data
  | "insert", "patset" => insertPSet data
  | "lookup", "natset" => lookupNatSet data
  | "lookup", "patset" => lookupPSet data
  | "union", "natset" => unionNatSet data
  | "union", "patset" => unionPSet data
  | "subset", "natset" => subsetNatSet data
  | "subset", "patset" => subsetPSet data
  | _, _ => throw <| IO.userError s!"unknown benchmark: op={op} struct={struct}"

def structs : List (String × String) := [("natset", "NatSet"), ("patset", "PSet64")]
def domains : List (String × String) :=
  [("seq", "sequential"), ("shuffled", "shuffled"), ("random", "random 0..2⁶³")]
def ops : List (String × String) :=
  [("insert", "insertion"), ("lookup", "lookup"), ("union", "union"), ("subset", "subset")]

def fmtMs (nanos : Nat) : String :=
  let h := (nanos + 5000) / 10000
  s!"{h / 100}.{if h % 100 < 10 then "0" else ""}{h % 100}"

def padLeft (w : Nat) (s : String) : String := "".pushn ' ' (w - min w s.length) ++ s
def padRight (w : Nat) (s : String) : String := s ++ "".pushn ' ' (w - min w s.length)

private def labelW : Nat := 26
private def colW : Nat := 20

def printTable (title : String) (rows : List (String × List (Option Sample)))
    (cell : Sample → String) : IO Unit := do
  IO.println title
  IO.println <| structs.foldl (fun acc (_, nm) => acc ++ padLeft colW nm) (padRight labelW "")
  for (label, cells) in rows do
    IO.println <| cells.foldl
      (fun acc c => acc ++ padLeft colW (c.elim "—" cell)) (padRight labelW label)
  IO.println ""

def printChecks (rows : List (String × List (Option Sample))) : IO Unit := do
  IO.println "Cross-check (size / sum — identical inputs, so must agree across structures)"
  for (label, cells) in rows do
    let vals := cells.filterMap (·.map (·.check))
    let status := match vals with
      | [] => "no data"
      | v :: rest => if rest.all (· == v) then s!"{v}  OK" else s!"MISMATCH {vals}"
    IO.println <| padRight labelW label ++ status
  IO.println ""

def worker (struct domain op : String) (n : Nat) : IO Unit := do
  let s ← runOne struct domain op n
  IO.println s!"RESULT\t{s.nanos}\t{s.deltaKB}\t{s.check}"

def parseResult (out : String) : Option Sample := do
  let line ← out.splitOn "\n" |>.find? (·.startsWith "RESULT")
  match line.splitOn "\t" with
  | [_, ns, kb, ck] => return { nanos := (← ns.toNat?), deltaKB := (← kb.toInt?), check := (← ck.toNat?) }
  | _ => none

def driver (n : Nat) : IO Unit := do
  let self ← IO.appPath
  IO.println s!"path-compression prototype   (N = {n})"
  IO.println "  NatSet  vs  PSet64 (32-way big-endian Patricia, path-compressed)"
  IO.println "  each cell timed in its own process; memory = resident-set growth (ΔRSS)"
  IO.println ""
  let mut rows : List (String × List (Option Sample)) := []
  for (dKey, dName) in domains do
    for (oKey, oName) in ops do
      let label := s!"{dName} / {oName}"
      let mut cells : List (Option Sample) := []
      for (sKey, _) in structs do
        IO.eprint s!"  {label} / {sKey} ... "
        let out ← IO.Process.output { cmd := self.toString, args := #["worker", sKey, dKey, oKey, toString n] }
        let cell := if out.exitCode == 0 then parseResult out.stdout else none
        match cell with
        | some s => IO.eprintln s!"{fmtMs s.nanos} ms, {s.deltaKB} KB"
        | none => IO.eprintln s!"FAILED ({out.stderr.trimAscii})"
        cells := cells ++ [cell]
      rows := rows ++ [(label, cells)]
  IO.println ""
  printTable "Time (ms)" rows (fun s => fmtMs s.nanos)
  printTable "Memory ΔRSS (KB)" rows (fun s => toString s.deltaKB)
  printChecks rows

end Bench

end Pat

def main (args : List String) : IO Unit := do
  match args with
  | ["worker", struct, domain, op, nStr] =>
    Pat.Bench.worker struct domain op (nStr.toNat?.getD Pat.Bench.defaultN)
  | [nStr] =>
    match nStr.toNat? with
    | some n => Pat.Bench.driver n
    | none => throw <| IO.userError s!"expected a numeric N, got '{nStr}'"
  | [] => Pat.Bench.driver Pat.Bench.defaultN
  | _ => throw <| IO.userError "usage: pat-bench [N]"
