/-
Micro-benchmarks for `NatCol`, comparing `NatSet` against Lean's `Std.HashSet Nat`
and `Lean.PersistentHashSet Nat`, following the recipe in `docs/DESIGN.md`.

For each *domain* of inputs
  * `sequential` — `0, 1, …, N-1`
  * `shuffled`   — a fixed seeded shuffle of `0 … N-1` (so values stay "small")
  * `random`     — `N` values in `[0, 2⁶³)`
we time seven *operations*
  * `insertion`  — build the set from the value list (report its size)
  * `lookup`     — sum the elements found while probing every value (report the sum)
  * `union`      — turn the values into singletons, then fold them pairwise into one set
  * `subset`     — build two equal sets from the values, then check `s ⊆ t` (report 1/0)
  * `erase present` — build the set, then erase every value (report the final size, 0)
  * `erase absent`  — build a set of the doubled (even) values, then erase the odd
                      shadows `2v+1` — every erase is a logical no-op (report the size)
  * `re-insert`     — build the set, then insert the same values again — every insert
                      is a logical no-op (report the size)

`Std.HashSet` ships a `union`; `PersistentHashSet` does not, so we synthesize one
with `fold` (per the design note). Neither ships a `subset`, so we synthesize those
from `all`/`contains` and `fold`/`contains` respectively — matching `NatSet.subset`,
each is `O(|s|)` membership checks. The two sets are equal, so the answer is always
`true` and every element is traversed (the full-work case, no early bail-out).

Each (data structure × domain × operation) cell runs in its *own* freshly spawned
worker process: the driver (run with no args, or a single `N` to override the
default) spawns one worker per cell, so wall-clock time and resident-memory growth
are each measured against a clean baseline, free of cross-benchmark GC interference.
Input generation is deterministic, so every worker rebuilds the very same list and
the three data structures are compared on identical inputs — and the reported
size/sum is a cross-check that they agree.

Run:  `lake exe nat-bench`           (default N, see `defaultN`)
      `lake exe nat-bench 100000`     (override N)
-/
import NatCol
import Std.Data.HashSet
import Lean.Data.PersistentHashSet

open NatCol

namespace Bench

/-- The number of values to feed each benchmark, unless overridden on the command line.
`docs/DESIGN.md` suggests `1000000`; the `union` benchmark in particular is heavy at
that size, so pass a smaller `N` for a quick run. -/
def defaultN : Nat := 1000000

/-! ## Deterministic input generation

Inputs come from a 64-bit linear congruential generator rather than a real RNG, so a
benchmark is reproducible and — crucially — every worker process regenerates the very
same list from a fixed seed. -/

/-- One step of a 64-bit LCG (Knuth's MMIX constants); `UInt64` arithmetic wraps mod 2⁶⁴. -/
@[inline]
def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

private def shuffleSeed : UInt64 := 0xdeadbeefcafef00d
private def randomSeed : UInt64 := 0x9e3779b97f4a7c15

/-- `[0, 1, …, n-1]`. -/
def seqData (n : Nat) : List Nat := (Array.range n).toList

/-- A fixed seeded shuffle of `[0, …, n-1]` (Fisher–Yates) — values stay "relatively small". -/
def shuffledData (n : Nat) : List Nat := Id.run do
  let mut a := Array.range n
  let mut s := shuffleSeed
  for i in [0 : n - 1] do
    let hi := n - 1 - i          -- runs n-1, n-2, …, 1
    s := lcg s
    a := a.swapIfInBounds hi (s.toNat % (hi + 1))
  return a.toList

/-- `n` "large" values, each in `[0, 2⁶³)` (the high 63 bits of the LCG state). -/
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

/-! ## Measurement

A benchmark's *setup* (building the input list, and for `lookup` the set itself) is done
by the caller before `measure`, so it isn't timed. `measure` then times the strict
construction of `build ()` and the resident-memory growth it causes, and finally reads a
`probe` (size/sum) off the still-live result. -/

/-- Evaluate `fn ()` *now*, as part of the IO sequence. `noinline` makes this an opaque
IO action the optimizer can neither inline nor float, so a pure computation it wraps is
forced at exactly this point — essential for timing a build and for materializing setup
data before the clock starts (a plain `let x := …` may be deferred to first use). -/
@[noinline]
def forceIO {α : Type} (fn : Unit → α) : IO α := pure (fn ())

/-- Keep `a` reachable across the resident-memory probe so it isn't collected early. -/
@[noinline]
def keepAlive {α : Type u} (_a : α) : IO Unit := pure ()

/-- Resident set size of process `pid` in KB, via `ps` (`0` if it can't be read). -/
def rssKB (pid : UInt32) : IO Nat := do
  try
    let out ← IO.Process.output { cmd := "ps", args := #["-o", "rss=", "-p", toString pid] }
    return out.stdout.trimAscii.toNat?.getD 0
  catch _ =>
    return 0

structure Sample where
  nanos : Nat
  deltaKB : Int
  check : Nat
deriving Inhabited

def measure {α : Type} (build : Unit → α) (probe : α → Nat) : IO Sample := do
  let pid ← IO.Process.getPID
  let m0 ← rssKB pid
  let t0 ← IO.monoNanosNow
  let a ← forceIO build            -- built strictly, inside the timed region
  let t1 ← IO.monoNanosNow
  let m1 ← rssKB pid               -- `a` is still live (used by `probe` below)
  let c := probe a
  keepAlive a
  return { nanos := t1 - t0, deltaKB := (m1 : Int) - (m0 : Int), check := c }

/-! ## The three operations, per data structure -/

private abbrev HSet := Std.HashSet Nat
private abbrev PSet := Lean.PersistentHashSet Nat

@[inline]
private def emptyHSet : HSet := Std.HashSet.emptyWithCapacity
@[inline]
private def emptyPSet : PSet := Lean.PersistentHashSet.empty

/-- `PersistentHashSet` has no `size`, so count via `fold`. -/
private def psSize (s : PSet) : Nat := s.fold (fun n _ => n + 1) 0

/-- `PersistentHashSet` has no `union`, so synthesize one with `fold` (design note). -/
private def psUnion (a b : PSet) : PSet := b.fold (·.insert ·) a

/-- `PersistentHashSet` has no `subset`/`all`, so synthesize `a ⊆ b` with `fold`: every
element of `a` is in `b`. (`fold` visits all of `a`; `&&` only short-circuits the membership
check, not the traversal — fine here, where every probe succeeds.) -/
private def psSubset (a b : PSet) : Bool := a.fold (fun acc x => acc && b.contains x) true

/-- One pairwise-union pass: `[a,b,c,d] → [a∪b, c∪d]`, `[a,b,c] → [a∪b, c]`. -/
private def unionPass {α : Type u} (u : α → α → α) : List α → List α
  | a :: b :: rest => u a b :: unionPass u rest
  | rest => rest

/-- Fold a list of sets pairwise — `[a,b,c,d] → [a∪b, c∪d] → [(a∪b)∪(c∪d)]` — until one remains. -/
private partial def unionAll {α : Type u} (u : α → α → α) (empty : α) : List α → α
  | [] => empty
  | [x] => x
  | xs => unionAll u empty (unionPass u xs)

-- insertion: build the set from `data`; check = size
def insertNatSet (data : List Nat) : IO Sample :=
  measure (fun _ => NatSet.ofList data) (·.size)
def insertHashSet (data : List Nat) : IO Sample :=
  measure (fun _ => data.foldl (·.insert ·) emptyHSet) (·.size)
def insertPHashSet (data : List Nat) : IO Sample :=
  measure (fun _ => data.foldl (·.insert ·) emptyPSet) psSize

-- lookup: set built in setup (untimed, forced); time the sum of every probe; check = sum
def lookupNatSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => NatSet.ofList data)
  measure (fun _ => data.foldl (fun acc k => if s.contains k then acc + k else acc) 0) id
def lookupHashSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => data.foldl (·.insert ·) emptyHSet)
  measure (fun _ => data.foldl (fun acc k => if s.contains k then acc + k else acc) 0) id
def lookupPHashSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => data.foldl (·.insert ·) emptyPSet)
  measure (fun _ => data.foldl (fun acc k => if s.contains k then acc + k else acc) 0) id

-- union: singletons built in setup (untimed, forced); time the pairwise fold; check = size
def unionNatSet (data : List Nat) : IO Sample := do
  let singles ← forceIO (fun _ => data.map (NatSet.empty.insert ·))
  measure (fun _ => unionAll NatSet.union NatSet.empty singles) (·.size)
def unionHashSet (data : List Nat) : IO Sample := do
  let singles ← forceIO (fun _ => data.map (emptyHSet.insert ·))
  measure (fun _ => unionAll Std.HashSet.union emptyHSet singles) (·.size)
def unionPHashSet (data : List Nat) : IO Sample := do
  let singles ← forceIO (fun _ => data.map (emptyPSet.insert ·))
  measure (fun _ => unionAll psUnion emptyPSet singles) psSize

-- subset: two equal sets built in setup (untimed, forced); time `s ⊆ t`; check = 1 if ⊆ else 0
private def boolCheck (b : Bool) : Nat := if b then 1 else 0
def subsetNatSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => NatSet.ofList data)
  let t ← forceIO (fun _ => NatSet.ofList data)
  measure (fun _ => s.subset t) boolCheck
def subsetHashSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => data.foldl (·.insert ·) emptyHSet)
  let t ← forceIO (fun _ => data.foldl (·.insert ·) emptyHSet)
  measure (fun _ => s.all t.contains) boolCheck
def subsetPHashSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => data.foldl (·.insert ·) emptyPSet)
  let t ← forceIO (fun _ => data.foldl (·.insert ·) emptyPSet)
  measure (fun _ => psSubset s t) boolCheck

-- erase (present): set built in setup (untimed, forced); time erasing every value; check = final
-- size (0 — every value, duplicates included, ends up erased)
def erasePresentNatSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => NatSet.ofList data)
  measure (fun _ => data.foldl (·.erase ·) s) (·.size)
def erasePresentHashSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => data.foldl (·.insert ·) emptyHSet)
  measure (fun _ => data.foldl (·.erase ·) s) (·.size)
def erasePresentPHashSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => data.foldl (·.insert ·) emptyPSet)
  measure (fun _ => data.foldl (·.erase ·) s) psSize

-- erase (absent): set built from the doubled (even) values, probe list = their odd shadows
-- `2v+1` (same magnitudes, guaranteed absent) — both in setup; time the all-no-op erase fold;
-- check = size (unchanged)
def eraseAbsentNatSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => NatSet.ofList (data.map (· * 2)))
  let absent ← forceIO (fun _ => data.map (2 * · + 1))
  measure (fun _ => absent.foldl (·.erase ·) s) (·.size)
def eraseAbsentHashSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => (data.map (· * 2)).foldl (·.insert ·) emptyHSet)
  let absent ← forceIO (fun _ => data.map (2 * · + 1))
  measure (fun _ => absent.foldl (·.erase ·) s) (·.size)
def eraseAbsentPHashSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => (data.map (· * 2)).foldl (·.insert ·) emptyPSet)
  let absent ← forceIO (fun _ => data.map (2 * · + 1))
  measure (fun _ => absent.foldl (·.erase ·) s) psSize

-- re-insert: set built in setup (untimed, forced); time inserting the same values again (every
-- insert a logical no-op); check = size (unchanged)
def reinsertNatSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => NatSet.ofList data)
  measure (fun _ => data.foldl (·.insert ·) s) (·.size)
def reinsertHashSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => data.foldl (·.insert ·) emptyHSet)
  measure (fun _ => data.foldl (·.insert ·) s) (·.size)
def reinsertPHashSet (data : List Nat) : IO Sample := do
  let s ← forceIO (fun _ => data.foldl (·.insert ·) emptyPSet)
  measure (fun _ => data.foldl (·.insert ·) s) psSize

def runOne (struct domain op : String) (n : Nat) : IO Sample := do
  let data := mkData domain n
  match op, struct with
  | "insert", "natset" => insertNatSet data
  | "insert", "hashset" => insertHashSet data
  | "insert", "phashset" => insertPHashSet data
  | "lookup", "natset" => lookupNatSet data
  | "lookup", "hashset" => lookupHashSet data
  | "lookup", "phashset" => lookupPHashSet data
  | "union", "natset" => unionNatSet data
  | "union", "hashset" => unionHashSet data
  | "union", "phashset" => unionPHashSet data
  | "subset", "natset" => subsetNatSet data
  | "subset", "hashset" => subsetHashSet data
  | "subset", "phashset" => subsetPHashSet data
  | "erasep", "natset" => erasePresentNatSet data
  | "erasep", "hashset" => erasePresentHashSet data
  | "erasep", "phashset" => erasePresentPHashSet data
  | "erasea", "natset" => eraseAbsentNatSet data
  | "erasea", "hashset" => eraseAbsentHashSet data
  | "erasea", "phashset" => eraseAbsentPHashSet data
  | "reinsert", "natset" => reinsertNatSet data
  | "reinsert", "hashset" => reinsertHashSet data
  | "reinsert", "phashset" => reinsertPHashSet data
  | _, _ => throw <| IO.userError s!"unknown benchmark: op={op} struct={struct}"

/-! ## Worker / driver plumbing -/

/-- The three data structures: `(cli-key, display name)`. -/
def structs : List (String × String) :=
  [("natset", "NatSet"), ("hashset", "Std.HashSet"), ("phashset", "PersistentHashSet")]
/-- The three input domains. -/
def domains : List (String × String) :=
  [("seq", "sequential"), ("shuffled", "shuffled"), ("random", "random 0..2⁶³")]
/-- The seven operations. -/
def ops : List (String × String) :=
  [("insert", "insertion"), ("lookup", "lookup"), ("union", "union"), ("subset", "subset"),
   ("erasep", "erase present"), ("erasea", "erase absent"), ("reinsert", "re-insert")]

/-- Format nanoseconds as milliseconds with two decimals, using integer math. -/
def fmtMs (nanos : Nat) : String :=
  let h := (nanos + 5000) / 10000      -- rounded hundredths of a millisecond
  s!"{h / 100}.{if h % 100 < 10 then "0" else ""}{h % 100}"

def padLeft (w : Nat) (s : String) : String := "".pushn ' ' (w - min w s.length) ++ s
def padRight (w : Nat) (s : String) : String := s ++ "".pushn ' ' (w - min w s.length)

private def labelW : Nat := 32
private def colW : Nat := 20

/-- Print one table: rows are `domain / op`, columns are the data structures. -/
def printTable (title : String) (rows : List (String × List (Option Sample)))
    (cell : Sample → String) : IO Unit := do
  IO.println title
  IO.println <| structs.foldl (fun acc (_, nm) => acc ++ padLeft colW nm) (padRight labelW "")
  for (label, cells) in rows do
    IO.println <| cells.foldl
      (fun acc c => acc ++ padLeft colW (c.elim "—" cell)) (padRight labelW label)
  IO.println ""

/-- Confirm the size/sum cross-check agrees across the structures of each row. -/
def printChecks (rows : List (String × List (Option Sample))) : IO Unit := do
  IO.println "Cross-check (size / sum — identical inputs, so must agree across structures)"
  for (label, cells) in rows do
    let vals := cells.filterMap (·.map (·.check))
    let status := match vals with
      | [] => "no data"
      | v :: rest => if rest.all (· == v) then s!"{v}  OK" else s!"MISMATCH {vals}"
    IO.println <| padRight labelW label ++ status
  IO.println ""

/-- Worker: run a single benchmark and print one machine-readable result line. -/
def worker (struct domain op : String) (n : Nat) : IO Unit := do
  let s ← runOne struct domain op n
  IO.println s!"RESULT\t{s.nanos}\t{s.deltaKB}\t{s.check}"

def parseResult (out : String) : Option Sample := do
  let line ← out.splitOn "\n" |>.find? (·.startsWith "RESULT")
  match line.splitOn "\t" with
  | [_, ns, kb, ck] => return { nanos := (← ns.toNat?), deltaKB := (← kb.toInt?), check := (← ck.toNat?) }
  | _ => none

/-- Driver: spawn one worker per cell, collect results, print the summary tables. -/
def driver (n : Nat) : IO Unit := do
  let self ← IO.appPath
  IO.println s!"nat-col micro-benchmarks   (N = {n})"
  IO.println "  NatSet  vs  Std.HashSet Nat  vs  Lean.PersistentHashSet Nat"
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

def main (args : List String) : IO Unit := do
  match args with
  | ["worker", struct, domain, op, nStr] =>
    Bench.worker struct domain op (nStr.toNat?.getD Bench.defaultN)
  | [nStr] =>
    match nStr.toNat? with
    | some n => Bench.driver n
    | none => throw <| IO.userError s!"expected a numeric N, got '{nStr}'"
  | [] => Bench.driver Bench.defaultN
  | _ => throw <| IO.userError "usage: nat-bench [N]"
