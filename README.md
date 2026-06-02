# nat-col

Verified maps and sets on `Nat` with efficient **lattice operations** — union/intersection
(`join`/`meet`), subset/restriction (`restricts`), and friends — written in Lean 4, with the
distributive-lattice laws proven, not just tested.

It is inspired by the HAMT (hash array-mapped trie), but with two twists: there is **no hashing**
(a `Nat` key is its own path), and **keys are never stored** — the trie's *shape* alone records
which keys are present.

```lean
import NatCol
open NatCol

#eval (NatSet.ofList [3, 1, 2, 1]).toList            -- [1, 2, 3]   (deduplicated, sorted)
#eval ((NatSet.ofList [1, 2]) ∪ (NatSet.ofList [2, 3])).toList   -- [1, 2, 3]
#eval ((NatSet.ofList [1, 2, 3]) ∩ (NatSet.ofList [2, 3, 4])).toList  -- [2, 3]

example (s t u : NatSet) : (s ∪ t) ∪ u = s ∪ (t ∪ u) := NatSet.union_assoc s t u
example (s t : NatSet)   : s ∩ t ⊆ s                  := NatSet.inter_subset_left s t
```

## Highlights

- **`NatSet`** — a set of natural numbers; `∪` (union), `∩` (intersection), `⊆` (subset), `∈`.
- **`NatMap α`** — a map `Nat → α`; lattice ops take a `combine`/`rel` to resolve coinciding keys.
- **Canonical representation** — the trie is kept in a unique normal form, so **structural equality
  *is* logical equality**: `NatSet`/`NatMap` are `LawfulBEq`, `DecidableEq`, and `LawfulHashable`.
  Two sets built in any order, at any intermediate height, compare and hash equal.
- **Mask-driven lattice ops** — `join`/`meet`/`restricts` work off each node's 32-bit
  `positionsMask`, reusing/discarding whole subtrees that occur on only one side instead of
  walking them.
- **Proven distributive-lattice laws** — identities, annihilators, commutativity, associativity,
  idempotence, absorption, least-upper-/greatest-lower-bound, and both distributive laws — see
  [Verified laws](#verified-laws).
- **`NatMap` is a lawful `Functor`** via `NatMap.map`.

## Design

At the heart of both collections is a 32-ary trie. A `Nat` key is read 5 bits at a time (`2⁵ = 32`):
each 5-bit chunk selects a slot at one level of the trie, and the tree is only ever **as tall as the
largest key requires**. A node stores a `UInt32` `positionsMask` (which of the 32 slots are
occupied) plus a *compact* array holding exactly the occupied children — no empty slots, no stored
keys.

```lean
-- the generic, leaf-parameterised core (simplified)
structure Node (α : Type u) where
  positionsMask    : UInt32          -- which of the 32 slots are present
  elements         : Array α         -- exactly `positionsMask.popCount` children, in order
  …

abbrev Tree (leaf : Type u) : Nat → Type u
  | 0     => leaf                    -- the bottom level is a leaf…
  | n + 1 => Node (Tree leaf n)      -- …above it, nested nodes

structure NatCollection (leaf : Type u) where
  height : Nat
  tree   : Tree leaf height
  wf     : Tree.Canonical height tree   -- the canonical-shape invariant, carried in the type

def NatMap (α : Type u) := NatCollection (Node α)   -- leaves are value-nodes
def NatSet              := NatCollection UInt32      -- leaves are 32-bit bitsets
```

A **`NatSet`** bottoms out in a `UInt32` leaf used as a 32-element bitset of the lowest 5 bits, so
the leaf carries **no boxed payload** and the lattice ops become plain bitwise `|||` / `&&&` / mask
tests. (`UInt32` rather than `UInt64` because boxed polymorphic positions store a `UInt32`
unallocated, by bit-shifting, whereas a `UInt64` would allocate.) A **`NatMap α`** uses a `Node α`
leaf — itself a sparse 32-slot map of values.

Every operation and every theorem is written **once** generically over `NatCollection`/`Tree`,
abstracting the leaf behind a `LeafOps` typeclass, then instantiated for `NatSet` (the `UInt32`
leaf) and `NatMap` (the `Node α` leaf).

A longer write-up — invariants, the canonical form, the mask-merge optimisations — lives in
[`docs/DESIGN.md`](docs/DESIGN.md).

## Layout

| File | Role |
| --- | --- |
| [`NatCol/Bits.lean`](NatCol/Bits.lean) | `UInt32` bit primitives — chunking a `Nat`, `popCount` (SWAR), set/clear/test bit |
| [`NatCol/Node.lean`](NatCol/Node.lean) | the sparse 32-slot `Node`: `insert`/`erase`/`get?`, mask-scan `join`/`meet`/`restricts`, `map`, `filterMap` |
| [`NatCol/Tree.lean`](NatCol/Tree.lean) | the height-indexed `Tree`, the `Canonical` invariant, and the `get?`-denotational layer the proofs ride on |
| [`NatCol/Collection.lean`](NatCol/Collection.lean) | `NatCollection`: the user-facing wrapper, `LeafOps` typeclass, generic ops + generic laws |
| [`NatCol/Set.lean`](NatCol/Set.lean) | `NatSet` — `UInt32`-leaf instance, `∪`/`∩`/`⊆`/`∈` API, set laws |
| [`NatCol/Map.lean`](NatCol/Map.lean) | `NatMap α` — `Node α`-leaf instance, key/value API, `Functor`, map laws |
| [`Bench.lean`](Bench.lean) | the `nat-bench` micro-benchmark executable |

Within each `NatCol/*.lean` the declarations are split under two banners: **Implementation** first
(definitions + inline `#guard` example-tests), then **Theorems**.

## API at a glance

Both collections follow the naming of `Std.Data.HashMap`/`HashSet`.

**`NatSet`** — `empty`/`∅`, `isEmpty`, `size`, `contains` / `∈`, `insert`, `erase`, `ofList`,
`toList`, `fold`/`foldM`, `all`/`any`/`filter` (+ monadic `allM`/`anyM`/`filterM`), and the lattice
ops `union` (`∪`), `inter` (`∩`), `subset` (`⊆`).

**`NatMap α`** — the above keyed form (`get?`, `getD`, `modify`, value-aware `fold`/`filter`/…),
plus `join`/`meet`/`restricts` taking a `combine : α → α → α` (resp. `rel : α → α → Bool`) to
reconcile values at coinciding keys, and `NatMap.map : (α → β) → NatMap α → NatMap β` (the `Functor`
action `f <$> m`).

`filter` and the monadic variants return a **canonical** result — equal to the collection rebuilt
from the survivors, with the height shrunk back when deep keys drop out.

## Verified laws

Proven generically over `NatCollection` and lifted to `NatSet`/`NatMap` (the `NatMap` versions are
*relative* to the supplied `combine`/`rel`, e.g. needing it to be associative/commutative/reflexive):

- `∅` is a two-sided **identity** of `join` and a two-sided **annihilator** of `meet`; `∅ ⊆` everything.
- `join`/`meet` are **commutative**, **associative**, and **idempotent** (`s ∪ s = s`, `s ∩ s = s`); **absorption** holds.
- `restricts` is a **partial order**: reflexive, transitive, anti-symmetric (anti-symmetry gives `⊆`-based extensionality).
- `join` is the **least upper bound** and `meet` the **greatest lower bound** for `restricts`.
- both **distributive** laws: `meet` over `join` and `join` over `meet`.
- `get?`-after-`insert`, the membership/lookup spec, inclusion–exclusion on `size`, etc.
- `NatSet`/`NatMap` are `LawfulBEq`; `NatMap` is a `LawfulFunctor`.

Each law is backed by `#guard` example-tests on concrete (including mixed-height) instances sitting
next to the operations.

## Building, testing, benchmarking

Requires the Lean toolchain pinned in [`lean-toolchain`](lean-toolchain)
(`leanprover/lean4:v4.30.0`); [`elan`](https://github.com/leanprover/elan) installs it
automatically.

```sh
lake build                  # build the library (this also runs every #guard test)
lake exe nat-bench          # micro-benchmarks (default N = 1,000,000)
lake exe nat-bench 100000   # …with a smaller N for a quick run
lake clean                  # clean build artifacts
```

Tests are inline `#guard` / `example`-with-proof commands, so **`lake build` is the test run** — a
failed example fails the build. There is no separate test target.

`nat-bench` ([`Bench.lean`](Bench.lean)) compares `NatSet` against Lean's `Std.HashSet Nat` and
`Lean.PersistentHashSet Nat` across three input *domains* (`sequential`, `shuffled`, `random`) and
four *operations* (`insertion`, `lookup`, `union`, `subset`). Each `(structure × domain × operation)`
cell runs in its **own freshly-spawned worker process** so wall-clock time and resident-memory growth
are measured against a clean baseline; input generation is deterministic, and a reported size/sum
cross-checks that the structures agree. `subset` builds two equal sets and checks `s ⊆ t` (always
`true`, so every element is traversed); neither hash structure ships a `subset`, so they synthesize
one from `all`/`fold` + `contains`, matching `NatSet.subset` at `O(|s|)` membership checks.

### Sample results

Measured on an **Apple M4 Pro MacBook** at `N = 1,000,000` with Lean `v4.30.0`. Lower is better;
the size/sum cross-check agreed across all three structures on every row.

**Time (ms)**

| Domain / operation | `NatSet` | `Std.HashSet` | `PersistentHashSet` |
| --- | ---: | ---: | ---: |
| sequential / insertion | 92.11 | 21.40 | 27.56 |
| sequential / lookup | 16.94 | 14.05 | 31.28 |
| sequential / union | **133.06** | 620.45 | 533.20 |
| sequential / subset | **0.96** | 34.70 | 62.92 |
| shuffled / insertion | 139.61 | 46.51 | 48.01 |
| shuffled / lookup | **19.18** | 57.43 | 47.36 |
| shuffled / union | **429.61** | 894.56 | 864.65 |
| shuffled / subset | **0.78** | 166.39 | 75.08 |
| random 0..2⁶³ / insertion | 720.80 | 68.04 | 74.41 |
| random 0..2⁶³ / lookup | 1142.31 | 252.76 | 321.21 |
| random 0..2⁶³ / union | 1129.48 | 909.63 | 707.17 |
| random 0..2⁶³ / subset | 2212.61 | **155.90** | 237.26 |

**Memory — resident-set growth (KB)**

| Domain / operation | `NatSet` | `Std.HashSet` | `PersistentHashSet` |
| --- | ---: | ---: | ---: |
| sequential / insertion | **64** | 28 784 | 4 256 |
| sequential / lookup | 64 | 64 | 32 |
| sequential / union | **39 232** | 89 872 | 74 928 |
| sequential / subset | 64 | 32 | 64 |
| shuffled / insertion | **64** | 28 784 | 5 680 |
| shuffled / lookup | 64 | 64 | 64 |
| shuffled / union | 76 384 | 89 840 | 70 320 |
| shuffled / subset | 0 | 32 | 64 |
| random 0..2⁶³ / insertion | 473 616 | 28 784 | 30 336 |
| random 0..2⁶³ / lookup | 80 | 112 | 64 |
| random 0..2⁶³ / union | 74 944 | 90 352 | 101 808 |
| random 0..2⁶³ / subset | 48 | 32 | 32 |

Reading it: `NatSet` is strongest on **dense, "small" key domains** (`sequential`/`shuffled`) — it
wins `union` outright and inserts with negligible resident growth, since dense keys share trie
spines and the leaves carry no boxed payload. `subset` makes the gap starkest: on dense keys it
finishes in **under a millisecond** (35–200× ahead), because equal tries compare their present-masks
in lockstep with no per-element hashing, whereas the hash structures must probe every element. On
**sparse `random` keys** it pays for the deep, mostly one-child spines — slower lookups, a ~2.2 s
`subset` walk, heavier insertion memory — where the hash structures hold up better. (`subset`, like
`lookup`, is read-only, so its resident growth is noise across the board.) Numbers will vary run to
run and across machines.

## Relation to Gödel hashing

A close cousin in spirit is [Gödel hashing](https://matt.might.net/papers/liang2014godel.pdf)
(Liang & Might, 2014), which encodes a finite set as a single integer — the product of one distinct
prime per element — so that union becomes `lcm`, intersection `gcd`, subset divisibility, and
equality numeric equality. Both schemes are **canonical** (equal sets share one representation) and
both realise the *same* distributive lattice; Gödel hashing simply maps into the divisibility
lattice `(ℕ, gcd, lcm)` and inherits its laws from number theory, where nat-col builds the lattice
on a trie and proves the laws in Lean. The difference is regime: Gödel hashing is wonderfully terse
and ideal for memoising small, dense universes (its home turf of static analysis), but the encoding
integer grows with every element, needs an element→prime oracle, and can only be read back out by
*factoring* it — so cardinality, enumeration, and arbitrary-valued maps are costly or out of reach.
nat-col keeps keys as trie paths instead, trading that arithmetic elegance for cheap enumeration,
real `NatMap`s over arbitrary values, `O(key length)` incremental updates, and large, sparse keys.

## Status

The trie core, `NatSet`/`NatMap`, their lattice operations, and the laws above are implemented and
proven. The derived `IndexedMap`/`IndexedSet` collections (for any type with an injection to `Nat`)
sketched in [`docs/DESIGN.md`](docs/DESIGN.md) are a planned addition. See the design doc's
"Future improvements" for the known memory-locality trade-off (two pointer hops per level, pending a
safe dependent-array representation).

## License

[Apache License 2.0](LICENSE).
