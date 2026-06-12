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
  Two sets built in any order compare and hash equal.
- **Mask-driven lattice ops** — `join`/`meet`/`restricts` work off each node's 32-bit
  `positionsMask`, reusing/discarding whole subtrees that occur on only one side instead of
  walking them.
- **Proven distributive-lattice laws** — identities, annihilators, commutativity, associativity,
  idempotence, absorption, least-upper-/greatest-lower-bound, and both distributive laws — see
  [Verified laws](#verified-laws).
- **`NatMap` is a lawful `Functor`** via `NatMap.map`.

## Design

At the heart of both collections is a **path-compressed (Patricia) 32-ary trie**. A `Nat` key is
read 5 bits at a time (`2⁵ = 32`): each 5-bit chunk selects a slot. Rather than store a node per
level (so the tree would be as tall as the largest key), a `bin` branches **only where its children
actually diverge**, and a `tip` carries a whole compressed run of keys that share their high bits —
so a single sparse/large key is *one* node, not a chain of single-child ones. Each `bin` stores a
`UInt32` `mask` (which of the 32 slots are occupied) plus a *compact* array holding exactly the
occupied children — no empty slots, no stored keys.

```lean
-- the generic, leaf-parameterised core (simplified)
inductive PTree (L : Type u)
  | nil
  | tip (pfx : Nat) (leaf : L)                                     -- a compressed run of keys sharing high bits
  | bin (pfx level : Nat) (mask : UInt32) (kids : Array (PTree L)) -- branch at `level`; `mask`/`kids` are compact

structure Node (α : Type u) where     -- the map leaf
  positionsMask : UInt32              -- which of the 32 slots are present
  elements      : Array α             -- exactly `positionsMask.popCount` values, in order
  …

structure NatCollection (L : Type u) {V : Type u} [LeafOps L V] where
  tree : PTree L
  wf   : PTree.WF tree                -- the canonical-shape invariant (no nil children / empty leaves)

def NatMap (α : Type u) := NatCollection (Node α)   -- leaves are value-nodes
def NatSet              := NatCollection UInt32      -- leaves are 32-bit bitsets
```

A **`NatSet`** bottoms out in a `UInt32` leaf used as a 32-element bitset of the lowest 5 bits, so
the leaf carries **no boxed payload** and the lattice ops become plain bitwise `|||` / `&&&` / mask
tests. (`UInt32` rather than `UInt64` because boxed polymorphic positions store a `UInt32`
unallocated, by bit-shifting, whereas a `UInt64` would allocate.) A **`NatMap α`** uses a `Node α`
leaf — itself a sparse 32-slot map of values.

Every operation and every theorem is written **once** generically over `PTree`/`NatCollection`,
abstracting the leaf behind a `LeafOps` typeclass, then instantiated for `NatSet` (the `UInt32`
leaf) and `NatMap` (the `Node α` leaf).

A longer write-up — invariants, the canonical form, the mask-merge optimisations — lives in
[`docs/DESIGN.md`](docs/DESIGN.md).

## Layout

| File | Role |
| --- | --- |
| [`NatCol/Bits.lean`](NatCol/Bits.lean) | `UInt32` bit primitives — chunking a `Nat`, `popCount` (SWAR), set/clear/test bit |
| [`NatCol/Node.lean`](NatCol/Node.lean) | the sparse 32-slot `Node` (`insert`/`erase`/`get?`, mask-scan `join`/`meet`/`restricts`, `map`, `filterMap`), plus the `LeafOps` typeclass + value-level `optV` algebra |
| [`NatCol/PTree.lean`](NatCol/PTree.lean) | the path-compressed `PTree` over `LeafOps`: ops, the `WF` invariant, structural `beq`, the `map` functor, and the `get?`-denotational lattice/order layer the proofs ride on |
| [`NatCol/Collection.lean`](NatCol/Collection.lean) | `NatCollection`: the user-facing `{ tree, wf }` wrapper, generic ops + generic laws (one-line lifts of the `PTree` seams) |
| [`NatCol/Set.lean`](NatCol/Set.lean) | `NatSet` — `UInt32`-leaf instance, `∪`/`∩`/`⊆`/`∈` API, set laws |
| [`NatCol/Map.lean`](NatCol/Map.lean) | `NatMap α` — `Node α`-leaf instance, key/value API, `Functor`, map laws |
| [`Bench.lean`](Bench.lean) | the `nat-bench` micro-benchmark executable |

Within each `NatCol/*.lean` the declarations are split under two banners: **Implementation** first
(definitions + inline `#guard` example-tests), then **Theorems**.

## API at a glance

Both collections follow the naming of `Std.Data.HashMap`/`HashSet`.

**`NatSet`** — `empty`/`∅`, `isEmpty`, `size`, `contains` / `∈`, `insert`, `erase`, `ofList`,
`toList`, `fold`/`foldM`, `all`/`any`/`filter`/`partition` (+ monadic `allM`/`anyM`/`filterM`), and
the lattice ops `union` (`∪`), `inter` (`∩`), `diff` (`\`), `symmDiff`, `subset` (`⊆`),
`isDisjoint`.

**`NatMap α`** — the above keyed form (`get?`, `getD`, `alter`, `modify`, value-aware
`fold`/`filter`/`partition`/…, plus `keys`/`values` and `domain`, the key set as a `NatSet`), plus
`join`/`meet`/`restricts` taking a `combine : α → α → α` (resp. `rel : α → α → Bool`) to
reconcile values at coinciding keys, key-only `diff`/`symmDiff`/`isDisjoint`, and
`NatMap.map : (α → β) → NatMap α → NatMap β` (the `Functor` action `f <$> m`).

**Ordered queries** — the trie keeps keys in ascending order structurally, so these are O(depth)
descents (a hash structure scans all *n* entries): `min?`/`max?` (`minKey?`/`maxKey?`/
`minEntry?`/`maxEntry?` on maps), successor/predecessor `succ?`/`pred?`/`succEq?`/`predEq?`
(`entryGT?`/`entryGE?`/`entryLT?`/`entryLE?` on maps), `popMin?`/`popMax?` (the priority-queue
step), and the bound prunes `split` (at a key) and `range` (inclusive window), which keep whole
off-path subtrees shared instead of copying them.

**Structural merges** — `diff`, `symmDiff`, and `isDisjoint` are Patricia merge walks, not
per-element probes: subtrees whose prefixes cannot meet are kept whole (shared) or answered in
O(1), aligned leaves combine in one bitwise op, and `isDisjoint` is allocation-free with an early
exit at the first shared key.

`filter`, the monadic variants, and all of the above return a **canonical** result — equal to the
collection rebuilt from the survivors, so structural equality still coincides with logical
equality.

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

Each law is backed by `#guard` example-tests on concrete (including multi-level, cross-prefix)
instances sitting next to the operations.

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

Measured on an **Apple M4 Pro MacBook** at `N = 1,000,000` with Lean `v4.30.0`, on the
path-compressed `NatSet`. Lower is better; the size/sum cross-check agreed across all three
structures on every row.

**Time (ms)**

| Domain / operation | `NatSet` | `Std.HashSet` | `PersistentHashSet` |
| --- | ---: | ---: | ---: |
| sequential / insertion | 97.79 | **21.64** | 29.40 |
| sequential / lookup | 18.16 | **13.03** | 29.36 |
| sequential / union | **29.70** | 648.67 | 539.85 |
| sequential / subset | **0.87** | 38.88 | 64.85 |
| shuffled / insertion | 165.28 | **41.04** | 52.20 |
| shuffled / lookup | **19.46** | 48.84 | 37.36 |
| shuffled / union | **445.75** | 915.34 | 863.86 |
| shuffled / subset | **0.78** | 142.45 | 74.75 |
| random 0..2⁶³ / insertion | 455.22 | 65.66 | **63.76** |
| random 0..2⁶³ / lookup | 384.25 | **240.17** | 315.09 |
| random 0..2⁶³ / union | 806.01 | 928.90 | **708.51** |
| random 0..2⁶³ / subset | 244.59 | **146.88** | 233.08 |

**Memory — resident-set growth (KB)**

| Domain / operation | `NatSet` | `Std.HashSet` | `PersistentHashSet` |
| --- | ---: | ---: | ---: |
| sequential / insertion | **96** | 28 784 | 4 256 |
| sequential / lookup | 64 | 64 | 32 |
| sequential / union | **41 200** | 89 872 | 74 928 |
| sequential / subset | 80 | 32 | 64 |
| shuffled / insertion | **112** | 28 784 | 5 680 |
| shuffled / lookup | 64 | 64 | 64 |
| shuffled / union | 108 720 | 89 904 | **70 304** |
| shuffled / subset | 80 | 32 | 64 |
| random 0..2⁶³ / insertion | 79 328 | **28 784** | 30 336 |
| random 0..2⁶³ / lookup | 80 | 112 | 64 |
| random 0..2⁶³ / union | 115 008 | **90 368** | 101 808 |
| random 0..2⁶³ / subset | 48 | 32 | 32 |

Reading it: `NatSet` wins `union` and `subset` across **every** key domain — often by an order of
magnitude — because equal/aligned tries merge and compare their present-masks in lockstep with no
per-element hashing, whereas the hash structures must rebuild or probe every element. On **dense,
"small" key domains** it also inserts with negligible resident growth (the leaves carry no boxed
payload). On **sparse `random` keys**, path compression collapses the single-child runs that a
height-indexed trie would build — so `subset` finishes in ~0.24 s (was ~2.2 s before compression),
lookups are competitive, and insertion memory dropped ~6×; the hash structures still lead on raw
random insert/lookup throughput and on peak `union` memory. (`subset`/`lookup` are read-only, so
their resident growth is noise.) Numbers vary run to run and across machines.

## Related work

### Gödel hashing

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

### Okasaki–Gill Patricia tries

The direct ancestor of nat-col's core is *Fast Mergeable Integer Maps* (Okasaki & Gill, 1998), the
paper that revived Morrison's PATRICIA trees as a purely functional data structure and became the
basis of Haskell's `Data.IntMap`/`IntSet`. Its insight is the one this library is built
on: when an integer key is its own path and a branch node is created **only where keys diverge**
(path compression), the tree's shape is canonical, updates touch one root-to-leaf path, and
`union`/`intersection`/`subset` become divide-and-conquer **merges** — subtrees are aligned by
prefix and reused or discarded wholesale rather than probed element by element, which is exactly
why a Patricia trie merges fast where a hash table must rebuild. nat-col's `join`/`meet`/`restricts`
are that merge, and the benchmark story above (winning `union`/`subset` across every key domain) is
the paper's title claim playing out. What nat-col changes is the *node*: Okasaki & Gill branch on
**one bit** at a time and store one key per leaf, whereas nat-col consumes **5 bits** per level
through a 32-slot mask plus a popcount-indexed compact child array (the HAMT node layout — minus
the hashing) and bottoms out in 32-bit bitset leaves, so the trie is a fifth as deep, the bottom
five bits of every key are plain bitwise ops, and keys are never stored at all. And where the paper
argues correctness informally and validates the design with benchmarks, nat-col proves the lattice
laws machine-checked in Lean.

## Status

The path-compressed trie core, `NatSet`/`NatMap`, their lattice operations, and the laws above are
implemented and proven (no `sorry`, no `partial` in the verified library). The core representation
was migrated from a height-indexed GADT trie to the path-compressed `PTree` while keeping every
theorem statement byte-identical; see [`docs/DESIGN.md`](docs/DESIGN.md) for the measured speedups.
The derived `IndexedMap`/`IndexedSet` collections (for any type with an injection to `Nat`) sketched
in the design doc are a planned addition, as is the `union`-throughput / memory-locality work under
its "Future improvements".

## License

[Apache License 2.0](LICENSE).
