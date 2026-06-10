# Overview

This project implements maps and sets on `Nat` with efficient lattice operations (e.g. `join`, `meet`, and `restricts`). It is inspired by HAMT, except there's no hashing, and the keys/elements aren't literally stored.

At the heart of `NatMap` and `NatSet` is a **path-compressed (Patricia) 32-ary trie** (à la HAMT, but with single-child runs collapsed). The core type is height-erased and generic over a leaf interface `LeafOps L V`:
```lean
inductive PTree (L : Type u)
  | nil
  | tip (pfx : Nat) (leaf : L)                                    -- a compressed run of keys sharing high bits
  | bin (pfx level : Nat) (mask : UInt32) (kids : Array (PTree L)) -- branch at `level`; `mask` is the slot bitset
```
A `bin` branches at the chunk `level` where its children actually diverge (path compression), storing its present children compactly (`kids.size = mask.popCount`). A `tip` carries the leaf — itself a sparse 32-slot structure:
```lean
private structure Node (α : Type u) where      -- the map leaf
  positionsMask    : UInt32
  elements         : Array α
  elements_compact : elements.size = positionsMask.popCount
```
A `NatSet`'s leaf is `UInt32` (a 32-bit set of the low chunk); a `NatMap`'s leaf is `Node α`. We use `UInt32` (not `UInt64`) because polymorphic array positions are Lean-boxed: `UInt64` would allocate, `UInt32` only bit-shifts. The leaf interface `LeafOps L V` packages the per-leaf `get?`/`insert`/`join`/`meet`/`restricts`/… (plus the proof obligations the generic theorems route through), so the whole trie — operations and proofs — is written once over `LeafOps` and instantiated for both leaves.
```lean
structure NatCollection (L : Type u) {V : Type u} [LeafOps L V] where
  tree : PTree L
  wf : PTree.WF tree           -- canonical: no `nil` children, no empty leaves, path-compression minimal

def NatMap (α : Type u) : Type u := NatCollection (Node α)
def NatSet : Type := NatCollection UInt32
```

`PTree.WF` is the canonical-shape invariant: a single sparse/large key produces *one* `tip` rather than a chain of single-child nodes whose height is tied to the largest key. Every operation returns a `WF` trie, so structural equality (`PTree.beq`) coincides with logical equality.

# Programming APIs

At the minimum, there are basic operations following the naming convention in `Std.Data.{HashMap,HashSet}`:
* `empty`
* `isEmpty`
* `size` (either as a cached field or operation)
* `contains`
* `insert`
* `erase`
* `modify`
* `ofList`

Additionally, there are `join` and `meet`:
* With `NatSet`, `join` and `meet` are `union` and `intersection`, respectively.
* With `NatMap`, `join` and `meet` also take a function deciding how to combine values on key collision.
* Optimize these operations based on the `positionMask`s. For example:
  - With `join`, reuse children that only come from one side, without recursively traversing them
  - With `meet`, discard children that only come from one side.

There's also `restricts`:
* With `NatSet`, this means "is subset of"
* With `NatMap`, this takes another predicate on pairs of values, to check whether the first map's domain restricts the second map's, and all values at coinciding keys satisfy the passed in predicate.
* As with `join` and `meet`, optimize the operations by taking advantage of the `positionMask`s.

These operations are implemented once generically on `PTree`/`NatCollection` (over `LeafOps`), then instantiated for `NatMap` and `NatSet`.

# Theorems

`NatMap` and `NatSet` behave like a distributive lattice:
* The empty map/set is left and right identities of `join`
* The empty map/set is left and right annihilator of `meet`
* The empty map/set `restricts` everything
* A set/map `join`/`meet` with itself is itself.
* `join`/`meet` is associative and commutative (in the case of map, it's relative w.r.t. the passed in operation on colliding values)
* `restricts` is reflexive, transitive, and anti-symmetric. (Again, the `NatMap`'s version is relatively so, depending on the passed in predicate on values.)
* `join` of two maps/sets gives the tightest map/set that contains both
* `meet` of two maps/sets gives the largest map/set that `restricts` both
* `join` distributes over `meet`
* `meet` distributes over `join`

Miscelaneous:
* Collections are instances of `LawfulBEq`
* Map is an instance of `LawfulFunctor`

These theorems are stated and proven once generically for `PTree`/`NatCollection` (over `LeafOps`), then instantiated for `NatMap` and `NatSet`. The whole lattice/order/functor suite routes through a handful of denotational seams (`get?_empty`/`get?_insert`/`get?_join`/`get?_meet`/`get?_restricts`) and extensionality (`ext_get?`).

# Derived collections

Convenient collections `IndexedMap k v` and `IndexedSet k` for any type that has an injection to `Nat`:
```lean
class Countable (α : Type u) where
  index : α → Nat
  index_injective : index a = index b → a = b

structure IndexedMap (k : Type u) [Countable k] (v : Type w) where
  map : NatMap v
-- Operations, instances, and theorems straightforwardly deferred to `NatMap`

structure IndexedSet (α : Type u) [Countable α] where
  set : NatSet
-- Operations, instances, and theorems straightforwardly deferred to `NatSet`
```

# Micro benchmarks

Basic comparison of `NatSet` with Lean's standard `HashSet Nat` (🍎 to 🍊) and `PersistentHashSet Nat` to get some idea of the relative performance.
If either `HashSet` or `PersistentHashSet` doesn't have `union`, implement them using `fold`.

Pick a reasonable N (e.g. 1000000). Each domain below regenerates the same deterministic list every run:
- **sequential**: `0 … N-1`
- **shuffled**: a fixed shuffle of `[0 … N-1]` (so values stay "relatively small")
- **random**: `N` values in `[0, 2^63)`

For each domain, measure each operation, printing a final size/sum as a cross-check:
- "insertion": build the set from the value list (report its size)
- "lookup": sum the elements found over the list (report the sum)
- "union": turn the values into singletons, then union consecutive sets until one remains (report its size)
- "subset": build two equal sets from the values, then check `s ⊆ t` — always true, so every element is traversed (report 1/0). `HashSet`/`PersistentHashSet` lack `subset`; synthesize it from `all`/`fold` + `contains`.

Be careful not to measure the time it takes to set up the data (e.g. the initial list).

Measure both the time (in ms) and memory use (in KB) of each set.

Table at the end: colums for the data structure, rows for the benchmarks.

# Verified path-compression results

The core representation was migrated from a height-indexed GADT trie (height tied to the largest key, so a sparse key built a chain of single-child nodes) to the height-erased path-compressed `PTree` above — preserving every theorem statement on `NatSet`/`NatMap` byte-for-byte. Re-measuring the verified `NatSet` against the old height-indexed one (`N = 1,000,000`, ΔRSS for memory):

| domain | op | old | new | change |
|--------|----|-----|-----|--------|
| random `[0,2⁶³)` | insert | 689 ms | 451 ms | **1.5× faster** |
| | lookup | 1128 ms | 411 ms | **2.7× faster** |
| | union | 1141 ms | 822 ms | **1.4× faster** |
| | subset | 2216 ms | 237 ms | **9.4× faster** |
| | insert memory | 462 MB | 77 MB | **6.0× less** |
| sequential | union | 133 ms | 28 ms | **4.7× faster** |
| shuffled (dense) | insert | 144 ms | 154 ms | +7% (accepted) |
| | union | 419 ms | 467 ms | +12% time, +58% peak mem (accepted) |

Decisive wins on the sparse/large-key domain in both time and memory; the only regressions are on dense keys (shuffled insert/union), pre-accepted as the cost of path compression. (The verified `union` is ~1.5–2× slower than an unverified `partial def` Patricia prototype — the gap is the total, canonical, proof-shaped merge code — but still faster than the old height-indexed `union`.)

# Future improvements
- Memory use and locality. It's still 2 hops to the next level: each `bin` keeps a pointer to the array of pointers to children. If dependent arrays didn't require `unsafe`, we would have used those.
- `union` throughput. The verified merge (`unionU`/`mergeKids`) rebuilds child arrays in a proof-friendly shape; a tighter in-place merge would close the gap to the prototype, at the cost of harder termination/WF proofs.
