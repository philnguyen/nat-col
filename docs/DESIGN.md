# Overview

This project implements maps and sets on `Nat` with efficient lattice operations (e.g. `join`, `meet`, and `restricts`). It is inspired by HAMT, except there's no hashing, and the keys/elements aren't literally stored.

At the heart of `NatMap` and `NatSet` is a 32-ary trie (à la HAMT), something like below:
```lean
private structure Node (α : Type u) where
  positionsMask    : UInt32
  elements         : Array α
  elements_compact : elements.size = indices.countBits

private abbrev Tree (leaf : Type u) : Nat → Type u
  | 0     => leaf
  | n + 1 => Node (Tree leaf n)
```

A `NatMap` is a `Tree` whose leaves are `Node`s of values, and a `NatSet` is a `Tree` whose leaves are `UInt32`. We're doing `UInt32` instead of `UInt64` because all polymorphic positions (e.g. array elements) will be Lean-boxed: `UInt64` will be allocated, while `UInt32` only bit-shifted.
```lean
structure NatCollection (leaf : Type u) where
  height : Nat
  tree : Tree leaf height

abbrev NatMap (α : Type u) : Type u := NatCollection (Node α)
abbrev NatSet : Type := NatCollection UInt32
```

The tree structure should be cannonical given the elements. For example, its height should only be large enough to accomodate the largest element. The structure indicates what keys are present. Structural equality is logical equality.

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

These operations should be implemented once generically on `NatCollection` or `Tree`, then instantiated appropriately for `NatMap` and `NatSet`.

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

These theorems should be stated and proven once generically for `NatCollection` or `Tree`, then instantiated appropriately for `NatMap` and `NatSet`.
