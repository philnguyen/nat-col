import NatCol.Node

/-!
# The height-indexed trie and its generic operations

`Tree leaf h` is a uniform 32-ary trie of height `h`: a tree of height 0 is a single
`leaf`, and a tree of height `h+1` is a `Node` of height-`h` subtrees. A key's 5-bit
chunk at level `j` selects the slot at the node of height `j`, so a tree of height `h`
stores exactly the keys `< 32^(h+1)`.

All operations are written once here, generically over the leaf via `LeafOps L V`, where
`V` is the value type a leaf maps slot indices to (`Unit` for sets, `α` for maps). The
instances live in `NatCol/Set.lean` and `NatCol/Map.lean`.

Height is an explicit argument so the recursions (several of which recurse *through*
`Array.foldl` / `Node.join` closures) terminate on it. Binary operations on two trees
of different heights are handled at the `NatCollection` level by lifting the shorter one
(`liftBy`/`cast`) to the common height.
-/

namespace NatCol

/-- A uniform 32-ary trie of the given height. -/
abbrev Tree (leaf : Type u) : Nat → Type u
  | 0 => leaf
  | n + 1 => Node (Tree leaf n)

/-- A leaf collection: maps 5-bit slot indices to values of type `V`. This is the single
seam that distinguishes sets (`UInt32` leaves, `V = Unit`) from maps (`Node α` leaves,
`V = α`); everything else is shared. -/
class LeafOps (L : Type u) (V : outParam (Type u)) where
  empty     : L
  isEmpty   : L → Bool
  size      : L → Nat
  get?      : L → UInt32 → Option V
  insert    : L → UInt32 → V → L
  erase     : L → UInt32 → L
  modify    : L → UInt32 → (V → V) → L
  join      : (V → V → V) → L → L → L
  meet      : (V → V → V) → L → L → L
  restricts : (V → V → Bool) → L → L → Bool
  /-- Present `(slot, value)` pairs in ascending slot order. -/
  toArray   : L → Array (UInt32 × V)
  /-- Inserting a value yields a non-empty leaf, so freshly-built subtrees are never empty.
  Part of the canonical-shape invariant (`Tree.Full`). -/
  insert_ne_empty : ∀ (l : L) (i : UInt32) (v : V), isEmpty (insert l i v) = false
  /-- Modifying a value never changes whether a leaf is empty (it touches values, not
  presence), so `modify` preserves canonical shape. -/
  isEmpty_modify : ∀ (l : L) (i : UInt32) (g : V → V), isEmpty (modify l i g) = isEmpty l
  /-- The empty leaf reads as empty. Lets the collection layer prove `empty.isEmpty = true`,
  which the lattice identities (e.g. left identity of `join`) bottom out in. -/
  isEmpty_empty : isEmpty (empty : L) = true
  /-- An empty leaf *is* the empty leaf (the canonical converse of `isEmpty_empty`). Lets the
  collection layer recover `c = empty` from `c.isEmpty = true` at height 0, which the right
  identity of `join` (`join a empty = a`) bottoms out in. -/
  eq_empty_of_isEmpty : ∀ (l : L), isEmpty l = true → l = empty
  /-- `restricts` is reflexive on a leaf when `rel` is reflexive on values: a leaf's keys are
  trivially a subset of its own, and `rel` holds on every coinciding value. Lets the collection
  layer prove reflexivity of `restricts`. -/
  restricts_refl : ∀ (rel : V → V → Bool), (∀ x, rel x x = true) →
    ∀ (l : L), restricts rel l l = true

namespace Tree

variable {L : Type u} {V : Type u} [LeafOps L V]

/-- The empty tree of a given height. -/
def empty : (h : Nat) → Tree L h
  | 0 => LeafOps.empty
  | _ + 1 => Node.empty

/-- Is the tree empty? (For canonical trees only the leaf or the top node can be empty.) -/
def isEmpty : (h : Nat) → Tree L h → Bool
  | 0, l => LeafOps.isEmpty l
  | _ + 1, n => Node.isEmpty n

/-- Number of keys present. -/
def size : (h : Nat) → Tree L h → Nat
  | 0, l => LeafOps.size l
  | h + 1, n => n.elements.foldl (fun acc c => acc + size h c) 0
termination_by h => h

/-- Look up the value at key `k`. -/
def get? (k : Nat) : (h : Nat) → Tree L h → Option V
  | 0, l => LeafOps.get? l (chunk k 0)
  | h + 1, n =>
    match Node.get? n (chunk k (h + 1)) with
    | some child => get? k h child
    | none => none
termination_by h => h

/-- A tree of the given height holding the single key `k` ↦ `v`. -/
def singleton (k : Nat) (v : V) : (h : Nat) → Tree L h
  | 0 => LeafOps.insert LeafOps.empty (chunk k 0) v
  | h + 1 => Node.singleton (chunk k (h + 1)) (singleton k v h)
termination_by h => h

/-- Insert / overwrite key `k` ↦ `v`. Assumes `h` is large enough to hold `k`
(the `NatCollection` layer grows the height first when needed). -/
def insert (k : Nat) (v : V) : (h : Nat) → Tree L h → Tree L h
  | 0, l => LeafOps.insert l (chunk k 0) v
  | h + 1, n => n.alter (chunk k (h + 1)) fun
      | some child => some (insert k v h child)
      | none => some (singleton k v h)
termination_by h => h

/-- Erase key `k`, pruning subtrees that become empty (keeps the tree canonical below
the top level). -/
def erase (k : Nat) : (h : Nat) → Tree L h → Tree L h
  | 0, l => LeafOps.erase l (chunk k 0)
  | h + 1, n => n.alter (chunk k (h + 1)) fun
      | some child =>
        let c := erase k h child
        if isEmpty h c then none else some c
      | none => none
termination_by h => h

/-- Apply `f` to the value at key `k`, if present. -/
def modify (k : Nat) (f : V → V) : (h : Nat) → Tree L h → Tree L h
  | 0, l => LeafOps.modify l (chunk k 0) f
  | h + 1, n => n.alter (chunk k (h + 1)) fun
      | some child => some (modify k f h child)
      | none => none
termination_by h => h

/-- Lift a tree up by `d` levels (wrapping it under slot 0). Cast-free: the result type
`Tree L (h + d)` lines up definitionally because `h + (d+1)` reduces to `(h + d) + 1`. -/
def liftBy : (d : Nat) → {h : Nat} → Tree L h → Tree L (h + d)
  | 0, _, t => t
  | _ + 1, _, t => Node.singleton 0 (liftBy _ t)

/-- Transport a tree along a proof of equal heights (compiles to the identity). -/
def cast {ha hb : Nat} (h : ha = hb) (t : Tree L ha) : Tree L hb := h ▸ t

/-- Union of two equal-height trees. Children present on only one side are reused by
`Node.join` without recursion; shared children are merged recursively, combining leaf
values with `c`.

The recursive merge is guarded by `if isEmpty … then none`, exactly like `meetEq`. For
canonical (non-empty) children this guard never fires — a union is never empty — so it does
not change behavior, but it makes "no empty subtree" (`Tree.Full`) hold by construction:
every surviving merged child is provably non-empty. -/
def joinEq (c : V → V → V) : (h : Nat) → Tree L h → Tree L h → Tree L h
  | 0, a, b => LeafOps.join c a b
  | h + 1, a, b => Node.join (fun x y =>
      let t := joinEq c h x y
      if isEmpty h t then none else some t) a b
termination_by h => h

/-- Intersection of two equal-height trees. Children present on only one side are dropped
by `Node.meet`; shared subtrees are intersected recursively and pruned if they become
empty. -/
def meetEq (c : V → V → V) : (h : Nat) → Tree L h → Tree L h → Tree L h
  | 0, a, b => LeafOps.meet c a b
  | h + 1, a, b => Node.meet (fun x y =>
      let t := meetEq c h x y
      if isEmpty h t then none else some t) a b
termination_by h => h

/-- `a` restricts `b` (equal heights): `a`'s keys are a subset of `b`'s and `rel` holds
on every coinciding value. -/
def restrictsEq (rel : V → V → Bool) : (h : Nat) → Tree L h → Tree L h → Bool
  | 0, a, b => LeafOps.restricts rel a b
  | h + 1, a, b => Node.restricts (fun x y => restrictsEq rel h x y) a b
termination_by h => h

/-! ### Operating a shorter tree against a taller one without lifting

A canonical tree of height `h + d` holds the keys it shares with a height-`h` tree only on its
**slot-0 spine** (`d` levels of slot-0 children); everything off that spine lies outside the
shorter tree's key range. So a binary operation between a shorter tree `s : Tree L h` and a
taller `t : Tree L (h + d)` only needs to touch `t`'s spine — no lift of `s` to the taller
height. These are the spine analogues of the equal-height kernels above. -/

/-- Union of a shorter `s` (height `h`) with a taller `t` (height `h + d`): descend `t`'s slot-0
spine to height `h`, `joinEq` there, and plug the result back in; off-spine children of `t` are
reused untouched. The `combine` order is `c (s-value) (t-value)`. The `if isEmpty` guard makes
"no empty subtree" hold by construction, exactly as in `joinEq`. -/
def joinSpine (c : V → V → V) (h : Nat) : (d : Nat) → Tree L h → Tree L (h + d) → Tree L (h + d)
  | 0, s, t => joinEq c h s t
  | d + 1, s, t => t.alter 0 fun
      | some child =>
          let r := joinSpine c h d s child
          if isEmpty (h + d) r then none else some r
      | none => some (liftBy d s)
termination_by d => d

/-- Intersection of a shorter `s` (height `h`) with a taller `t` (height `h + d`): only keys on
`t`'s slot-0 spine can be shared, so descend to height `h` and `meetEq` there, discarding all
off-spine structure of `t`. The result lives at the *smaller* height `h`. -/
def meetSpine (c : V → V → V) (h : Nat) : (d : Nat) → Tree L h → Tree L (h + d) → Tree L h
  | 0, s, t => meetEq c h s t
  | d + 1, s, t =>
      match Node.get? t 0 with
      | some child => meetSpine c h d s child
      | none => Tree.empty h
termination_by d => d

/-- `a` (height `h`) restricts a taller `b` (height `h + d`): `a`'s keys can only match on `b`'s
slot-0 spine, so descend to height `h` and `restrictsEq` there; `b`'s off-spine children are
irrelevant. If the spine runs out (`none`), `b` has no key in `a`'s range, so `a ⊆ b` iff `a` is
empty. -/
def restrictsSpine (rel : V → V → Bool) (h : Nat) : (d : Nat) → Tree L h → Tree L (h + d) → Bool
  | 0, a, b => restrictsEq rel h a b
  | d + 1, a, b =>
      match Node.get? b 0 with
      | some child => restrictsSpine rel h d a child
      | none => Tree.isEmpty h a
termination_by d => d

/-- Structural equality at a fixed height. For canonical trees this coincides with
logical equality. -/
def beq [BEq L] : (h : Nat) → Tree L h → Tree L h → Bool
  | 0, a, b => a == b
  | h + 1, a, b => a.positionsMask == b.positionsMask && a.elements.isEqv b.elements (beq h)
termination_by h => h

/-- `beq` is reflexive at every height (given a reflexive leaf `BEq`). -/
theorem beq_refl [BEq L] [LawfulBEq L] : (h : Nat) → (t : Tree L h) → beq h t t = true := by
  intro h
  induction h with
  | zero => intro t; simp only [beq]; exact BEq.rfl
  | succ h ih =>
    intro t
    obtain ⟨m, e, _⟩ := t
    simp only [beq, Bool.and_eq_true]
    refine ⟨BEq.rfl, ?_⟩
    rw [Array.isEqv_iff_rel]
    exact ⟨rfl, fun i _ => ih e[i]⟩

/-- `beq` decides propositional equality: structurally-equal trees are equal. (This is the
heart of `LawfulBEq (NatCollection L)`; it holds for *any* tree, canonical or not.) -/
theorem eq_of_beq [BEq L] [LawfulBEq L] :
    (h : Nat) → {a b : Tree L h} → beq h a b = true → a = b := by
  intro h
  induction h with
  | zero => intro a b hb; simp only [beq] at hb; exact LawfulBEq.eq_of_beq hb
  | succ h ih =>
    intro a b hb
    obtain ⟨ma, ea, ha⟩ := a
    obtain ⟨mb, eb, hb'⟩ := b
    simp only [beq, Bool.and_eq_true] at hb
    obtain ⟨hm, he⟩ := hb
    rw [Array.isEqv_iff_rel] at he
    obtain ⟨hsize, hpt⟩ := he
    have hmeq : ma = mb := LawfulBEq.eq_of_beq hm
    have heeq : ea = eb := Array.ext hsize (fun i hi₁ _ => ih (hpt i hi₁))
    subst hmeq; subst heeq; rfl

/-- `restrictsEq` is reflexive when `rel` is reflexive on values: a tree's keys are a subset of
its own and `rel` holds on every coinciding value, at every height. Needs no canonical-shape
hypothesis — both operands are the same tree. Bottoms out in `LeafOps.restricts_refl` at a leaf
and `Node.restricts_self` at each node. -/
theorem restrictsEq_self (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) :
    (h : Nat) → (t : Tree L h) → restrictsEq rel h t t = true := by
  intro h
  induction h with
  | zero => intro l; simp only [restrictsEq]; exact LeafOps.restricts_refl rel hrefl l
  | succ h ih =>
    intro n
    simp only [restrictsEq]
    exact Node.restricts_self _ n (fun c _ => ih c)

/-- Collect `(key, value)` pairs into `acc`, ascending by key. `pfx` carries the key bits
fixed by higher levels. -/
def toArrayAux (pfx : Nat) : (h : Nat) → Tree L h → Array (Nat × V) → Array (Nat × V)
  | 0, l, acc => (LeafOps.toArray l).foldl (fun acc (i, v) => acc.push (pfx ||| i.toNat, v)) acc
  | h + 1, n, acc =>
    n.foldl (fun acc i child => toArrayAux (pfx ||| (i.toNat <<< (5 * (h + 1)))) h child acc) acc
termination_by h => h

/-- All `(key, value)` pairs, ascending by key. -/
def toArray (h : Nat) (t : Tree L h) : Array (Nat × V) := toArrayAux 0 h t #[]

/-! ### Canonical shape

`Full` is "no empty subtree": every present child, at every level, is non-empty. `TopProper`
is "no excessive height": the top node has a slot above slot 0 set (`2 ≤ positionsMask`), so
the height is minimal. Their conjunction `Canonical` is the invariant the `NatCollection`
layer carries as a proof field. Each lemma below shows one operation preserves or establishes
the relevant piece; the collection layer assembles them. -/

/-- No empty subtree: every present child, recursively, is non-empty. (Vacuous at a leaf —
a leaf's own emptiness is governed at the collection's top, not here.) -/
def Full : (h : Nat) → Tree L h → Prop
  | 0, _ => True
  | h + 1, n => ∀ c ∈ n.elements, Tree.isEmpty h c = false ∧ Full h c

/-- Height-minimal at the top: the top node has a slot ≥ 1 set, so the height cannot be
lowered. (Vacuous at a leaf.) -/
def TopProper : (h : Nat) → Tree L h → Prop
  | 0, _ => True
  | _ + 1, n => 2 ≤ n.positionsMask

/-- A canonical tree: no empty subtree and minimal height. -/
def Canonical (h : Nat) (t : Tree L h) : Prop := Full h t ∧ TopProper h t

/-- The empty tree has no subtrees, so it is `Full`. -/
theorem Full_empty : (h : Nat) → Full h (Tree.empty h : Tree L h)
  | 0 => trivial
  | _ + 1 => by intro c hc; simp [Tree.empty, Node.empty] at hc

/-- A singleton tree is non-empty at every height. -/
private theorem isEmpty_singleton : (h : Nat) → (k : Nat) → (v : V) →
    Tree.isEmpty h (Tree.singleton k v h : Tree L h) = false
  | 0, _, _ => by simp only [Tree.isEmpty, Tree.singleton]; exact LeafOps.insert_ne_empty _ _ _
  | _ + 1, _, _ => by simp only [Tree.isEmpty, Tree.singleton]; exact Node.isEmpty_singleton _ _

/-- A singleton tree has no empty subtree. -/
theorem Full_singleton : (h : Nat) → (k : Nat) → (v : V) → Full h (Tree.singleton k v h : Tree L h)
  | 0, _, _ => trivial
  | h + 1, k, v => by
      intro c hc
      simp only [Tree.singleton, Node.singleton, Array.mem_singleton] at hc
      subst hc
      exact ⟨isEmpty_singleton h k v, Full_singleton h k v⟩

/-- An `insert` result is never empty (it adds a key). -/
private theorem isEmpty_insert : (h : Nat) → (k : Nat) → (v : V) → (t : Tree L h) →
    Tree.isEmpty h (Tree.insert k v h t) = false
  | 0, _, _, _ => by simp only [Tree.isEmpty, Tree.insert]; exact LeafOps.insert_ne_empty _ _ _
  | h + 1, k, v, n => by
      simp only [Tree.isEmpty, Tree.insert, Node.isEmpty]
      rw [Node.positionsMask_alter_of_isSome n (chunk k (h + 1)) _
            (by cases Node.get? n (chunk k (h + 1)) <;> rfl)]
      exact beq_eq_false_iff_ne.mpr (setBit_ne_zero _ _)

/-- `insert` preserves "no empty subtree". -/
theorem Full_insert : (h : Nat) → (k : Nat) → (v : V) → (t : Tree L h) →
    Full h t → Full h (Tree.insert k v h t)
  | 0, _, _, _, _ => trivial
  | h + 1, k, v, n, hn => by
      intro c hc
      simp only [Tree.insert] at hc
      rcases Node.mem_alter n (chunk k (h + 1)) _ c hc with hmem | ⟨a, hfa, hca⟩
      · exact hn c hmem
      · subst hca
        cases hget : Node.get? n (chunk k (h + 1)) with
        | some child =>
          rw [hget] at hfa; simp only [Option.some.injEq] at hfa; subst hfa
          have hchild : Full h child := (hn child (Node.mem_of_get? n _ child hget)).2
          exact ⟨isEmpty_insert h k v child, Full_insert h k v child hchild⟩
        | none =>
          rw [hget] at hfa; simp only [Option.some.injEq] at hfa; subst hfa
          exact ⟨isEmpty_singleton h k v, Full_singleton h k v⟩

/-- `erase` preserves "no empty subtree" (it prunes any child that becomes empty). -/
theorem Full_erase : (h : Nat) → (k : Nat) → (t : Tree L h) →
    Full h t → Full h (Tree.erase k h t)
  | 0, _, _, _ => trivial
  | h + 1, k, n, hn => by
      intro c hc
      simp only [Tree.erase] at hc
      rcases Node.mem_alter n (chunk k (h + 1)) _ c hc with hmem | ⟨a, hfa, hca⟩
      · exact hn c hmem
      · subst hca
        cases hget : Node.get? n (chunk k (h + 1)) with
        | some child =>
          rw [hget] at hfa; simp only at hfa
          have hchild : Full h child := (hn child (Node.mem_of_get? n _ child hget)).2
          split at hfa
          · simp at hfa
          · rename_i hne
            simp only [Option.some.injEq] at hfa; subst hfa
            exact ⟨by simpa using hne, Full_erase h k child hchild⟩
        | none =>
          rw [hget] at hfa; simp at hfa

/-- `joinEq` preserves "no empty subtree": every merged child is guarded non-empty. -/
theorem Full_joinEq : (h : Nat) → (c : V → V → V) → (a b : Tree L h) →
    Full h a → Full h b → Full h (joinEq c h a b)
  | 0, _, _, _, _, _ => trivial
  | h + 1, c, a, b, ha, hb => by
      simp only [joinEq]
      refine Node.join_forall (fun x hx => ha x hx) (fun y hy => hb y hy) ?_
      intro x hx y hy v hv
      simp only at hv
      split at hv
      · simp at hv
      · rename_i hne
        simp only [Option.some.injEq] at hv; subst hv
        exact ⟨by simpa using hne, Full_joinEq h c x y (ha x hx).2 (hb y hy).2⟩

/-- `meetEq` preserves "no empty subtree": every surviving child is guarded non-empty. -/
theorem Full_meetEq : (h : Nat) → (c : V → V → V) → (a b : Tree L h) →
    Full h a → Full h b → Full h (meetEq c h a b)
  | 0, _, _, _, _, _ => trivial
  | h + 1, c, a, b, ha, hb => by
      simp only [meetEq]
      refine Node.meet_forall ?_
      intro x hx y hy v hv
      simp only at hv
      split at hv
      · simp at hv
      · rename_i hne
        simp only [Option.some.injEq] at hv; subst hv
        exact ⟨by simpa using hne, Full_meetEq h c x y (ha x hx).2 (hb y hy).2⟩

/-- Lifting a non-empty tree keeps it non-empty. -/
private theorem isEmpty_liftBy : (d : Nat) → {h : Nat} → (t : Tree L h) →
    Tree.isEmpty h t = false → Tree.isEmpty (h + d) (liftBy d t) = false
  | 0, _, _, ht => ht
  | d + 1, _, t, _ => Node.isEmpty_singleton 0 (liftBy d t)

/-- Lifting a non-empty `Full` tree keeps it `Full` (the new slot-0 children are non-empty
copies of the original). -/
theorem Full_liftBy : (d : Nat) → {h : Nat} → (t : Tree L h) →
    Full h t → Tree.isEmpty h t = false → Full (h + d) (liftBy d t)
  | 0, _, _, hf, _ => hf
  | d + 1, _, t, hf, hne => by
      intro c hc
      simp only [liftBy, Node.singleton, Array.mem_singleton] at hc
      subst hc
      exact ⟨isEmpty_liftBy d t hne, Full_liftBy d t hf hne⟩

/-- Transporting a tree along an equality of heights preserves `Full`. -/
theorem Full_cast {ha hb : Nat} (heq : ha = hb) (t : Tree L ha) (hf : Full ha t) :
    Full hb (Tree.cast heq t) := by subst heq; exact hf

/-- `joinSpine` preserves "no empty subtree": the spine's merged child is guarded non-empty
(`some` branch) or is a lifted copy of the non-empty `s` (`none` branch); off-spine children
come straight from the `Full` taller tree. Requires `s` non-empty (its lift must stay `Full`). -/
theorem Full_joinSpine (c : V → V → V) (h : Nat) : (d : Nat) → (s : Tree L h) → (t : Tree L (h + d)) →
    Tree.isEmpty h s = false → Full h s → Full (h + d) t → Full (h + d) (joinSpine c h d s t)
  | 0, s, t, _, hs, ht => by simp only [joinSpine, Nat.add_zero]; exact Full_joinEq h c s t hs ht
  | d + 1, s, t, hsne, hs, ht => by
      simp only [joinSpine]
      intro x hx
      rcases Node.mem_alter t 0 _ x hx with hmem | ⟨a, hfa, hxa⟩
      · exact ht x hmem
      · subst hxa
        cases hget : Node.get? t 0 with
        | some child =>
            rw [hget] at hfa
            simp only at hfa
            split at hfa
            · simp at hfa
            · rename_i hne
              simp only [Option.some.injEq] at hfa; subst hfa
              have hchild : Full (h + d) child := (ht child (Node.mem_of_get? t 0 child hget)).2
              exact ⟨by simpa using hne, Full_joinSpine c h d s child hsne hs hchild⟩
        | none =>
            rw [hget] at hfa
            simp only [Option.some.injEq] at hfa; subst hfa
            exact ⟨isEmpty_liftBy d s hsne, Full_liftBy d s hs hsne⟩

/-- `meetSpine` preserves "no empty subtree": each step recurses into a `Full` spine child or
returns the empty tree (`Full_empty`); the base case is `meetEq`. -/
theorem Full_meetSpine (c : V → V → V) (h : Nat) : (d : Nat) → (s : Tree L h) → (t : Tree L (h + d)) →
    Full h s → Full (h + d) t → Full h (meetSpine c h d s t)
  | 0, s, t, hs, ht => by simp only [meetSpine]; exact Full_meetEq h c s t hs ht
  | d + 1, s, t, hs, ht => by
      simp only [meetSpine]
      split
      · rename_i child hget
        have hchild : Full (h + d) child := (ht child (Node.mem_of_get? t 0 child hget)).2
        exact Full_meetSpine c h d s child hs hchild
      · exact Full_empty h

/-- `modify` never empties a leaf, so it preserves emptiness at every height. -/
private theorem isEmpty_modify : (h : Nat) → (k : Nat) → (f : V → V) → (t : Tree L h) →
    Tree.isEmpty h (Tree.modify k f h t) = Tree.isEmpty h t
  | 0, _, _, _ => by simp only [Tree.isEmpty, Tree.modify]; exact LeafOps.isEmpty_modify _ _ _
  | h + 1, k, f, n => by
      simp only [Tree.isEmpty, Tree.modify]
      exact Node.isEmpty_alter_invariant n (chunk k (h + 1)) _ (by intro o; cases o <;> rfl)

/-- `modify` preserves "no empty subtree" (it changes values, not structure). -/
theorem Full_modify : (h : Nat) → (k : Nat) → (f : V → V) → (t : Tree L h) →
    Full h t → Full h (Tree.modify k f h t)
  | 0, _, _, _, _ => trivial
  | h + 1, k, f, n, hn => by
      intro c hc
      simp only [Tree.modify] at hc
      rcases Node.mem_alter n (chunk k (h + 1)) _ c hc with hmem | ⟨a, hfa, hca⟩
      · exact hn c hmem
      · subst hca
        cases hget : Node.get? n (chunk k (h + 1)) with
        | some child =>
          rw [hget] at hfa; simp only [Option.some.injEq] at hfa; subst hfa
          have hchild := hn child (Node.mem_of_get? n _ child hget)
          refine ⟨?_, Full_modify h k f child hchild.2⟩
          rw [isEmpty_modify h k f child]; exact hchild.1
        | none =>
          rw [hget] at hfa; simp at hfa

end Tree

end NatCol
