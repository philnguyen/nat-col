import NatCol.Tree

/-!
# `NatCollection`: the generic top-level API

A `NatCollection` pairs a trie with its (minimal) height. All operations are generic over
`[LeafOps L V]`; `NatMap`/`NatSet` are thin instantiations.

## Canonical form

A collection is *canonical* when its height is minimal for its largest key and it contains
no empty subtrees. Every operation here returns a canonical collection, so structural
equality (`beq`) coincides with logical equality.

Two facts drive the implementation:

* **Different heights ⇒ different contents.** A canonical collection's height is a function
  of its largest key, so `beq` can short-circuit to `false` when heights differ.
* **Lifting an empty tree would create junk.** `liftBy` wraps a tree under slot 0; doing
  that to an *empty* tree manufactures spurious empty subtrees. So binary operations and
  `insert` special-case empty operands instead of lifting them.
-/

namespace NatCol

/-- A trie together with its height, carrying a proof that it is in *canonical shape* —
no excessive height and no empty subtree (`Tree.Canonical`). Every operation below returns a
`NatCollection`, so the invariant holds throughout; that is what makes structural equality
(`beq`) coincide with logical equality. -/
structure NatCollection (L : Type u) {V : Type u} [LeafOps L V] where
  height : Nat
  tree : Tree L height
  wf : Tree.Canonical height tree

namespace NatCollection

variable {L : Type u} {V : Type u} [LeafOps L V]

/-- The empty collection. -/
def empty : NatCollection L := ⟨0, Tree.empty 0, ⟨Tree.Full_empty 0, trivial⟩⟩

def isEmpty (c : NatCollection L) : Bool := Tree.isEmpty c.height c.tree

def size (c : NatCollection L) : Nat := Tree.size c.height c.tree

/-- Lift a collection's tree up to a common height `H ≥ c.height`. -/
def liftTo (c : NatCollection L) (H : Nat) (le : c.height ≤ H) : Tree L H :=
  Tree.cast (by omega) (Tree.liftBy (H - c.height) c.tree)

/-- Lifting a non-empty canonical collection's tree keeps it `Full`. -/
private theorem Full_liftTo (c : NatCollection L) (H : Nat) (le : c.height ≤ H) (hne : c.isEmpty = false) :
    Tree.Full H (c.liftTo H le) :=
  Tree.Full_cast _ _ (Tree.Full_liftBy (H - c.height) c.tree c.wf.1 hne)

/-- Smart constructor: from any `Full` tree, build a *canonical* collection by lowering the
height while the top node is empty or holds only slot 0 (this is what restores minimal height
after `erase`/`meet`; for `insert`/`modify`/`join` results the top is already proper, so it is
the identity). The `Full` precondition is preserved as we descend, and the final top — being
neither `0` nor only-slot-`0` — is height-minimal (`TopProper`). -/
def normalizeAux : (h : Nat) → (t : Tree L h) → Tree.Full h t → NatCollection L
  | 0, t, hf => ⟨0, t, ⟨hf, trivial⟩⟩
  | h + 1, n, hf =>
    match hm0 : n.positionsMask == 0 with
    | true => normalizeAux h (Tree.empty h) (Tree.Full_empty h)
    | false =>
      match hm1 : n.positionsMask == 1 with
      | true =>
        -- mask is exactly `1`, so slot 0 is present; read its child totally via `Node.get`
        have h0 : testBit n.positionsMask 0 = true := by rw [eq_of_beq hm1]; decide
        normalizeAux h (n.get 0 h0) (hf _ (n.get_mem 0 h0)).2
      | false =>
        ⟨h + 1, n, ⟨hf, two_le_of_ne n.positionsMask (by simpa using hm0) (by simpa using hm1)⟩⟩
termination_by h => h

/-- Look up the value at key `k`. -/
def get? (c : NatCollection L) (k : Nat) : Option V :=
  if requiredHeight k > c.height then none else Tree.get? k c.height c.tree

/-- Is key `k` present? -/
def contains (c : NatCollection L) (k : Nat) : Bool := (c.get? k).isSome

/-- Insert / overwrite key `k` ↦ `v`, growing the height if `k` needs more chunks. -/
def insert (c : NatCollection L) (k : Nat) (v : V) : NatCollection L :=
  match hemp : c.isEmpty with
  | true =>
    normalizeAux (requiredHeight k) (Tree.singleton k v (requiredHeight k))
      (Tree.Full_singleton (requiredHeight k) k v)
  | false =>
    let H := max c.height (requiredHeight k)
    normalizeAux H (Tree.insert k v H (c.liftTo H (Nat.le_max_left _ _)))
      (Tree.Full_insert H k v _ (Full_liftTo c H (Nat.le_max_left _ _) hemp))

/-- Erase key `k`. -/
def erase (c : NatCollection L) (k : Nat) : NatCollection L :=
  if requiredHeight k > c.height then c
  else normalizeAux c.height (Tree.erase k c.height c.tree) (Tree.Full_erase c.height k c.tree c.wf.1)

/-- Apply `f` to the value at key `k`, if present. -/
def modify (c : NatCollection L) (k : Nat) (f : V → V) : NatCollection L :=
  if requiredHeight k > c.height then c
  else normalizeAux c.height (Tree.modify k f c.height c.tree) (Tree.Full_modify c.height k f c.tree c.wf.1)

/-- Union. Leaf values at coinciding keys are combined with `combine`. Rather than lift the
shorter tree up to the taller's height, descend the taller tree's slot-0 spine to the shorter
height, `joinSpine` there, and reuse all off-spine structure (see `Tree.joinSpine`). When the
*left* operand is the taller one, `combine` is flipped so the original `combine a-value b-value`
order is preserved. -/
def join (combine : V → V → V) (a b : NatCollection L) : NatCollection L :=
  if hae : a.isEmpty then b
  else if hbe : b.isEmpty then a
  else if hle : a.height ≤ b.height then
    normalizeAux _
      (Tree.joinSpine combine a.height (b.height - a.height) a.tree (Tree.cast (by omega) b.tree))
      (Tree.Full_joinSpine combine a.height (b.height - a.height) a.tree (Tree.cast (by omega) b.tree)
        (by simpa using hae) a.wf.1 (Tree.Full_cast (by omega) b.tree b.wf.1))
  else
    normalizeAux _
      (Tree.joinSpine (fun x y => combine y x) b.height (a.height - b.height) b.tree
        (Tree.cast (by omega) a.tree))
      (Tree.Full_joinSpine (fun x y => combine y x) b.height (a.height - b.height) b.tree
        (Tree.cast (by omega) a.tree) (by simpa using hbe) b.wf.1 (Tree.Full_cast (by omega) a.tree a.wf.1))

/-- Intersection. Leaf values at coinciding keys are combined with `combine`. Only keys on the
taller tree's slot-0 spine can be shared, so descend to the *smaller* height and `meetSpine`
there, discarding the taller tree's off-spine structure (see `Tree.meetSpine`). The result lives
at the smaller height; `normalizeAux` lowers it further as needed. When the *left* operand is the
taller one, `combine` is flipped so the original argument order is preserved. -/
def meet (combine : V → V → V) (a b : NatCollection L) : NatCollection L :=
  if a.isEmpty then empty
  else if b.isEmpty then empty
  else if hle : a.height ≤ b.height then
    normalizeAux a.height
      (Tree.meetSpine combine a.height (b.height - a.height) a.tree (Tree.cast (by omega) b.tree))
      (Tree.Full_meetSpine combine a.height (b.height - a.height) a.tree (Tree.cast (by omega) b.tree)
        a.wf.1 (Tree.Full_cast (by omega) b.tree b.wf.1))
  else
    normalizeAux b.height
      (Tree.meetSpine (fun x y => combine y x) b.height (a.height - b.height) b.tree
        (Tree.cast (by omega) a.tree))
      (Tree.Full_meetSpine (fun x y => combine y x) b.height (a.height - b.height) b.tree
        (Tree.cast (by omega) a.tree) b.wf.1 (Tree.Full_cast (by omega) a.tree a.wf.1))

/-- `a` restricts `b`: `a`'s keys are a subset of `b`'s, and `rel` holds on every value at
a coinciding key. When `b` is the taller tree, `a`'s keys can only match on `b`'s slot-0 spine,
so descend to `a`'s height and `restrictsSpine` there, ignoring `b`'s off-spine structure (see
`Tree.restrictsSpine`). When `a` is the taller one it has a key above `b`'s key range (it is
canonical, so `TopProper` forces an off-spine slot), hence cannot be a subset — answer `false`. -/
def restricts (rel : V → V → Bool) (a b : NatCollection L) : Bool :=
  if a.isEmpty then true
  else if b.isEmpty then false
  else if hle : a.height ≤ b.height then
    Tree.restrictsSpine rel a.height (b.height - a.height) a.tree (Tree.cast (by omega) b.tree)
  else
    false

/-- All `(key, value)` pairs, ascending by key. -/
def toList (c : NatCollection L) : List (Nat × V) := (Tree.toArray c.height c.tree).toList

/-- Build a collection from `(key, value)` pairs (later pairs win on duplicate keys). -/
def ofList (l : List (Nat × V)) : NatCollection L := l.foldl (fun c (k, v) => c.insert k v) empty

/-- Structural equality: equal heights and equal trees. Canonical ⇒ logical equality. -/
def beq [BEq L] (a b : NatCollection L) : Bool :=
  if h : a.height = b.height then Tree.beq a.height a.tree (Tree.cast h.symm b.tree) else false

instance [BEq L] : BEq (NatCollection L) := ⟨beq⟩

/-- Hash a collection by its `(key, value)` list. The list is derived structurally, so
`BEq`-equal collections hash equally; since the list is also sorted and canonical, the hash
agrees with logical equality too. -/
instance [Hashable V] : Hashable (NatCollection L) := ⟨fun c => hash c.toList⟩

/-- `beq` decides propositional equality, so the structural `BEq` is lawful. With this,
`LawfulHashable (NatCollection L)` follows automatically from the core
`[LawfulBEq] → [LawfulHashable]` instance. -/
instance [BEq L] [LawfulBEq L] : LawfulBEq (NatCollection L) where
  eq_of_beq {a b} hb := by
    have hb' : NatCollection.beq a b = true := hb
    unfold NatCollection.beq at hb'
    split at hb'
    · rename_i hh
      obtain ⟨ha, ta, wa⟩ := a
      obtain ⟨hbh, tb, wb⟩ := b
      dsimp only at hh hb'
      subst hh
      have htt : ta = tb := Tree.eq_of_beq _ hb'
      subst htt
      rfl
    · exact absurd hb' (by simp)
  rfl {a} := by
    show NatCollection.beq a a = true
    unfold NatCollection.beq
    rw [dif_pos (rfl : a.height = a.height)]
    exact Tree.beq_refl a.height a.tree

/-- Decidable propositional equality, built from the lawful `BEq` (so it agrees with the
`==` test and, via canonical form, with logical equality). -/
instance [BEq L] [LawfulBEq L] : DecidableEq (NatCollection L) := _root_.instDecidableEqOfLawfulBEq

/-! ## Lattice laws -/

/-- The empty collection is recognized as empty (lifts the leaf law `LeafOps.isEmpty_empty`
through `Tree.isEmpty 0 (Tree.empty 0)`). -/
@[simp, grind =]
theorem isEmpty_empty : (empty : NatCollection L).isEmpty = true := LeafOps.isEmpty_empty

/-- The empty collection is a left identity of `join`: `join` returns its right operand
verbatim once the left is empty, and `empty` is empty by `isEmpty_empty`. -/
@[simp, grind =]
theorem join_empty_left (combine : V → V → V) (b : NatCollection L) :
    join combine empty b = b := by
  unfold join
  split
  · rfl
  · rename_i h; rw [isEmpty_empty] at h; exact absurd h (by decide)

/-- An empty collection is *the* empty collection. At height ≥ 1 the canonical-shape field
`TopProper` forces a slot above slot 0 to be set (`2 ≤ positionsMask`), so an empty collection
must have height 0, where its leaf is the empty leaf by `LeafOps.eq_empty_of_isEmpty`. -/
theorem eq_empty_of_isEmpty (c : NatCollection L) (hc : c.isEmpty = true) : c = empty := by
  obtain ⟨height, tree, wf⟩ := c
  cases height with
  | zero =>
    have htree : tree = LeafOps.empty := LeafOps.eq_empty_of_isEmpty tree hc
    subst htree; rfl
  | succ h =>
    exfalso
    have hmask : tree.positionsMask = 0 := eq_of_beq hc
    have htop : 2 ≤ tree.positionsMask := wf.2
    rw [hmask] at htop
    exact absurd htop (by decide)

/-- The empty collection is a right identity of `join`. Unlike the left identity this is not
verbatim: when `a` is empty `join` returns `empty`, which equals `a` only because an empty
collection *is* `empty` (`eq_empty_of_isEmpty`); otherwise the second branch returns `a` since
`empty.isEmpty = true`. -/
@[simp, grind =]
theorem join_empty_right (combine : V → V → V) (a : NatCollection L) :
    join combine a empty = a := by
  unfold join
  split
  · rename_i h; exact (eq_empty_of_isEmpty a h).symm
  · split
    · rfl
    · rename_i h; rw [isEmpty_empty] at h; exact absurd h (by decide)

/-- The empty collection is a left annihilator of `meet`. Like the left identity of `join` (and
unlike its right identity) this is verbatim: `meet`'s first branch fires once the left operand is
empty (`isEmpty_empty`) and returns `empty` — no new leaf law required. -/
@[simp, grind =]
theorem meet_empty_left (combine : V → V → V) (b : NatCollection L) :
    meet combine empty b = empty := by
  unfold meet
  rw [if_pos isEmpty_empty]

/-- The empty collection is a right annihilator of `meet`. Like the left annihilator (and unlike
the right *identity* of `join`) this is verbatim: when the left operand is empty the first branch
returns `empty`; otherwise the second branch fires, since the right operand is empty
(`isEmpty_empty`), and also returns `empty`. No new leaf law required. -/
@[simp, grind =]
theorem meet_empty_right (combine : V → V → V) (a : NatCollection L) :
    meet combine a empty = empty := by
  unfold meet
  split <;> first | rfl | rw [if_pos isEmpty_empty]

/-- The empty collection restricts every collection. Like the left annihilator of `meet` this is
verbatim: `restricts`'s first branch fires once the left operand is empty (`isEmpty_empty`) and
returns `true` — the empty collection's keys are vacuously a subset of any other's, and `rel`
holds vacuously. No new leaf law required. -/
@[simp, grind =]
theorem restricts_empty_left (rel : V → V → Bool) (b : NatCollection L) :
    restricts rel empty b = true := by
  unfold restricts
  rw [if_pos isEmpty_empty]

/-- `restricts` is reflexive when `rel` is reflexive on values. If `a` is empty the first branch
returns `true`; otherwise the two emptiness guards fail and the `a.height ≤ a.height` branch fires
with height difference `a.height - a.height = 0`, so `restrictsSpine` reduces to `restrictsEq` on
`a.tree` against itself (the `Tree.cast` along `a.height = a.height + 0` is the identity), where
`Tree.restrictsEq_self` applies. -/
theorem restricts_refl (rel : V → V → Bool) (hrefl : ∀ x, rel x x = true) (a : NatCollection L) :
    restricts rel a a = true := by
  unfold restricts
  by_cases hemp : a.isEmpty = true
  · rw [if_pos hemp]
  · rw [if_neg hemp, if_neg hemp, dif_pos (Nat.le_refl a.height)]
    -- the height difference is `0`; generalize it to `subst` away the dependent `Tree.cast`
    suffices h : ∀ (d : Nat) (pf : a.height = a.height + d), d = 0 →
        Tree.restrictsSpine rel a.height d a.tree (Tree.cast pf a.tree) = true from
      h (a.height - a.height) (by omega) (Nat.sub_self _)
    intro d pf hd
    subst hd
    simp only [Tree.restrictsSpine]
    exact Tree.restrictsEq_self rel hrefl a.height a.tree

/-- `normalizeAux` depends on its tree only up to equality — the `Full` proof is irrelevant — so
equal trees normalize to equal collections. Backs `join_comm`'s equal-height case, where the two
sides build the *same* tree by different (flipped) recursions. -/
private theorem normalizeAux_congr {h : Nat} {t₁ t₂ : Tree L h} (heq : t₁ = t₂)
    (hf₁ : Tree.Full h t₁) (hf₂ : Tree.Full h t₂) :
    normalizeAux h t₁ hf₁ = normalizeAux h t₂ hf₂ := by
  subst heq; rfl

/-- `join` commutes when the combine is flipped: `join combine a b = join (fun x y => combine y x) b a`.
The empty short-circuits line up directly (two empty operands are both `empty`); when the heights
differ both sides descend the *same* (taller) tree's spine — the double flip cancels by η, so they
are definitionally equal; at equal heights both reduce to a `joinEq` with `d = 0`, related by
`Tree.joinEq_comm`. -/
theorem join_comm (combine : V → V → V) (a b : NatCollection L) :
    join combine a b = join (fun x y => combine y x) b a := by
  unfold join
  by_cases hae : a.isEmpty = true
  · rw [dif_pos hae]
    by_cases hbe : b.isEmpty = true
    · -- both empty: each operand is `empty`
      rw [dif_pos hbe, eq_empty_of_isEmpty a hae, eq_empty_of_isEmpty b hbe]
    · -- only `a` empty: the flipped call skips its first guard, then returns `b` on the second
      rw [dif_neg hbe, dif_pos hae]
  · rw [dif_neg hae]
    by_cases hbe : b.isEmpty = true
    · -- only `b` empty: both calls return `a`
      rw [dif_pos hbe, dif_pos hbe]
    · -- both non-empty: clear the flipped call's `a.isEmpty` guard too, then compare heights
      rw [dif_neg hbe, dif_neg hbe, dif_neg hae]
      rcases Nat.lt_trichotomy a.height b.height with hlt | heq | hgt
      · -- `a` shorter: both descend `b`'s spine (RHS's double flip cancels by η)
        rw [dif_pos (Nat.le_of_lt hlt), dif_neg (Nat.not_le.mpr hlt)]
      · -- equal heights: both reduce to a `joinEq` (`d = 0`); close by `joinEq_comm`
        rw [dif_pos (Nat.le_of_eq heq), dif_pos (Nat.le_of_eq heq.symm)]
        obtain ⟨ha, ta, wa⟩ := a
        obtain ⟨hb, tb, wb⟩ := b
        dsimp only at heq ⊢
        subst hb
        apply normalizeAux_congr
        -- generalize the (zero) height difference to `subst` away the dependent `Tree.cast`s
        suffices H : ∀ (d : Nat), d = 0 → ∀ (p₁ p₂ : ha = ha + d),
            Tree.joinSpine combine ha d ta (Tree.cast p₁ tb)
              = Tree.joinSpine (fun x y => combine y x) ha d tb (Tree.cast p₂ ta) from
          H (ha - ha) (Nat.sub_self ha) (by omega) (by omega)
        intro d hd p₁ p₂
        subst hd
        simp only [Tree.joinSpine]
        exact Tree.joinEq_comm combine (fun x y => combine y x) (fun _ _ => rfl) ha ta tb
      · -- `a` taller: both descend `a`'s spine with the same flipped combine
        rw [dif_neg (Nat.not_le.mpr hgt), dif_pos (Nat.le_of_lt hgt)]

/-- `meet` commutes when the combine is flipped: `meet combine a b = meet (fun x y => combine y x) b a`.
The empty short-circuits both return `empty`; when the heights differ both sides descend the *same*
(taller) tree's spine to the *smaller* height — the double flip cancels by η, so they are
definitionally equal; at equal heights both reduce to a `meetEq` with `d = 0`, related by
`Tree.meetEq_comm`. -/
theorem meet_comm (combine : V → V → V) (a b : NatCollection L) :
    meet combine a b = meet (fun x y => combine y x) b a := by
  unfold meet
  by_cases hae : a.isEmpty = true
  · rw [if_pos hae]
    by_cases hbe : b.isEmpty = true
    · -- both empty: each side returns `empty` outright
      rw [if_pos hbe]
    · -- only `a` empty: the flipped call skips its first guard, then returns `empty` on the second
      rw [if_neg hbe, if_pos hae]
  · rw [if_neg hae]
    by_cases hbe : b.isEmpty = true
    · -- only `b` empty: both calls return `empty`
      rw [if_pos hbe, if_pos hbe]
    · -- both non-empty: clear the flipped call's `a.isEmpty` guard too, then compare heights
      rw [if_neg hbe, if_neg hbe, if_neg hae]
      rcases Nat.lt_trichotomy a.height b.height with hlt | heq | hgt
      · -- `a` shorter: both descend `b`'s spine to height `a.height` (RHS's double flip cancels by η)
        rw [dif_pos (Nat.le_of_lt hlt), dif_neg (Nat.not_le.mpr hlt)]
      · -- equal heights: both reduce to a `meetEq` (`d = 0`); close by `meetEq_comm`
        rw [dif_pos (Nat.le_of_eq heq), dif_pos (Nat.le_of_eq heq.symm)]
        obtain ⟨ha, ta, wa⟩ := a
        obtain ⟨hb, tb, wb⟩ := b
        dsimp only at heq ⊢
        subst hb
        apply normalizeAux_congr
        -- generalize the (zero) height difference to `subst` away the dependent `Tree.cast`s
        suffices H : ∀ (d : Nat), d = 0 → ∀ (p₁ p₂ : ha = ha + d),
            Tree.meetSpine combine ha d ta (Tree.cast p₁ tb)
              = Tree.meetSpine (fun x y => combine y x) ha d tb (Tree.cast p₂ ta) from
          H (ha - ha) (Nat.sub_self ha) (by omega) (by omega)
        intro d hd p₁ p₂
        subst hd
        simp only [Tree.meetSpine]
        exact Tree.meetEq_comm combine (fun x y => combine y x) (fun _ _ => rfl) ha ta tb
      · -- `a` taller: both descend `a`'s spine to height `b.height` with the same flipped combine
        rw [dif_neg (Nat.not_le.mpr hgt), dif_pos (Nat.le_of_lt hgt)]

/-! ### Associativity of `join`

The collection-level `join` mixes heights via `joinSpine`/`normalizeAux`; the strategy is to lift
both operands to a common height `H` and show `join` there is `Tree.joinEq`, then invoke the
equal-height kernel `Tree.joinEq_assoc`. The `Tree` bridge lemmas
(`joinSpine_eq_joinEq_liftBy`, `liftBy_joinEq`, `liftBy_liftBy`) do the structural work; the
collection lemmas below handle the `normalizeAux` smart constructor and the height bookkeeping. -/

/-- `normalizeAux` is the identity on an already-canonical tree (its top mask is `≥ 2`, so neither
height-lowering arm fires). -/
private theorem normalizeAux_eq_of_TopProper : (h : Nat) → (t : Tree L h) → (hf : Tree.Full h t) →
    (htp : Tree.TopProper h t) → normalizeAux h t hf = ⟨h, t, ⟨hf, htp⟩⟩
  | 0, _, _, _ => by simp only [normalizeAux]
  | h + 1, n, hf, htp => by
      have htp' : 2 ≤ n.positionsMask := htp
      unfold normalizeAux
      split
      · rename_i hm0; rw [eq_of_beq hm0] at htp'; exact absurd htp' (by decide)
      · split
        · rename_i hm1; rw [eq_of_beq hm1] at htp'; exact absurd htp' (by decide)
        · rfl

/-- The `TopProper` argument shared by the join lemmas (left operand the shorter). -/
private theorem topProper_joinSpine_left (combine : V → V → V) (a b : NatCollection L)
    (ha : a.isEmpty = false) (hle : a.height ≤ b.height) :
    Tree.TopProper _ (Tree.joinSpine combine a.height (b.height - a.height) a.tree
      (Tree.cast (by omega) b.tree)) :=
  Tree.TopProper_joinSpine combine a.height (b.height - a.height) a.tree (Tree.cast (by omega) b.tree)
    (by simpa using ha) a.wf.1 (Tree.Full_cast (by omega) b.tree b.wf.1) a.wf.2
    (Tree.TopProper_cast (by omega) b.tree b.wf.2)

/-- A `join` of two non-empty collections is non-empty. -/
private theorem isEmpty_join (combine : V → V → V) (a b : NatCollection L)
    (ha : a.isEmpty = false) (hb : b.isEmpty = false) :
    (join combine a b).isEmpty = false := by
  have hane : Tree.isEmpty a.height a.tree = false := by simpa using ha
  have hbne : Tree.isEmpty b.height b.tree = false := by simpa using hb
  unfold join
  rw [dif_neg (by simpa using ha), dif_neg (by simpa using hb)]
  by_cases hle : a.height ≤ b.height
  · rw [dif_pos hle, normalizeAux_eq_of_TopProper _ _ _ (topProper_joinSpine_left combine a b ha hle)]
    show Tree.isEmpty _ (Tree.joinSpine combine a.height (b.height - a.height) a.tree
        (Tree.cast (by omega) b.tree)) = false
    rw [Tree.joinSpine_eq_joinEq_liftBy combine a.height a.tree hane a.wf.1 (b.height - a.height)
          (Tree.cast (by omega) b.tree) (Tree.Full_cast (by omega) b.tree b.wf.1)]
    exact Tree.isEmpty_joinEq_eq_false combine _ _ _
      (Tree.isEmpty_liftBy (b.height - a.height) a.tree hane)
      (Tree.Full_liftBy (b.height - a.height) a.tree a.wf.1 hane)
      (Tree.Full_cast (by omega) b.tree b.wf.1)
  · rw [dif_neg hle, normalizeAux_eq_of_TopProper _ _ _
        (topProper_joinSpine_left (fun x y => combine y x) b a hb (Nat.le_of_lt (Nat.not_le.mp hle)))]
    show Tree.isEmpty _ (Tree.joinSpine (fun x y => combine y x) b.height (a.height - b.height) b.tree
        (Tree.cast (by omega) a.tree)) = false
    rw [Tree.joinSpine_eq_joinEq_liftBy (fun x y => combine y x) b.height b.tree hbne b.wf.1
          (a.height - b.height) (Tree.cast (by omega) a.tree) (Tree.Full_cast (by omega) a.tree a.wf.1)]
    exact Tree.isEmpty_joinEq_eq_false _ _ _ _
      (Tree.isEmpty_liftBy (a.height - b.height) b.tree hbne)
      (Tree.Full_liftBy (a.height - b.height) b.tree b.wf.1 hbne)
      (Tree.Full_cast (by omega) a.tree a.wf.1)

/-- A `join` of two non-empty collections sits at the maximum of the operand heights. -/
private theorem join_height (combine : V → V → V) (a b : NatCollection L)
    (ha : a.isEmpty = false) (hb : b.isEmpty = false) :
    (join combine a b).height = max a.height b.height := by
  unfold join
  rw [dif_neg (by simpa using ha), dif_neg (by simpa using hb)]
  by_cases hle : a.height ≤ b.height
  · rw [dif_pos hle, normalizeAux_eq_of_TopProper _ _ _ (topProper_joinSpine_left combine a b ha hle)]
    show a.height + (b.height - a.height) = max a.height b.height
    omega
  · rw [dif_neg hle, normalizeAux_eq_of_TopProper _ _ _
        (topProper_joinSpine_left (fun x y => combine y x) b a hb (Nat.le_of_lt (Nat.not_le.mp hle)))]
    show b.height + (a.height - b.height) = max a.height b.height
    omega

/-- Explicit structure of a `join` when the left operand is the shorter (`normalizeAux` is the
identity on the canonical spine result). -/
private theorem join_eq_le (combine : V → V → V) (a b : NatCollection L)
    (ha : a.isEmpty = false) (hb : b.isEmpty = false) (hle : a.height ≤ b.height) :
    join combine a b = ⟨a.height + (b.height - a.height),
      Tree.joinSpine combine a.height (b.height - a.height) a.tree (Tree.cast (by omega) b.tree),
      ⟨Tree.Full_joinSpine combine a.height (b.height - a.height) a.tree (Tree.cast (by omega) b.tree)
          (by simpa using ha) a.wf.1 (Tree.Full_cast (by omega) b.tree b.wf.1),
        topProper_joinSpine_left combine a b ha hle⟩⟩ := by
  unfold join
  rw [dif_neg (by simpa using ha), dif_neg (by simpa using hb), dif_pos hle]
  exact normalizeAux_eq_of_TopProper _ _ _ (topProper_joinSpine_left combine a b ha hle)

/-- Explicit structure of a `join` when the *right* operand is the shorter (the left taller).
The combine is flipped, matching `join`'s definition. -/
private theorem join_eq_gt (combine : V → V → V) (a b : NatCollection L)
    (ha : a.isEmpty = false) (hb : b.isEmpty = false) (hgt : ¬ a.height ≤ b.height) :
    join combine a b = ⟨b.height + (a.height - b.height),
      Tree.joinSpine (fun x y => combine y x) b.height (a.height - b.height) b.tree
        (Tree.cast (by omega) a.tree),
      ⟨Tree.Full_joinSpine (fun x y => combine y x) b.height (a.height - b.height) b.tree
          (Tree.cast (by omega) a.tree) (by simpa using hb) b.wf.1 (Tree.Full_cast (by omega) a.tree a.wf.1),
        topProper_joinSpine_left (fun x y => combine y x) b a hb
          (Nat.le_of_lt (Nat.not_le.mp hgt))⟩⟩ := by
  unfold join
  rw [dif_neg (by simpa using ha), dif_neg (by simpa using hb), dif_neg hgt]
  exact normalizeAux_eq_of_TopProper _ _ _
    (topProper_joinSpine_left (fun x y => combine y x) b a hb (Nat.le_of_lt (Nat.not_le.mp hgt)))

/-- Lifting a `join` to a common height `H` equals the equal-height `joinEq` of both operands
lifted to `H`. The structural heart of `join_assoc`. -/
private theorem join_liftTo (combine : V → V → V) (a b : NatCollection L)
    (ha : a.isEmpty = false) (hb : b.isEmpty = false) (H : Nat)
    (hAH : a.height ≤ H) (hBH : b.height ≤ H) (hjH : (join combine a b).height ≤ H) :
    (join combine a b).liftTo H hjH = Tree.joinEq combine H (a.liftTo H hAH) (b.liftTo H hBH) := by
  by_cases hle : a.height ≤ b.height
  · -- left operand shorter: descend `b`'s spine
    simp only [join_eq_le combine a b ha hb hle]
    simp only [NatCollection.liftTo]
    rw [Tree.liftBy_joinSpine combine a.height (b.height - a.height) a.tree
          (Tree.cast (by omega) b.tree) (H - (a.height + (b.height - a.height)))
          (by simpa using ha)
          ((Tree.isEmpty_cast (by omega) b.tree).trans (by simpa using hb))
          a.wf.1 (Tree.Full_cast (by omega) b.tree b.wf.1),
        Tree.joinEq_cast]
    rw [Tree.cast_cast,
        Tree.liftBy_congr_d (show (b.height - a.height) + (H - (a.height + (b.height - a.height)))
          = H - a.height by omega) a.tree,
        Tree.cast_cast,
        Tree.liftBy_cast, Tree.cast_cast,
        Tree.liftBy_congr_d (show H - (a.height + (b.height - a.height)) = H - b.height by omega)
          b.tree,
        Tree.cast_cast]
  · -- left operand taller: descend `a`'s spine with flipped combine, then `joinEq_comm`
    simp only [join_eq_gt combine a b ha hb hle]
    simp only [NatCollection.liftTo]
    rw [Tree.liftBy_joinSpine (fun x y => combine y x) b.height (a.height - b.height) b.tree
          (Tree.cast (by omega) a.tree) (H - (b.height + (a.height - b.height)))
          (by simpa using hb)
          ((Tree.isEmpty_cast (by omega) a.tree).trans (by simpa using ha))
          b.wf.1 (Tree.Full_cast (by omega) a.tree a.wf.1),
        Tree.joinEq_cast,
        Tree.joinEq_comm (fun x y => combine y x) combine (fun _ _ => rfl) H]
    rw [Tree.cast_cast, Tree.liftBy_cast, Tree.cast_cast,
        Tree.liftBy_congr_d (show H - (b.height + (a.height - b.height)) = H - a.height by omega)
          a.tree,
        Tree.cast_cast,
        Tree.liftBy_congr_d (show (a.height - b.height) + (H - (b.height + (a.height - b.height)))
          = H - b.height by omega) b.tree,
        Tree.cast_cast]

/-- Two collections of equal height that lift to the same tree at a common height `H` are equal.
`liftTo` is injective (lifting wraps the tree under slot-0 singletons, which `liftBy_inj` undoes,
and `cast` is invertible), so equal lifts force equal trees, hence equal collections. -/
private theorem eq_of_liftTo_eq (a b : NatCollection L) (H : Nat)
    (hAH : a.height ≤ H) (hBH : b.height ≤ H) (hh : a.height = b.height)
    (hlift : a.liftTo H hAH = b.liftTo H hBH) : a = b := by
  obtain ⟨ha, ta, wa⟩ := a
  obtain ⟨hb, tb, wb⟩ := b
  subst hh
  simp only [NatCollection.liftTo] at hlift
  have hcast : Tree.liftBy (H - ha) ta = Tree.liftBy (H - ha) tb := Tree.cast_inj _ _ _ hlift
  have htt : ta = tb := Tree.liftBy_inj (H - ha) ta tb hcast
  subst htt
  rfl

/-- **Associativity of `join`** for an associative `combine`. Both sides are lifted to the common
height `H = max (max a.height b.height) e.height` and reduced — via `join_liftTo` — to nested
equal-height `joinEq`s, where `Tree.joinEq_assoc` discharges the reassociation; injectivity of
`liftTo` (`eq_of_liftTo_eq`) then transfers the equality back to the collections. -/
theorem join_assoc (combine : V → V → V)
    (hassoc : ∀ x y z, combine (combine x y) z = combine x (combine y z))
    (a b e : NatCollection L) :
    join combine (join combine a b) e = join combine a (join combine b e) := by
  by_cases hae : a.isEmpty = true
  · rw [eq_empty_of_isEmpty a hae, join_empty_left, join_empty_left]
  · by_cases hbe : b.isEmpty = true
    · rw [eq_empty_of_isEmpty b hbe, join_empty_right, join_empty_left]
    · by_cases hee : e.isEmpty = true
      · rw [eq_empty_of_isEmpty e hee, join_empty_right, join_empty_right]
      · -- all three non-empty
        simp only [Bool.not_eq_true] at hae hbe hee
        have hab_ne : (join combine a b).isEmpty = false := isEmpty_join combine a b hae hbe
        have hbe_ne : (join combine b e).isEmpty = false := isEmpty_join combine b e hbe hee
        have hab_h : (join combine a b).height = max a.height b.height := join_height combine a b hae hbe
        have hbe_h : (join combine b e).height = max b.height e.height := join_height combine b e hbe hee
        have hL_h : (join combine (join combine a b) e).height = max (join combine a b).height e.height :=
          join_height combine (join combine a b) e hab_ne hee
        have hR_h : (join combine a (join combine b e)).height = max a.height (join combine b e).height :=
          join_height combine a (join combine b e) hae hbe_ne
        generalize hH : max (max a.height b.height) e.height = H
        have h_a_H : a.height ≤ H := by omega
        have h_b_H : b.height ≤ H := by omega
        have h_e_H : e.height ≤ H := by omega
        have h_ab_H : (join combine a b).height ≤ H := by omega
        have h_be_H : (join combine b e).height ≤ H := by omega
        have hLH : (join combine (join combine a b) e).height ≤ H := by omega
        have hRH : (join combine a (join combine b e)).height ≤ H := by omega
        refine eq_of_liftTo_eq _ _ H hLH hRH (by omega) ?_
        rw [join_liftTo combine (join combine a b) e hab_ne hee H h_ab_H h_e_H hLH,
            join_liftTo combine a b hae hbe H h_a_H h_b_H h_ab_H,
            join_liftTo combine a (join combine b e) hae hbe_ne H h_a_H h_be_H hRH,
            join_liftTo combine b e hbe hee H h_b_H h_e_H h_be_H,
            Tree.joinEq_assoc combine hassoc H (a.liftTo H h_a_H) (b.liftTo H h_b_H)
              (e.liftTo H h_e_H) (Full_liftTo a H h_a_H hae) (Full_liftTo b H h_b_H hbe)
              (Full_liftTo e H h_e_H hee)]

section Tests

-- The canonical-shape invariant is a field, so it is available on *every* collection — and
-- on every operation result — by construction, no side condition: no excessive height
-- (`TopProper`) and no empty subtree (`Full`).
example (c : NatCollection L) : Tree.Full c.height c.tree := c.wf.1
example (c : NatCollection L) : Tree.TopProper c.height c.tree := c.wf.2
example (c : NatCollection L) (k : Nat) (v : V) :
    Tree.Canonical (c.insert k v).height (c.insert k v).tree := (c.insert k v).wf

end Tests

end NatCollection

end NatCol
