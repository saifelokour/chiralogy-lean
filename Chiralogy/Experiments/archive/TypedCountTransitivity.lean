import Chiralogy.Model.AssemblageRelations

/-! ARCHIVED (fully graduated). The exchange between equinumerous fibres.

GRADUATED to `Model/NaryAssemblage`, same names: the exchange through the cast, `swapT` with `swapT_i`,
`swapT_j`, `swapT_other`, `swapT_involutive`, `coordSwapT`, `mem_diffSet_swapT`, `diffSet_swapT`,
`coordSwapT_crossStable`, `sdiff_after_swapT`, and the coordinatewise half `exists_equiv_pair`, `movePair`,
`fibEquiv`, `sameOrbit_of_same_diffSet`. Spec 9.22, 9.24.

CHANGED IN GRADUATION. The induction graduated in its EQUINUMEROSITY form, not the cardinal form this file
proved. `swapT` was always parameterized by a bijection and never mentioned cardinality; only the SOURCE of
that bijection changed, from `Fintype.equivOfCardEq` to the equinumerosity hypothesis. That single substitution
is what lifted the transitivity off finiteness.

The cast discipline this file established is what made the audit meaningful: the cast is confined to three
reading lemmas, so there were only three places it could have gone wrong. Typechecks standalone. -/

/-! # Experiment (LIVE): the exchange between equinumerous fibres

`HeterogeneousOrbit` proved the plain differing count fails heterogeneously and left the typed count's
transitivity open, because the exchange it needs moves a value between fibres that are equinumerous but not
identical. That is a cast in a dependent product, and it was not attempted.

This attempts it.

Register-neutral throughout: no statement and no proof mentions any domain.

Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.TypedCountTransitivity

/-! ### GRADUATED (external-relation pass)

Into `Model/NaryAssemblage`, same names: the exchange through the cast, `swapT` with `swapT_i`, `swapT_j`,
`swapT_other`, `swapT_involutive`, `coordSwapT`, `mem_diffSet_swapT`, `diffSet_swapT`,
`coordSwapT_crossStable`, `sdiff_after_swapT`, and the coordinatewise half `exists_equiv_pair`, `movePair`,
`fibEquiv`, `sameOrbit_of_same_diffSet`. Spec 9.22, 9.24.

CHANGED IN GRADUATION: the induction graduated in its equinumerosity form (`sameOrbit_of_same_eqTypedCount`),
not the cardinal form. `swapT` was always parameterized by a bijection; only the SOURCE of that bijection
changed, from `Fintype.equivOfCardEq` to the equinumerosity hypothesis.

This file is fully graduated. -/

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-! ## The differing set and the orbit relation, restated

Live files cannot import each other, so the machinery the earlier builds established is restated. Its proofs
are the same proofs. -/

def diffSet (a b : Pt X) : Finset (Fin n) := Finset.univ.filter (fun i => a i ≠ b i)

theorem mem_diffSet {a b : Pt X} {i : Fin n} : i ∈ diffSet a b ↔ a i ≠ b i := by
  simp [diffSet]

theorem diffSet_eq_empty_iff (a b : Pt X) : diffSet a b = ∅ ↔ a = b := by
  constructor
  · intro h
    funext i
    by_contra hne
    have : i ∈ (∅ : Finset (Fin n)) := by rw [← h]; exact mem_diffSet.mpr hne
    simp at this
  · intro h
    subst h
    exact Finset.filter_eq_empty_iff.mpr (fun _ _ => by simp)

theorem differsInOne_iff_diffSet (a b : Pt X) (i : Fin n) :
    differsInOne a b i ↔ diffSet a b = {i} := by
  constructor
  · rintro ⟨hne, hoth⟩
    ext j
    rw [mem_diffSet, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hji
      exact hj (hoth j hji)
    · intro hj; subst hj; exact hne
  · intro h
    refine ⟨?_, fun j hj => ?_⟩
    · exact mem_diffSet.mp (by rw [h]; exact Finset.mem_singleton_self i)
    · by_contra hc
      exact hj (Finset.mem_singleton.mp (by rw [← h]; exact mem_diffSet.mpr hc))

def CrossStable (e : Pt X ≃ Pt X) : Prop := ∀ a b, IsCross a b ↔ IsCross (e a) (e b)

theorem exists_differsInOne_iff_card (a b : Pt X) :
    (∃ k, differsInOne a b k) ↔ (diffSet a b).card = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    rw [(differsInOne_iff_diffSet a b k).mp hk]
    exact Finset.card_singleton k
  · intro h
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h
    exact ⟨k, (differsInOne_iff_diffSet a b k).mpr hk⟩

/-- A bijection permuting the differing set by a fixed index permutation is cross-stable: the differing sets
correspond, so their sizes agree, and being cross is the size not being one. -/
theorem crossStable_of_diffSet_perm (e : Pt X ≃ Pt X) (σ : Equiv.Perm (Fin n))
    (h : ∀ a b k, k ∈ diffSet (e a) (e b) ↔ σ k ∈ diffSet a b) : CrossStable e := by
  intro a b
  have hmap : diffSet (e a) (e b) = (diffSet a b).map σ.symm.toEmbedding := by
    ext k
    rw [h a b k, Finset.mem_map]
    constructor
    · intro hk
      refine ⟨σ k, hk, ?_⟩
      show σ.symm (σ k) = k
      rw [Equiv.symm_apply_apply]
    · rintro ⟨m, hm, rfl⟩
      show σ (σ.symm m) ∈ _
      rw [Equiv.apply_symm_apply]
      exact hm
  have hcard : (diffSet (e a) (e b)).card = (diffSet a b).card := by
    rw [hmap, Finset.card_map]
  show (¬ ∃ k, differsInOne a b k) ↔ (¬ ∃ k, differsInOne (e a) (e b) k)
  rw [exists_differsInOne_iff_card, exists_differsInOne_iff_card, hcard]

def SameOrbit (a b a' b' : Pt X) : Prop :=
  ∃ e : Pt X ≃ Pt X, CrossStable e ∧ e a = a' ∧ e b = b'

theorem crossStable_trans {e f : Pt X ≃ Pt X} (he : CrossStable e) (hf : CrossStable f) :
    CrossStable (e.trans f) := fun a b => (he a b).trans (hf (e a) (e b))

theorem sameOrbit_trans {a b a' b' a'' b'' : Pt X}
    (h : SameOrbit a b a' b') (h' : SameOrbit a' b' a'' b'') : SameOrbit a b a'' b'' := by
  obtain ⟨e, he, h1, h2⟩ := h
  obtain ⟨f, hf, k1, k2⟩ := h'
  refine ⟨e.trans f, crossStable_trans he hf, ?_, ?_⟩
  · show f (e a) = a''; rw [h1, k1]
  · show f (e b) = b''; rw [h2, k2]

/-! ### The coordinatewise half, restated: no hypothesis needed -/

theorem exists_equiv_pair {Y : Type} [DecidableEq Y] {u v u' v' : Y} (huv : u ≠ v) (huv' : u' ≠ v') :
    ∃ f : Y ≃ Y, f u = u' ∧ f v = v' := by
  refine ⟨(Equiv.swap u u').trans (Equiv.swap (Equiv.swap u u' v) v'), ?_, ?_⟩
  · show Equiv.swap (Equiv.swap u u' v) v' (Equiv.swap u u' u) = u'
    rw [Equiv.swap_apply_left]
    by_cases hw : Equiv.swap u u' v = v'
    · rw [hw, Equiv.swap_self]
      rfl
    · refine Equiv.swap_apply_of_ne_of_ne ?_ huv'
      intro hc
      by_cases hvu' : v = u'
      · rw [hvu', Equiv.swap_apply_right] at hc
        exact huv (hvu'.trans hc).symm
      · rw [Equiv.swap_apply_of_ne_of_ne (fun hx => huv hx.symm) hvu'] at hc
        exact hvu' hc.symm
  · show Equiv.swap (Equiv.swap u u' v) v' (Equiv.swap u u' v) = v'
    exact Equiv.swap_apply_left _ _

noncomputable def movePair {Y : Type} [DecidableEq Y] (u v u' v' : Y) : Y ≃ Y :=
  if h : u ≠ v ∧ u' ≠ v' then Classical.choose (exists_equiv_pair h.1 h.2)
  else Equiv.swap u u'

theorem movePair_spec_ne {Y : Type} [DecidableEq Y] {u v u' v' : Y} (huv : u ≠ v) (huv' : u' ≠ v') :
    movePair u v u' v' u = u' ∧ movePair u v u' v' v = v' := by
  have hd : u ≠ v ∧ u' ≠ v' := ⟨huv, huv'⟩
  rw [movePair, dif_pos hd]
  exact Classical.choose_spec (exists_equiv_pair hd.1 hd.2)

theorem movePair_spec_eq {Y : Type} [DecidableEq Y] {u v u' v' : Y} (huv : u = v) (huv' : u' = v') :
    movePair u v u' v' u = u' ∧ movePair u v u' v' v = v' := by
  have hd : ¬ (u ≠ v ∧ u' ≠ v') := fun h => h.1 huv
  rw [movePair, dif_neg hd]
  refine ⟨Equiv.swap_apply_left u u', ?_⟩
  rw [← huv, Equiv.swap_apply_left u u']
  exact huv'

def fibEquiv (π : ∀ k, X k ≃ X k) : Pt X ≃ Pt X where
  toFun a := fun k => π k (a k)
  invFun a := fun k => (π k).symm (a k)
  left_inv a := by funext k; exact (π k).symm_apply_apply (a k)
  right_inv a := by funext k; exact (π k).apply_symm_apply (a k)

theorem diffSet_fibEquiv (π : ∀ k, X k ≃ X k) (a b : Pt X) :
    diffSet (fibEquiv π a) (fibEquiv π b) = diffSet a b := by
  ext k
  rw [mem_diffSet, mem_diffSet]
  show π k (a k) ≠ π k (b k) ↔ a k ≠ b k
  exact ⟨fun h hc => h (by rw [hc]), fun h hc => h ((π k).injective hc)⟩

theorem fibEquiv_crossStable (π : ∀ k, X k ≃ X k) : CrossStable (fibEquiv π) :=
  crossStable_of_diffSet_perm _ (Equiv.refl _) (fun a b k => by
    rw [diffSet_fibEquiv]; exact Iff.rfl)

/-- The coordinatewise half: two cells with the same differing set lie in one orbit, no hypothesis. -/
theorem sameOrbit_of_same_diffSet (a b a' b' : Pt X) (h : diffSet a b = diffSet a' b') :
    SameOrbit a b a' b' := by
  refine ⟨fibEquiv (fun k => movePair (a k) (b k) (a' k) (b' k)),
    fibEquiv_crossStable _, ?_, ?_⟩
  · funext k
    show movePair (a k) (b k) (a' k) (b' k) (a k) = a' k
    by_cases hk : a k = b k
    · have hk' : a' k = b' k := by
        by_contra hc
        have h1 : k ∈ diffSet a' b' := mem_diffSet.mpr hc
        rw [← h] at h1
        exact (mem_diffSet.mp h1) hk
      exact (movePair_spec_eq hk hk').1
    · have hk' : a' k ≠ b' k := by
        intro hc
        have h1 : k ∈ diffSet a b := mem_diffSet.mpr hk
        rw [h] at h1
        exact (mem_diffSet.mp h1) hc
      exact (movePair_spec_ne hk hk').1
  · funext k
    show movePair (a k) (b k) (a' k) (b' k) (b k) = b' k
    by_cases hk : a k = b k
    · have hk' : a' k = b' k := by
        by_contra hc
        have h1 : k ∈ diffSet a' b' := mem_diffSet.mpr hc
        rw [← h] at h1
        exact (mem_diffSet.mp h1) hk
      exact (movePair_spec_eq hk hk').2
    · have hk' : a' k ≠ b' k := by
        intro hc
        have h1 : k ∈ diffSet a b := mem_diffSet.mpr hk
        rw [h] at h1
        exact (mem_diffSet.mp h1) hc
      exact (movePair_spec_ne hk hk').2

/-! ## Part 1: the exchange between equinumerous fibres

The map below is the one the previous build did not attempt. It exchanges coordinates `i` and `j` while
carrying the value across an equivalence `X i` to `X j`. The value at `i` has type `X i` and must be delivered
at `j`, which needs a CAST, and every lemma about the map passes through it. -/

section Exchange

variable {i j : Fin n}

/-- **THE TYPED EXCHANGE.** Swap coordinates `i` and `j`, transporting the values along `ψ`. The two casts are
what make the definition typecheck at all: the branch for `k = i` produces a value of type `X i` and must be
delivered at type `X k`. -/
def swapT (i j : Fin n) (ψ : X i ≃ X j) (a : Pt X) : Pt X :=
  fun k =>
    if hi : k = i then cast (congrArg X hi.symm) (ψ.symm (a j))
    else if hj : k = j then cast (congrArg X hj.symm) (ψ (a i))
    else a k

/-- Reading the exchange at `i`: the cast is along `rfl` and vanishes. -/
theorem swapT_i (ψ : X i ≃ X j) (a : Pt X) : swapT i j ψ a i = ψ.symm (a j) := by
  show (if hi : i = i then cast (congrArg X hi.symm) (ψ.symm (a j))
        else if hj : i = j then cast (congrArg X hj.symm) (ψ (a i)) else a i) = ψ.symm (a j)
  rw [dif_pos (rfl : i = i)]
  rfl

/-- Reading the exchange at `j`. -/
theorem swapT_j (hij : i ≠ j) (ψ : X i ≃ X j) (a : Pt X) : swapT i j ψ a j = ψ (a i) := by
  show (if hi : j = i then cast (congrArg X hi.symm) (ψ.symm (a j))
        else if hj : j = j then cast (congrArg X hj.symm) (ψ (a i)) else a j) = ψ (a i)
  rw [dif_neg (fun h => hij h.symm), dif_pos (rfl : j = j)]
  rfl

/-- Reading the exchange anywhere else: untouched. -/
theorem swapT_other (ψ : X i ≃ X j) (a : Pt X) {k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    swapT i j ψ a k = a k := by
  show (if hi : k = i then cast (congrArg X hi.symm) (ψ.symm (a j))
        else if hj : k = j then cast (congrArg X hj.symm) (ψ (a i)) else a k) = a k
  rw [dif_neg hki, dif_neg hkj]

theorem swapT_involutive (hij : i ≠ j) (ψ : X i ≃ X j) (a : Pt X) :
    swapT i j ψ (swapT i j ψ a) = a := by
  funext k
  by_cases hki : k = i
  · subst hki
    rw [swapT_i, swapT_j hij, Equiv.symm_apply_apply]
  · by_cases hkj : k = j
    · subst hkj
      rw [swapT_j hij, swapT_i, Equiv.apply_symm_apply]
    · rw [swapT_other ψ _ hki hkj, swapT_other ψ a hki hkj]

/-- The exchange as a bijection of the carrier. -/
def coordSwapT (hij : i ≠ j) (ψ : X i ≃ X j) : Pt X ≃ Pt X :=
  ⟨swapT i j ψ, swapT i j ψ, swapT_involutive hij ψ, swapT_involutive hij ψ⟩

/-- **The exchange permutes the differing set by the index swap.** Every clause passes through a cast, and the
casts are discharged by the three reading lemmas above rather than by any tactic guessing. -/
theorem mem_diffSet_swapT (hij : i ≠ j) (ψ : X i ≃ X j) (a b : Pt X) (k : Fin n) :
    k ∈ diffSet (swapT i j ψ a) (swapT i j ψ b) ↔ Equiv.swap i j k ∈ diffSet a b := by
  rw [mem_diffSet, mem_diffSet]
  by_cases hki : k = i
  · subst hki
    rw [swapT_i, swapT_i, Equiv.swap_apply_left]
    exact ⟨fun h hc => h (by rw [hc]), fun h hc => h (ψ.symm.injective hc)⟩
  · by_cases hkj : k = j
    · subst hkj
      rw [swapT_j hij, swapT_j hij, Equiv.swap_apply_right]
      exact ⟨fun h hc => h (by rw [hc]), fun h hc => h (ψ.injective hc)⟩
    · rw [swapT_other ψ a hki hkj, swapT_other ψ b hki hkj,
        Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem diffSet_swapT (hij : i ≠ j) (ψ : X i ≃ X j) (a b : Pt X) :
    diffSet (swapT i j ψ a) (swapT i j ψ b)
      = (diffSet a b).map (Equiv.swap i j).toEmbedding := by
  ext k
  rw [mem_diffSet_swapT hij, Finset.mem_map]
  constructor
  · intro hk
    refine ⟨Equiv.swap i j k, hk, ?_⟩
    show Equiv.swap i j (Equiv.swap i j k) = k
    rw [Equiv.swap_apply_self]
  · rintro ⟨m, hm, rfl⟩
    show Equiv.swap i j (Equiv.swap i j m) ∈ _
    rw [Equiv.swap_apply_self]
    exact hm

/-- **The exchange is cross-stable.** -/
theorem coordSwapT_crossStable (hij : i ≠ j) (ψ : X i ≃ X j) :
    CrossStable (coordSwapT hij ψ) :=
  crossStable_of_diffSet_perm _ (Equiv.swap i j) (fun a b k => mem_diffSet_swapT hij ψ a b k)

end Exchange

/-! ## The typed differing count -/

section Typed

variable [∀ i, Fintype (X i)]

def typedCount (a b : Pt X) (q : ℕ) : ℕ :=
  ((diffSet a b).filter (fun i => Fintype.card (X i) = q)).card

def sizes (X : Fin n → Type) [∀ i, Fintype (X i)] : Finset ℕ :=
  Finset.univ.image (fun i => Fintype.card (X i))

theorem plain_from_typed (a b : Pt X) :
    (diffSet a b).card = ∑ q ∈ sizes X, typedCount a b q := by
  refine Finset.card_eq_sum_card_fiberwise ?_
  intro i _
  simp [sizes]

/-- **The exchange preserves every typed count.** It moves the differing set by an index swap that exchanges
two coordinates of EQUAL fibre size, so each size class keeps its membership count. -/
theorem typedCount_swapT {i j : Fin n} (hij : i ≠ j) (ψ : X i ≃ X j)
    (hcard : Fintype.card (X i) = Fintype.card (X j)) (a b : Pt X) (q : ℕ) :
    typedCount (swapT i j ψ a) (swapT i j ψ b) q = typedCount a b q := by
  have hP : ∀ m : Fin n, (Fintype.card (X (Equiv.swap i j m)) = q) ↔ (Fintype.card (X m) = q) := by
    intro m
    by_cases hmi : m = i
    · subst hmi; rw [Equiv.swap_apply_left, hcard]
    · by_cases hmj : m = j
      · subst hmj; rw [Equiv.swap_apply_right, hcard]
      · rw [Equiv.swap_apply_of_ne_of_ne hmi hmj]
  have hset : ((diffSet a b).map (Equiv.swap i j).toEmbedding).filter
        (fun m => Fintype.card (X m) = q)
      = ((diffSet a b).filter (fun m => Fintype.card (X m) = q)).map
        (Equiv.swap i j).toEmbedding := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨⟨m, hm, rfl⟩, hk⟩
      exact ⟨m, ⟨hm, (hP m).mp hk⟩, rfl⟩
    · rintro ⟨m, ⟨hm, hq⟩, rfl⟩
      exact ⟨⟨m, hm, rfl⟩, (hP m).mpr hq⟩
  rw [typedCount, typedCount, diffSet_swapT hij, hset, Finset.card_map]

/-- The exchange step, at the level of the set difference. -/
theorem sdiff_after_swapT (S T : Finset (Fin n)) {i j : Fin n}
    (hi : i ∈ S) (hiT : i ∉ T) (hj : j ∈ T) (hjS : j ∉ S) :
    (S.map (Equiv.swap i j).toEmbedding) \ T = (S \ T).erase i := by
  ext k
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hkT⟩
    have hpi : p ≠ i := by
      intro hc
      subst hc
      rw [Equiv.swap_apply_left] at hkT
      exact hkT hj
    have hpj : p ≠ j := fun hc => hjS (hc ▸ hp)
    rw [Equiv.swap_apply_of_ne_of_ne hpi hpj] at hkT ⊢
    exact ⟨hpi, hp, hkT⟩
  · rintro ⟨hki, hkS, hkT⟩
    have hkj : k ≠ j := fun hc => hkT (hc ▸ hj)
    exact ⟨⟨k, hkS, Equiv.swap_apply_of_ne_of_ne hki hkj⟩, hkT⟩

/-! ## Part 2: transitivity on the typed count -/

/-- **THE TRANSITIVITY, carrier-general and with no homogeneity hypothesis.** Two cells with the same typed
differing count lie in one orbit. Induction on how far the two differing sets lie apart: while they differ,
some fibre-size class separates them, and within that class the exchange moves one closer without changing any
typed count; when the sets agree, the coordinatewise half finishes. -/
theorem sameOrbit_of_same_typedCount_aux : ∀ (N : ℕ) (a b a' b' : Pt X),
    (diffSet a b \ diffSet a' b').card = N →
    (∀ q, typedCount a b q = typedCount a' b' q) →
    SameOrbit a b a' b' := by
  intro N
  induction N with
  | zero =>
    intro a b a' b' hN hq
    have hsub : diffSet a b ⊆ diffSet a' b' := by
      rw [← Finset.sdiff_eq_empty_iff_subset]
      exact Finset.card_eq_zero.mp hN
    have hcard : (diffSet a' b').card ≤ (diffSet a b).card := by
      rw [plain_from_typed, plain_from_typed]
      exact le_of_eq (Finset.sum_congr rfl (fun q _ => (hq q).symm))
    exact sameOrbit_of_same_diffSet a b a' b' (Finset.eq_of_subset_of_card_le hsub hcard)
  | succ M ih =>
    intro a b a' b' hN hq
    set S := diffSet a b with hS
    set T := diffSet a' b' with hT
    have hne : (S \ T).Nonempty := Finset.card_pos.mp (by rw [hN]; omega)
    obtain ⟨k, hkST⟩ := hne
    rw [Finset.mem_sdiff] at hkST
    set q := Fintype.card (X k) with hqdef
    set A := S.filter (fun m => Fintype.card (X m) = q) with hA
    set B := T.filter (fun m => Fintype.card (X m) = q) with hB
    have hkA : k ∈ A := Finset.mem_filter.mpr ⟨hkST.1, rfl⟩
    have hkB : k ∉ B := fun hc => hkST.2 (Finset.mem_filter.mp hc).1
    have hABcard : A.card = B.card := hq q
    have hBA : (B \ A).Nonempty := by
      refine Finset.card_pos.mp ?_
      have h1 : (A \ B).card + (A ∩ B).card = A.card := Finset.card_sdiff_add_card_inter A B
      have h2 : (B \ A).card + (B ∩ A).card = B.card := Finset.card_sdiff_add_card_inter B A
      have h3 : (A ∩ B).card = (B ∩ A).card := by rw [Finset.inter_comm]
      have h4 : 0 < (A \ B).card :=
        Finset.card_pos.mpr ⟨k, Finset.mem_sdiff.mpr ⟨hkA, hkB⟩⟩
      omega
    obtain ⟨j, hjBA⟩ := hBA
    rw [Finset.mem_sdiff] at hjBA
    have hjT : j ∈ T := (Finset.mem_filter.mp hjBA.1).1
    have hjq : Fintype.card (X j) = q := (Finset.mem_filter.mp hjBA.1).2
    have hjS : j ∉ S := fun hc => hjBA.2 (Finset.mem_filter.mpr ⟨hc, hjq⟩)
    have hkj : k ≠ j := fun hc => hjS (hc ▸ hkST.1)
    have hcard : Fintype.card (X k) = Fintype.card (X j) := by rw [← hqdef, hjq]
    let ψ : X k ≃ X j := Fintype.equivOfCardEq hcard
    have hstep : SameOrbit a b (swapT k j ψ a) (swapT k j ψ b) :=
      ⟨coordSwapT hkj ψ, coordSwapT_crossStable hkj ψ, rfl, rfl⟩
    refine sameOrbit_trans hstep (ih (swapT k j ψ a) (swapT k j ψ b) a' b' ?_ ?_)
    · rw [diffSet_swapT hkj, ← hS, ← hT,
        sdiff_after_swapT S T hkST.1 hkST.2 hjT hjS,
        Finset.card_erase_of_mem (Finset.mem_sdiff.mpr hkST)]
      omega
    · intro r
      rw [typedCount_swapT hkj ψ hcard]
      exact hq r

theorem sameOrbit_of_same_typedCount (a b a' b' : Pt X)
    (h : ∀ q, typedCount a b q = typedCount a' b' q) : SameOrbit a b a' b' :=
  sameOrbit_of_same_typedCount_aux _ a b a' b' rfl h

/-- **THE CONSEQUENCE FOR THE TOWER.** Every structural label, being constant on orbits, is constant on typed
count classes: the orbit partition is coarser than or equal to the typed differing count, so every rung of the
tower is a coarsening of it. Carrier-general, no homogeneity. -/
theorem structural_labels_coarsen_typedCount {Q : Type} (q : Pt X → Pt X → Q)
    (hstruct : ∀ (e : Pt X ≃ Pt X), CrossStable e → ∀ a b, q (e a) (e b) = q a b)
    (a b a' b' : Pt X) (h : ∀ r, typedCount a b r = typedCount a' b' r) :
    q a b = q a' b' := by
  obtain ⟨e, he, rfl, rfl⟩ := sameOrbit_of_same_typedCount a b a' b' h
  exact (hstruct e he a b).symm

end Typed

/-! ## THE VERDICTS

PART 1: THE EXCHANGE THROUGH THE CAST WORKS, and the cast discipline is what makes it safe.

`swapT` is the map the previous build did not attempt: it exchanges two coordinates while carrying the value
across an equivalence between their fibres. It typechecks only because of two explicit casts, one per exchanged
coordinate, since the branch for `k = i` produces a value of type `X i` and must be delivered at type `X k`.

THE CAST IS HANDLED BY READING LEMMAS, NOT BY TACTICS. `swapT_i`, `swapT_j` and `swapT_other` discharge the
three cases once each, by reducing the dependent `if` at a known index so the cast is along `rfl` and vanishes.
Every later lemma goes through those three and never touches a cast again. That is deliberate: a cast
discharged by a tactic guessing at a transport is exactly the failure the audit exists to catch, and confining
it to three lemmas means there are only three places it could have gone wrong.

`swapT_involutive` makes it a bijection, `mem_diffSet_swapT` shows it permutes the differing set by the index
swap, and `coordSwapT_crossStable` concludes cross-stability. `typedCount_swapT` is the clause that needs the
fibres to be equinumerous: the index swap exchanges two coordinates of EQUAL fibre size, so every size class
keeps its membership count.

PART 2: TRANSITIVITY IS PROVED, carrier-general, with no homogeneity hypothesis.

`sameOrbit_of_same_typedCount` is the result. The induction is on how far the two differing sets lie apart.
While they differ, some fibre-size class separates them, and within that class both set differences are
nonempty by the counting argument, so an exchange between two equinumerous coordinates moves one set one
element closer while leaving every typed count fixed. When the sets agree, the coordinatewise half finishes,
and that half needs no hypothesis at all.

This is what `HeterogeneousOrbit` left open, and it closes.

PART 3: THE CLASSIFICATION IS NOT COMPLETE, and the brief's suggested shortcut does not work.

The brief asks whether arbitrary-distance INVARIANCE now follows from the transitivity. IT DOES NOT. They are
opposite inclusions. Transitivity says same typed count implies same orbit, so each typed class sits inside an
orbit and the orbit partition is COARSER than or equal to the typed count. Invariance would say same orbit
implies same typed count, putting each orbit inside a typed class. Neither implies the other, and only the
first is proved here.

WHAT IS THEREFORE ESTABLISHED, and it is worth stating exactly.
`structural_labels_coarsen_typedCount`: every structural label is constant on typed count classes, so EVERY
RUNG OF THE TOWER IS A COARSENING OF THE TYPED DIFFERING COUNT, at any carrier. That is an upper bound on how
fine the tower can be, and it is the half the classification needed from this direction.
NOT established: that the typed count is itself structural, which is what would make it the FINEST rung and
identify it with the orbit partition. `HeterogeneousOrbit` proved that only at distance one.

A CHEAPER ROUTE TO THE MISSING HALF THAN THE ONE PREVIOUSLY RECORDED. `HeterogeneousOrbit` sketched a geodesic
argument. There is a shorter one. For a cell with differing set `S`, the vertices adjacent to the first point
and one step nearer the second are exactly one per element of `S`, obtained by copying that coordinate across;
and the link count of each such vertex reads its coordinate's fibre size, by that file's `linkCount_eq`. So the
multiset of link counts over those vertices IS the typed count. It is preserved because adjacency is preserved
and the plain count is preserved. That needs the plain-count preservation and the first-step characterization,
and no geodesic bookkeeping. It is not formalized here.

PART 4: THE STRUCTURE CLAUSE CANNOT YET UPGRADE.

The external-relation bundle's STRUCTURE clause must still say the coarsenings of the ORBIT PARTITION. Saying
the coarsenings of the typed differing count would assert both inclusions, and only one is proved. What may now
be said, and is new, is that every rung is a coarsening of the typed count, which bounds the tower from one
side unconditionally.

The status is better than before in a specific way. Previously the concrete plain-count form was known FALSE
heterogeneously and nothing concrete was available. Now a concrete statement IS available in one direction, and
the remaining gap is a single named lemma rather than an open question about what the answer is.

GRADUATION. Nothing here graduates yet. When the missing half lands, this file and
`CrossStableGroup`, `HowManyIsOrbit` and `HeterogeneousOrbit` graduate as one classification group at
`Model/NaryAssemblage`, since they share the differing-set vocabulary and each supplies one clause.

VOCABULARY NOTE FOR THE SPEC, NOT FOR ANY THEOREM NAME. The exchange is the wreath-product generator acting
between equal-alphabet coordinates; the typed count is the class scheme of a product of Hamming schemes with
distinct alphabets; and the transitivity proved here is that scheme's classes being contained in the
automorphism group's orbitals. Those names belong in a spec entry citing the known setting, and nothing above is
claimed as new relative to them.

WHAT REMAINS OPEN

1. Invariance of the typed count at arbitrary distance, hence the identification of the orbit partition. The
   first-step route above is the concrete next step.
2. Nothing here is graduated. -/

#print axioms diffSet
#print axioms mem_diffSet
#print axioms diffSet_eq_empty_iff
#print axioms differsInOne_iff_diffSet
#print axioms CrossStable
#print axioms exists_differsInOne_iff_card
#print axioms crossStable_of_diffSet_perm
#print axioms SameOrbit
#print axioms crossStable_trans
#print axioms sameOrbit_trans
#print axioms exists_equiv_pair
#print axioms movePair
#print axioms movePair_spec_ne
#print axioms movePair_spec_eq
#print axioms fibEquiv
#print axioms diffSet_fibEquiv
#print axioms fibEquiv_crossStable
#print axioms sameOrbit_of_same_diffSet
#print axioms swapT
#print axioms swapT_i
#print axioms swapT_j
#print axioms swapT_other
#print axioms swapT_involutive
#print axioms coordSwapT
#print axioms mem_diffSet_swapT
#print axioms diffSet_swapT
#print axioms coordSwapT_crossStable
#print axioms typedCount
#print axioms sizes
#print axioms plain_from_typed
#print axioms typedCount_swapT
#print axioms sdiff_after_swapT
#print axioms sameOrbit_of_same_typedCount_aux
#print axioms sameOrbit_of_same_typedCount
#print axioms structural_labels_coarsen_typedCount

end Chiralogy.TypedCountTransitivity
