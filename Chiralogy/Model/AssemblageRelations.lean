import Chiralogy.Model.NaryAssemblage

/-! # The relations among an assemblage's parts

The kernel Hom does NOT reach assemblage factors: factors are bare classifications, not `Obj`, and `Member` has
no morphism notion. So the relations among an assemblage's parts are NOT morphisms. They are PREDICATES built
from the n-ary machinery (`nary`, `differsInOne`, `nary_apply_differ`): `IsFactorAt i A c` (the factor at a
coordinate, coordinate-indexed by necessity) and `ArePeersIn` (factors at distinct coordinates). A factor forces
region-independence at its coordinate (`IsFactorAt_imp_region_independent`), which drives transport under
coherent moves, vacuity under incoherent ones, and the presence/absence immunity duality.

Depends on `Model/NaryAssemblage` (and thereby `Model/InformationOrder`, `Model/Apophatic`); no dependence on the
ordered binary `Model/Assemblage`. -/

namespace Chiralogy

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-! ## The predicates -/

/-- **`c` is the factor at coordinate `i` of `A`.** The honest primitive: `c` agrees with `A`'s reading on every
differ-in-`i` pair. This pins `c` off its diagonal only, which is exactly what `nary_apply_differ` supplies. -/
def IsFactorAt (i : Fin n) (A : (∀ k, X k) → (∀ k, X k) → Option Bool) (c : X i → X i → Option Bool) : Prop :=
  ∀ a b : ∀ k, X k, differsInOne a b i → c (a i) (b i) = A a b

/-- `c` is a factor of `A` at some coordinate. Derived from the coordinate-indexed primitive. -/
def IsFactorOf (A : (∀ k, X k) → (∀ k, X k) → Option Bool)
    (i : Fin n) (c : X i → X i → Option Bool) : Prop := IsFactorAt i A c

/-- `c` and `c'` are peers: factors of the same `A` at distinct coordinates. -/
def ArePeersIn (A : (∀ k, X k) → (∀ k, X k) → Option Bool) (i j : Fin n)
    (c : X i → X i → Option Bool) (c' : X j → X j → Option Bool) : Prop :=
  i ≠ j ∧ IsFactorAt i A c ∧ IsFactorAt j A c'

/-! ## Basic facts -/

/-- The factors of a `nary` are its factors. -/
theorem IsFactorAt_of_nary (i : Fin n) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) : IsFactorAt i (nary c imp) (c i) :=
  fun _ _ hd => (nary_apply_differ c imp hd).symm

omit [∀ i, DecidableEq (X i)] in
/-- **Off-diagonal the factor is unique**: two factors at `i` agree wherever the coordinate values differ. -/
theorem IsFactorAt_offdiag_unique [∀ j, Inhabited (X j)] (i : Fin n)
    (A : (∀ k, X k) → (∀ k, X k) → Option Bool) (c c' : X i → X i → Option Bool)
    (h : IsFactorAt i A c) (h' : IsFactorAt i A c') (x y : X i) (hxy : x ≠ y) : c x y = c' x y := by
  have hd : differsInOne (Function.update (fun _ => default) i x)
      (Function.update (fun _ => default) i y) i := by
    refine ⟨?_, fun k hk => ?_⟩
    · simp only [Function.update_self]; exact hxy
    · simp only [Function.update_of_ne hk]
  have e1 := h _ _ hd
  have e2 := h' _ _ hd
  simp only [Function.update_self] at e1 e2
  rw [e1, e2]

/-- **The factor at a coordinate is NOT unique** (witness): the diagonal is free. Two classifications differing
only on the diagonal are both the factor at coordinate 0. -/
theorem IsFactorAt_not_unique :
    ∃ (A : (∀ _ : Fin 2, Fin 2) → (∀ _ : Fin 2, Fin 2) → Option Bool)
      (c c' : Fin 2 → Fin 2 → Option Bool), IsFactorAt 0 A c ∧ IsFactorAt 0 A c' ∧ c ≠ c' := by
  refine ⟨nary (fun _ => fun _ _ => none) (fun _ _ => none), (fun _ _ => none),
    (fun x y => if x = y then some true else none), ?_, ?_, by decide⟩
  · intro a b hd; rw [nary_apply_differ _ _ hd]
  · intro a b hd; rw [nary_apply_differ _ _ hd]; simp [hd.1]

omit [∀ i, DecidableEq (X i)] in
/-- **`ArePeersIn` is symmetric**: swapping the two factors and their coordinates. -/
theorem ArePeersIn_symm (A : (∀ k, X k) → (∀ k, X k) → Option Bool) (i j : Fin n)
    (c : X i → X i → Option Bool) (c' : X j → X j → Option Bool)
    (h : ArePeersIn A i j c c') : ArePeersIn A j i c' c :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

omit [∀ i, DecidableEq (X i)] in
/-- `ArePeersIn` is irreflexive on coordinates (distinct coordinates required). -/
theorem ArePeersIn_irrefl (A : (∀ k, X k) → (∀ k, X k) → Option Bool) (i : Fin n)
    (c c' : X i → X i → Option Bool) : ¬ ArePeersIn A i i c c' := fun h => h.1 rfl

/-- **Peers at distinct coordinates can be equal as classifications** (witness), when the coordinate types match. -/
theorem peers_can_be_equal :
    ∃ (A : (∀ _ : Fin 2, Fin 2) → (∀ _ : Fin 2, Fin 2) → Option Bool) (c : Fin 2 → Fin 2 → Option Bool),
      ArePeersIn A 0 1 c c := by
  refine ⟨nary (fun _ => fun _ _ => none) (fun _ _ => none), (fun _ _ => none),
    by decide, ?_, ?_⟩
  · intro a b hd; rw [nary_apply_differ _ _ hd]
  · intro a b hd; rw [nary_apply_differ _ _ hd]

/-! ## The hinge, transport, and the immunity duality -/

omit [∀ i, DecidableEq (X i)] in
/-- **A factor forces region-independence of `A` at its coordinate.** The hinge for transport, vacuity, and both
immunities. -/
theorem IsFactorAt_imp_region_independent (i : Fin n) (A : (∀ k, X k) → (∀ k, X k) → Option Bool)
    (c : X i → X i → Option Bool) (h : IsFactorAt i A c) {a b a' b' : ∀ k, X k}
    (hd : differsInOne a b i) (hd' : differsInOne a' b' i) (hai : a i = a' i) (hbi : b i = b' i) :
    A a b = A a' b' := by
  rw [← h a b hd, ← h a' b' hd', hai, hbi]

/-- **`IsFactorAt` transports under a region-coherent totalization**: the moved factor is the factor at `i` of
the moved composite. -/
theorem IsFactorAt_transport_totalization (i : Fin n) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (hs : ∀ a b : ∀ i, X i, ∀ hex : ∃ i, differsInOne a b i,
      decide (s b ≤ s a) = decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose))) :
    IsFactorAt i (totalization s (nary c imp)) (totalization (si i) (c i)) := by
  rw [nary_totalization_commutes s si c imp hs]
  exact IsFactorAt_of_nary i (fun i => totalization (si i) (c i)) (totalization s imp)

/-- `ArePeersIn` transports under a region-coherent totalization. -/
theorem ArePeersIn_transport_totalization (i j : Fin n) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (hij : i ≠ j)
    (hs : ∀ a b : ∀ i, X i, ∀ hex : ∃ i, differsInOne a b i,
      decide (s b ≤ s a) = decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose))) :
    ArePeersIn (totalization s (nary c imp)) i j (totalization (si i) (c i)) (totalization (si j) (c j)) :=
  ⟨hij, IsFactorAt_transport_totalization i c imp s si hs,
    IsFactorAt_transport_totalization j c imp s si hs⟩

/-- **Under an incoherent scale the relation goes vacuous** (witness): the broken coordinate has NO factor,
because `IsFactorAt` forces region-independence, which the incoherent fill destroys. -/
theorem incoherent_scale_no_factor :
    ∃ (c : ∀ _ : Fin 2, Fin 2 → Fin 2 → Option Bool)
      (imp : (∀ _ : Fin 2, Fin 2) → (∀ _ : Fin 2, Fin 2) → Option Bool)
      (s : (∀ _ : Fin 2, Fin 2) → Nat),
      ¬ ∃ c₀, IsFactorAt 0 (totalization s (nary c imp)) c₀ := by
  refine ⟨fun _ => fun _ _ => none, fun _ _ => none, fun p => (p 0).val * (p 1).val, ?_⟩
  rintro ⟨c₀, h⟩
  have hd : differsInOne (![0, 0] : ∀ _ : Fin 2, Fin 2) ![1, 0] 0 := by decide
  have hd' : differsInOne (![0, 1] : ∀ _ : Fin 2, Fin 2) ![1, 1] 0 := by decide
  have hreg := IsFactorAt_imp_region_independent 0 _ c₀ h hd hd' (by decide) (by decide)
  revert hreg
  simp only [totalization]
  rw [nary_apply_differ _ _ hd, nary_apply_differ _ _ hd']
  decide

/-- **Under an incoherent mask the relation goes vacuous too** (witness, dual to `incoherent_scale_no_factor`):
a mask reading the wrong coordinate breaks region-0 independence, so coordinate 0 has NO factor. -/
theorem incoherent_mask_no_factor :
    ∃ (c : ∀ _ : Fin 2, Fin 2 → Fin 2 → Option Bool)
      (imp : (∀ _ : Fin 2, Fin 2) → (∀ _ : Fin 2, Fin 2) → Option Bool)
      (w : (∀ _ : Fin 2, Fin 2) → (∀ _ : Fin 2, Fin 2) → Bool),
      ¬ ∃ c₀, IsFactorAt 0 (partialization w (nary c imp)) c₀ := by
  refine ⟨fun _ => fun _ _ => some true, fun _ _ => none, fun a _ => decide (a 1 = 0), ?_⟩
  rintro ⟨c₀, h⟩
  have hd : differsInOne (![0, 0] : ∀ _ : Fin 2, Fin 2) ![1, 0] 0 := by decide
  have hd' : differsInOne (![0, 1] : ∀ _ : Fin 2, Fin 2) ![1, 1] 0 := by decide
  have hreg := IsFactorAt_imp_region_independent 0 _ c₀ h hd hd' (by decide) (by decide)
  revert hreg
  simp only [partialization]
  rw [nary_apply_differ _ _ hd, nary_apply_differ _ _ hd']
  decide

/-- **Duality, presence side: a present-carried factor is immune to an incoherent scale.** If the factor at `i`
is total, `IsFactorAt` at `i` survives totalization by ANY scale, since totalization never touches present cells. -/
theorem presence_carried_factor_immune_to_scale (i : Fin n) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (s : (∀ i, X i) → Nat) (hc : isTotal (c i)) :
    IsFactorAt i (totalization s (nary c imp)) (c i) := by
  intro a b hd
  simp only [totalization]
  rw [nary_apply_differ c imp hd]
  rcases hcv : c i (a i) (b i) with _ | v
  · exact absurd hcv (hc (a i) (b i))
  · simp [Option.getD_some]

/-- **Duality, absence side: an absence-carried factor is immune to an incoherent mask.** If the factor at `i`
is all-absent, `IsFactorAt` at `i` survives partialization by ANY mask, since partialization never touches absent
cells. -/
theorem absence_carried_factor_immune_to_mask (i : Fin n) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (w : (∀ i, X i) → (∀ i, X i) → Bool)
    (hc : c i = fun _ _ => none) :
    IsFactorAt i (partialization w (nary c imp)) (fun _ _ => none) := by
  intro a b hd
  simp only [partialization]
  rw [nary_apply_differ c imp hd, hc]
  split <;> rfl

end Chiralogy
