import Chiralogy.Model.NaryAssemblage
import Chiralogy.Model.AssemblageDynamics

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

/-! ## The binary relations

For the ordered binary `assembleClassify` (Model/Assemblage), the factor predicates read on the two regions.
Factor-1's region includes the diagonal (so it is fully unique); factor-2's excludes it (so its diagonal is
free): the `a.2`-first artifact makes coordinate 1 more determined than coordinate 2. Both transport under a
region-coherent totalization and enjoy the presence/absence immunities. -/

/-- Binary factor-1: read on the shared-second-coordinate region (includes the diagonal). -/
def IsFactor1B {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (A : (X1 × X2) → (X1 × X2) → Option Bool) (c1 : X1 → X1 → Option Bool) : Prop :=
  ∀ a b : X1 × X2, a.2 = b.2 → c1 a.1 b.1 = A a b

/-- Binary factor-2: read on the shared-first-coordinate region, which EXCLUDES the diagonal (`a.2 ≠ b.2`). -/
def IsFactor2B {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (A : (X1 × X2) → (X1 × X2) → Option Bool) (c2 : X2 → X2 → Option Bool) : Prop :=
  ∀ a b : X1 × X2, a.1 = b.1 → a.2 ≠ b.2 → c2 a.2 b.2 = A a b

/-- Binary factors are factors of the assemblage (factor 1). -/
theorem IsFactor1B_of_assemble {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) : IsFactor1B (assembleClassify c1 c2 imp) c1 :=
  fun a b h => ((factors_determine_the_shared_region c1 c2 imp a b).1 h).symm

/-- Binary factors are factors of the assemblage (factor 2). -/
theorem IsFactor2B_of_assemble {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) : IsFactor2B (assembleClassify c1 c2 imp) c2 :=
  fun a b h1 h2 => ((factors_determine_the_shared_region c1 c2 imp a b).2 h1 h2).symm

/-- **Binary factor-1 is fully unique** (its diagonal is pinned, unlike the n-ary): the shared-second region
includes the diagonal. -/
theorem IsFactor1B_unique {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2] [Inhabited X2]
    (A : (X1 × X2) → (X1 × X2) → Option Bool) (c1 c1' : X1 → X1 → Option Bool)
    (h : IsFactor1B A c1) (h' : IsFactor1B A c1') : c1 = c1' := by
  funext x1 y1
  rw [h (x1, default) (y1, default) rfl, h' (x1, default) (y1, default) rfl]

/-- **Binary factor-2 is NOT unique** (witness): its diagonal is free. So the `a.2`-first artifact makes
coordinate 1 more determined than coordinate 2. -/
theorem IsFactor2B_not_unique :
    ∃ (A : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool) (c2 c2' : Fin 2 → Fin 2 → Option Bool),
      IsFactor2B A c2 ∧ IsFactor2B A c2' ∧ c2 ≠ c2' := by
  refine ⟨assembleClassify (fun _ _ => none) (fun x y => if x = y then some true else none)
      (fun _ _ => none), (fun _ _ => none), (fun x y => if x = y then some true else none), ?_, ?_, by decide⟩
  · unfold IsFactor2B; decide
  · unfold IsFactor2B; decide

/-- **Factor-1 transports under a region-coherent totalization.** -/
theorem IsFactor1B_transport_totalization {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (s : X1 × X2 → Nat) (s1 : X1 → Nat) (s2 : X2 → Nat) (c1 : X1 → X1 → Option Bool)
    (c2 : X2 → X2 → Option Bool) (imp : (X1 × X2) → (X1 × X2) → Option Bool)
    (hs1 : ∀ a b : X1 × X2, a.2 = b.2 → decide (s b ≤ s a) = decide (s1 b.1 ≤ s1 a.1))
    (hs2 : ∀ a b : X1 × X2, a.2 ≠ b.2 → a.1 = b.1 → decide (s b ≤ s a) = decide (s2 b.2 ≤ s2 a.2)) :
    IsFactor1B (totalization s (assembleClassify c1 c2 imp)) (totalization s1 c1) := by
  rw [totalization_commutes s s1 s2 c1 c2 imp hs1 hs2]
  exact IsFactor1B_of_assemble (totalization s1 c1) (totalization s2 c2) (totalization s imp)

/-- **Factor-2 transports identically**: the same coherent move, the same transport. -/
theorem IsFactor2B_transport_totalization {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (s : X1 × X2 → Nat) (s1 : X1 → Nat) (s2 : X2 → Nat) (c1 : X1 → X1 → Option Bool)
    (c2 : X2 → X2 → Option Bool) (imp : (X1 × X2) → (X1 × X2) → Option Bool)
    (hs1 : ∀ a b : X1 × X2, a.2 = b.2 → decide (s b ≤ s a) = decide (s1 b.1 ≤ s1 a.1))
    (hs2 : ∀ a b : X1 × X2, a.2 ≠ b.2 → a.1 = b.1 → decide (s b ≤ s a) = decide (s2 b.2 ≤ s2 a.2)) :
    IsFactor2B (totalization s (assembleClassify c1 c2 imp)) (totalization s2 c2) := by
  rw [totalization_commutes s s1 s2 c1 c2 imp hs1 hs2]
  exact IsFactor2B_of_assemble (totalization s1 c1) (totalization s2 c2) (totalization s imp)

/-- **Presence immunity, factor 1**: a present factor-1 survives any scale. -/
theorem IsFactor1B_presence_immune {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (s : X1 × X2 → Nat) (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (hc : ∀ x y, c1 x y ≠ none) :
    IsFactor1B (totalization s (assembleClassify c1 c2 imp)) c1 := by
  intro a b h
  simp only [totalization]
  rw [(factors_determine_the_shared_region c1 c2 imp a b).1 h]
  rcases hcv : c1 a.1 b.1 with _ | v
  · exact absurd hcv (hc a.1 b.1)
  · simp [Option.getD_some]

/-- **Presence immunity, factor 2 (minimal hypothesis).** Needs presence only OFF the diagonal, the only region
factor-2 reads: factor-2's diagonal is free, so its diagonal presence is irrelevant. -/
theorem IsFactor2B_presence_immune {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (s : X1 × X2 → Nat) (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (hc : ∀ x y, x ≠ y → c2 x y ≠ none) :
    IsFactor2B (totalization s (assembleClassify c1 c2 imp)) c2 := by
  intro a b h1 h2
  simp only [totalization]
  rw [(factors_determine_the_shared_region c1 c2 imp a b).2 h1 h2]
  rcases hcv : c2 a.2 b.2 with _ | v
  · exact absurd hcv (hc a.2 b.2 h2)
  · simp [Option.getD_some]

/-- **Absence immunity, factor 1**: an all-absent factor-1 survives any mask. -/
theorem IsFactor1B_absence_immune {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (w : (X1 × X2) → (X1 × X2) → Bool) (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (hc : c1 = fun _ _ => none) :
    IsFactor1B (partialization w (assembleClassify c1 c2 imp)) (fun _ _ => none) := by
  intro a b h
  simp only [partialization]
  rw [(factors_determine_the_shared_region c1 c2 imp a b).1 h, hc]
  split <;> rfl

/-- **Absence immunity, factor 2**: symmetric. -/
theorem IsFactor2B_absence_immune {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (w : (X1 × X2) → (X1 × X2) → Bool) (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (hc : c2 = fun _ _ => none) :
    IsFactor2B (partialization w (assembleClassify c1 c2 imp)) (fun _ _ => none) := by
  intro a b h1 h2
  simp only [partialization]
  rw [(factors_determine_the_shared_region c1 c2 imp a b).2 h1 h2, hc]
  split <;> rfl

/-- **The reading composes at the nesting layer.** Flat "factor of" is terminal by types (a nested
`B = (c1 ⊗ c2) ⊗ c3` has factor-1 the whole `c1 ⊗ c2`, not `c1`). But on cells where the `X3` and `X2`
coordinates both agree, `B` reads exactly `c1`: `c1` is recoverable from `B` at the composed `X1`-coordinate. -/
theorem nested_factor_reads {X1 X2 X3 : Type} [DecidableEq X1] [DecidableEq X2] [DecidableEq X3]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool) (c3 : X3 → X3 → Option Bool)
    (imp12 : (X1 × X2) → (X1 × X2) → Option Bool)
    (imp123 : ((X1 × X2) × X3) → ((X1 × X2) × X3) → Option Bool)
    (a b : (X1 × X2) × X3) (h3 : a.2 = b.2) (h2 : a.1.2 = b.1.2) :
    assembleClassify (assembleClassify c1 c2 imp12) c3 imp123 a b = c1 a.1.1 b.1.1 := by
  rw [(factors_determine_the_shared_region (assembleClassify c1 c2 imp12) c3 imp123 a b).1 h3,
    (factors_determine_the_shared_region c1 c2 imp12 a.1 b.1).1 h2]

/-! ## Absence carried through the import order

The framework's present-and-absence distinction re-enters at the import: present-carriage is monotone upward,
so the imports leaving a distinction absence-carried are closed downward. This is where the two branches meet,
which is why it sits here and not with either alone. -/

/-- **Present-carriage is monotone.** A distinction carried by presence survives every step upward in the
order, because the witnessing cells are present and presence is preserved upward. -/
theorem presentCarried_mono {Y : Type} {A B : Y → Y → Option Bool} (h : cLE A B) {x x' : Y}
    (hp : presentCarried A x x') : presentCarried B x x' := by
  obtain ⟨z, b, b', h1, h2, hb⟩ := hp
  refine ⟨z, b, b', ?_, ?_, hb⟩
  · rcases h x z with hc | hc
    · exact absurd hc (by rw [h1]; exact Option.some_ne_none b)
    · rw [← hc, h1]
  · rcases h x' z with hc | hc
    · exact absurd hc (by rw [h2]; exact Option.some_ne_none b')
    · rw [← hc, h2]

/-- **The absence-carried imports are downward closed.** At any fixed pair of assembly points, the imports
leaving that distinction absence-carried form a downward-closed subset of the import order. So the split of the
free region by carriage is order-theoretic, not arbitrary. -/
theorem absence_carried_downward_closed (c : ∀ i, X i → X i → Option Bool) (a a' : ∀ i, X i)
    (imp imp' : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (hle : ∀ p q, IsCross p q → optLE (imp p q) (imp' p q))
    (h : ¬ presentCarried (nary c imp') a a') : ¬ presentCarried (nary c imp) a a' :=
  fun hp => h (presentCarried_mono ((import_order_embeds c imp imp').2 hle) hp)

/-- **An absent factor hands its coordinate's carriage to the import.** If the factor at coordinate `i`
abstains off its diagonal, then over the empty import no distinction differing at that coordinate is
present-carried: the cross carriage is the import's to supply. -/
theorem cross_absence_carried_of_absent_factor (c : ∀ i, X i → X i → Option Bool) (i : Fin n)
    (habs : ∀ x y, x ≠ y → c i x y = none) (a a' : ∀ k, X k) (hne : a i ≠ a' i) :
    ¬ presentCarried (nary c (botC (∀ k, X k))) a a' := by
  rintro ⟨b, v, v', h1, h2, _⟩
  have e1 := present_forces_coord_eq c i habs a b (by rw [h1]; exact Option.some_ne_none v)
  have e2 := present_forces_coord_eq c i habs a' b (by rw [h2]; exact Option.some_ne_none v')
  exact hne (e1.trans e2.symm)

/-! ## The structure of variance

The free region is a faithful order-copy of the classification space, one level in. The embedding half lives in
`Model/NaryAssemblage`, where it needs nothing from the absence shelf; the carriage clause needs
`presentCarried`, so the whole statement lands here, in the first module that sees both branches. -/

/-- **THE STRUCTURE OF VARIANCE.** For fixed factors over an arbitrary finite product carrier, the import map is
a meet-embedding with kernel exactly cross-agreement, injective on cross-supported representatives, whose image
carries the classification order's own shape: a bottom, that bottom alone, plural incomparable maxima, and a
downward-closed present-and-absence split. Variance is not a second axis; it is the same structure re-entering
at the cross region. The generality minimum over the clauses is `Inhabited` fibres, contributed by the maxima
clause alone. -/
theorem structure_of_variance [∀ i, Inhabited (X i)] (c : ∀ i, X i → X i → Option Bool) :
    ((∀ imp imp' : Pt X → Pt X → Option Bool,
        cLE (importMap c imp) (importMap c imp') ↔ ∀ a b, IsCross a b → optLE (imp a b) (imp' a b))
      ∧ (∀ imp imp' : Pt X → Pt X → Option Bool,
        importMap c (cMeet imp imp') = cMeet (importMap c imp) (importMap c imp'))
      ∧ (∀ imp imp' : Pt X → Pt X → Option Bool,
        importMap c imp = importMap c imp' ↔ ∀ a b, IsCross a b → imp a b = imp' a b)
      ∧ (∀ imp imp' : Pt X → Pt X → Option Bool,
        CrossSupported imp → CrossSupported imp' → importMap c imp = importMap c imp' → imp = imp'))
    ∧ ((∀ imp : Pt X → Pt X → Option Bool, cLE (importMap c (botC (Pt X))) (importMap c imp))
      ∧ (∀ imp : Pt X → Pt X → Option Bool,
          cLE (importMap c imp) (importMap c (botC (Pt X))) → ∀ a b, IsCross a b → imp a b = none)
      ∧ (¬ cLE (importMap c cTrue) (importMap c cFalse) ∧ ¬ cLE (importMap c cFalse) (importMap c cTrue))
      ∧ (∀ (a a' : Pt X) (imp imp' : Pt X → Pt X → Option Bool),
          (∀ p q, IsCross p q → optLE (imp p q) (imp' p q)) →
          ¬ presentCarried (importMap c imp') a a' → ¬ presentCarried (importMap c imp) a a')) :=
  ⟨importMap_is_a_meet_embedding c,
   import_bottom c, bottom_is_unique c, maxima_are_plural c, absence_carried_downward_closed c⟩

/-! ### The one feature that is not a copy: the coordinate swap

Everything above says the free region reproduces the classification space's structure. The swap is the
exception, and it is a statement about the RELATION between the free and determined parts rather than structure
inside the free part. It lives on a homogeneous two-coordinate carrier, so it has its own section. -/

section Swap

variable {Y : Type} [DecidableEq Y]

abbrev TwoCoord (Y : Type) := ∀ _ : Fin 2, Y

theorem fin2_ne_iff : ∀ i j : Fin 2, j ≠ i ↔ j = i + 1 := by decide

theorem fin2_add_one_add_one (i : Fin 2) : i + 1 + 1 = i := by revert i; decide

/-- The coordinate swap on a homogeneous two-coordinate carrier. -/
def swapP (a : TwoCoord Y) : TwoCoord Y := fun i => a (i + 1)

omit [DecidableEq Y] in
theorem swapP_involutive (a : TwoCoord Y) : swapP (swapP a) = a := by
  funext i
  show a (i + 1 + 1) = a i
  rw [fin2_add_one_add_one]

omit [DecidableEq Y] in
theorem swapP_differsInOne (a b : TwoCoord Y) (i : Fin 2) :
    differsInOne (swapP a) (swapP b) i ↔ differsInOne a b (i + 1) := by
  constructor
  · rintro ⟨hne, hoth⟩
    refine ⟨hne, fun j hj => ?_⟩
    have hji : j = i := by rw [fin2_ne_iff] at hj; rw [hj, fin2_add_one_add_one]
    have hi : swapP a (i + 1) = swapP b (i + 1) := hoth (i + 1) (by rw [fin2_ne_iff])
    rw [hji]
    show a i = b i
    have hx : a (i + 1 + 1) = b (i + 1 + 1) := hi
    rwa [fin2_add_one_add_one] at hx
  · rintro ⟨hne, hoth⟩
    refine ⟨hne, fun j hj => ?_⟩
    show a (j + 1) = b (j + 1)
    refine hoth (j + 1) ?_
    rw [fin2_ne_iff] at hj ⊢
    rw [hj]

omit [DecidableEq Y] in
/-- **The swap fixes the cross region setwise**, so it acts on the import space. -/
theorem swap_fixes_cross (a b : TwoCoord Y) : IsCross a b ↔ IsCross (swapP a) (swapP b) := by
  constructor
  · rintro h ⟨i, hd⟩
    exact h ⟨i + 1, (swapP_differsInOne a b i).1 hd⟩
  · rintro h ⟨i, hd⟩
    refine h ⟨i + 1, (swapP_differsInOne a b (i + 1)).2 ?_⟩
    rwa [fin2_add_one_add_one]

/-- The swap's action on the import space. -/
def swapImp (imp : TwoCoord Y → TwoCoord Y → Option Bool) :
    TwoCoord Y → TwoCoord Y → Option Bool := fun a b => imp (swapP a) (swapP b)

/-- The swap's action on the factor family: it exchanges the two coordinates' factors. -/
def swapFactors (c : ∀ _ : Fin 2, Y → Y → Option Bool) : ∀ _ : Fin 2, Y → Y → Option Bool :=
  fun i => c (i + 1)

/-- **WHERE THE SWAP SITS.** It is not a symmetry of the assembly at fixed factors. It passes through only as a
transport law that SWAPS THE FACTORS: relabelling the assembly by the swap equals the assembly of the swapped
import under the swapped factors. So the swap relates the construction over one factor family to the
construction over another; it says something about the pair of parts, not about the free part alone. -/
theorem swap_transport (c : ∀ _ : Fin 2, Y → Y → Option Bool)
    (imp : TwoCoord Y → TwoCoord Y → Option Bool) :
    relabel swapP (nary c imp) = nary (swapFactors c) (swapImp imp) := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · obtain ⟨i, hd⟩ := hex
    have hd' : differsInOne (swapP a) (swapP b) (i + 1) :=
      (swapP_differsInOne a b (i + 1)).2 (by rwa [fin2_add_one_add_one])
    show nary c imp (swapP a) (swapP b) = nary (swapFactors c) (swapImp imp) a b
    rw [nary_apply_differ c imp hd', nary_apply_differ (swapFactors c) (swapImp imp) hd]
    show c (i + 1) (a (i + 1 + 1)) (b (i + 1 + 1)) = c (i + 1) (a i) (b i)
    rw [fin2_add_one_add_one]
  · have hc' : IsCross (swapP a) (swapP b) := (swap_fixes_cross a b).1 hex
    show nary c imp (swapP a) (swapP b) = nary (swapFactors c) (swapImp imp) a b
    rw [nary_apply_imp c imp hc', nary_apply_imp (swapFactors c) (swapImp imp) hex]
    rfl

end Swap

end Chiralogy
