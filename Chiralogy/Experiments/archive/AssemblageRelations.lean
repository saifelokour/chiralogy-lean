import Chiralogy.Experiments.archive.AssemblageDynamics

/-! # Experiment (ARCHIVED after graduation pass 5): the relations among an assemblage's parts

ARCHIVED. Both relation groups are canonical in `Model/AssemblageRelations`: the n-ary relations (pass 4) and the
BINARY relations (`IsFactor1B`/`IsFactor2B` and their `_unique`/`_not_unique`/`_of_assemble`/`_transport_totalization`/
`_presence_immune`/`_absence_immune`, plus `nested_factor_reads`) in pass 5. Nothing graduate-worthy remains. Kept
as a standalone record, namespaced `Chiralogy.AssemblageRelations`.

The kernel Hom does NOT reach assemblage factors (factors are bare classifications, not `Obj`; `Member` has no
morphism notion). So these relations are NOT morphisms. They are defined here as PREDICATES from existing
machinery (`isAssemblageN`, `nary`, `nary_apply_differ`, the move results), then tested.

GRADUATED (group 4 of 5, the relations group) to the new canonical module `Model/AssemblageRelations`
(`namespace Chiralogy`), verbatim under the same names: the predicates `IsFactorAt`, `IsFactorOf`, `ArePeersIn`;
the basic facts `IsFactorAt_of_nary`, `IsFactorAt_offdiag_unique`, `ArePeersIn_symm`, `ArePeersIn_irrefl`; the
hinge `IsFactorAt_imp_region_independent`; transport `IsFactorAt_transport_totalization`,
`ArePeersIn_transport_totalization`; the immunities `presence_carried_factor_immune_to_scale`,
`absence_carried_factor_immune_to_mask`; and the witnesses `IsFactorAt_not_unique`, `peers_can_be_equal`,
`incoherent_scale_no_factor`, `incoherent_mask_no_factor`. NOT graduated here (pass-5 binary material, they hook
`assembleClassify`): `nested_factor_reads` (a nested product), and the whole `IsFactor1B`/`IsFactor2B` block
(`_unique`, `_not_unique`, `_of_assemble`, `_transport_totalization`, `_presence_immune`, `_absence_immune`).
These stay live below. This file is NOT archived: it holds the pass-5 binary relations. -/

open Chiralogy Chiralogy.InformationOrder Chiralogy.AssemblageDynamics

namespace Chiralogy.AssemblageRelations

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-! ## Part 1: the relations, as predicates -/

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

/-- Binary factor-1: read on the shared-second-coordinate region (includes the diagonal). -/
def IsFactor1B {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (A : (X1 × X2) → (X1 × X2) → Option Bool) (c1 : X1 → X1 → Option Bool) : Prop :=
  ∀ a b : X1 × X2, a.2 = b.2 → c1 a.1 b.1 = A a b

/-- Binary factor-2: read on the shared-first-coordinate region, which EXCLUDES the diagonal (`a.2 ≠ b.2`). -/
def IsFactor2B {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (A : (X1 × X2) → (X1 × X2) → Option Bool) (c2 : X2 → X2 → Option Bool) : Prop :=
  ∀ a b : X1 × X2, a.1 = b.1 → a.2 ≠ b.2 → c2 a.2 b.2 = A a b

/-! ## Part 2: properties -/

/-- The factors of a `nary` are its factors. -/
theorem IsFactorAt_of_nary (i : Fin n) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) : IsFactorAt i (nary c imp) (c i) :=
  fun a b hd => (nary_apply_differ c imp hd).symm

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

/-- **The factor at a coordinate is NOT unique**: the diagonal is free. Two classifications differing only on
the diagonal are both the factor at coordinate 0. -/
theorem IsFactorAt_not_unique :
    ∃ (A : (∀ _ : Fin 2, Fin 2) → (∀ _ : Fin 2, Fin 2) → Option Bool)
      (c c' : Fin 2 → Fin 2 → Option Bool), IsFactorAt 0 A c ∧ IsFactorAt 0 A c' ∧ c ≠ c' := by
  refine ⟨nary (fun _ => fun _ _ => none) (fun _ _ => none), (fun _ _ => none),
    (fun x y => if x = y then some true else none), ?_, ?_, by decide⟩
  · intro a b hd; rw [nary_apply_differ _ _ hd]
  · intro a b hd; rw [nary_apply_differ _ _ hd]; simp [hd.1]

/-- **Binary factor-1 is fully unique** (its diagonal is pinned, unlike the n-ary): the shared-second region
includes the diagonal. -/
theorem IsFactor1B_unique {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2] [Inhabited X2]
    (A : (X1 × X2) → (X1 × X2) → Option Bool) (c1 c1' : X1 → X1 → Option Bool)
    (h : IsFactor1B A c1) (h' : IsFactor1B A c1') : c1 = c1' := by
  funext x1 y1
  rw [h (x1, default) (y1, default) rfl, h' (x1, default) (y1, default) rfl]

/-- **Binary factor-2 is NOT unique**: its diagonal is free, since the region excludes it. So the `a.2`-first
artifact makes coordinate 1 more determined than coordinate 2. -/
theorem IsFactor2B_not_unique :
    ∃ (A : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool) (c2 c2' : Fin 2 → Fin 2 → Option Bool),
      IsFactor2B A c2 ∧ IsFactor2B A c2' ∧ c2 ≠ c2' := by
  refine ⟨assembleClassify (fun _ _ => none) (fun x y => if x = y then some true else none)
      (fun _ _ => none), (fun _ _ => none), (fun x y => if x = y then some true else none), ?_, ?_, by decide⟩
  · unfold IsFactor2B; decide
  · unfold IsFactor2B; decide

/-- **`ArePeersIn` is symmetric**, in both settings: swapping the two factors and their coordinates. The
`a.2`-first artifact does not reach peer-symmetry. -/
theorem ArePeersIn_symm (A : (∀ k, X k) → (∀ k, X k) → Option Bool) (i j : Fin n)
    (c : X i → X i → Option Bool) (c' : X j → X j → Option Bool)
    (h : ArePeersIn A i j c c') : ArePeersIn A j i c' c :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

/-- `ArePeersIn` is irreflexive on coordinates (distinct coordinates required). -/
theorem ArePeersIn_irrefl (A : (∀ k, X k) → (∀ k, X k) → Option Bool) (i : Fin n)
    (c c' : X i → X i → Option Bool) : ¬ ArePeersIn A i i c c' := fun h => h.1 rfl

/-- **Peers at distinct coordinates can be equal as classifications** (when the coordinate types match). -/
theorem peers_can_be_equal :
    ∃ (A : (∀ _ : Fin 2, Fin 2) → (∀ _ : Fin 2, Fin 2) → Option Bool) (c : Fin 2 → Fin 2 → Option Bool),
      ArePeersIn A 0 1 c c := by
  refine ⟨nary (fun _ => fun _ _ => none) (fun _ _ => none), (fun _ _ => none),
    by decide, ?_, ?_⟩
  · intro a b hd; rw [nary_apply_differ _ _ hd]
  · intro a b hd; rw [nary_apply_differ _ _ hd]

/-! ## Part 3: behaviour under the moves -/

/-- A factor forces region-independence of `A` at its coordinate. -/
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

/-- **Under an incoherent scale the relation goes vacuous**: the broken coordinate has NO factor, because
`IsFactorAt` forces region-independence, which the incoherent fill destroys. -/
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

/-- **Duality, presence side: a present-carried factor is immune to an incoherent scale.** If the factor at `i`
is total, `IsFactorAt` at `i` survives totalization by ANY scale, since totalization never touches present
cells. -/
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
is all-absent, `IsFactorAt` at `i` survives partialization by ANY mask, since partialization never touches
absent cells. -/
theorem absence_carried_factor_immune_to_mask (i : Fin n) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (w : (∀ i, X i) → (∀ i, X i) → Bool)
    (hc : c i = fun _ _ => none) :
    IsFactorAt i (partialization w (nary c imp)) (fun _ _ => none) := by
  intro a b hd
  simp only [partialization]
  rw [nary_apply_differ c imp hd, hc]
  split <;> rfl

/-! ## (1) The dual partialization vacuity -/

/-- **Under an incoherent mask the relation goes vacuous too** (dual to `incoherent_scale_no_factor`): a mask
reading the wrong coordinate breaks region-0 independence, so coordinate 0 has NO factor. Stated in the same
shape as the totalization case. -/
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

/-! ## (2) Binary transport and duality, per coordinate -/

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

/-- **Presence immunity, factor 2 (lifted to the minimal hypothesis).** Needs presence only OFF the diagonal,
which is the only region factor-2 reads. Strictly weaker than the full-presence form, and this is the honest
generality: factor-2's diagonal is free, so its diagonal presence is irrelevant. -/
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

/-! ## (3) Transitivity at the nesting layer

Flat "factor of" is terminal by types (a nested `B = A ⊗ c3` has factor-1 the whole `A`, type
`(X1 × X2) → (X1 × X2) → Option Bool`, not `c1`'s type `X1 → X1 → Option Bool`). But the READING composes: on
the region where the two OTHER coordinates agree, `B` reads `c1`. That is what survives, with no new notion. -/

/-- **The reading composes.** In a left-nested assemblage `B = (c1 ⊗ c2) ⊗ c3`, on cells where the `X3` and `X2`
coordinates both agree, `B` reads exactly `c1`. So `c1` is recoverable from `B` at the composed `X1`-coordinate,
even though the flat `IsFactor1B B c1` does not typecheck. -/
theorem nested_factor_reads {X1 X2 X3 : Type} [DecidableEq X1] [DecidableEq X2] [DecidableEq X3]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool) (c3 : X3 → X3 → Option Bool)
    (imp12 : (X1 × X2) → (X1 × X2) → Option Bool)
    (imp123 : ((X1 × X2) × X3) → ((X1 × X2) × X3) → Option Bool)
    (a b : (X1 × X2) × X3) (h3 : a.2 = b.2) (h2 : a.1.2 = b.1.2) :
    assembleClassify (assembleClassify c1 c2 imp12) c3 imp123 a b = c1 a.1.1 b.1.1 := by
  rw [(factors_determine_the_shared_region (assembleClassify c1 c2 imp12) c3 imp123 a b).1 h3,
    (factors_determine_the_shared_region c1 c2 imp12 a.1 b.1).1 h2]

end Chiralogy.AssemblageRelations
