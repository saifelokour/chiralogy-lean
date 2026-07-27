import Chiralogy.Model.AssemblageRelations

/-! ARCHIVED (fully graduated). The readiness pass's generalizations, which graduated to three different
modules once the graph placed them.

  invariant_scale_constant_G, forced_at_bottom_G, EquivariantG, determiner_output_invariant_G
      -> Model/InformationOrder as swap_invariant_scale_constant, fill_at_order_bottom_forced,
         EquivariantDeterminer, equivariant_determiner_invariant (spec 9.9)
  present_forces_coord_eq ................. Model/NaryAssemblage, same name (spec 9.12)
  cross_absence_carried_general ........... Model/AssemblageRelations as
         cross_absence_carried_of_absent_factor (spec 9.19)
  false_diagonal_survives_every_fill ...... Model/Moves, same name (spec 9.17), a placement correction:
         it reaches totalization and nothing above it

The generalized forms are what graduated; `ScaleIndependence`'s constant-carrier-map versions are superseded and
stay live only as the record of why the groupoid restriction mattered. Typechecks standalone. -/

/-! # Experiment (LIVE): the readiness pass for the physics and categorical arc

Step 2 of the readiness pass. This file holds ONLY the generalizations that the sort demanded: results that
sorted as graduates-candidates but were stated below the generality of the section they would join, or whose
formalization needed checking against a stricter symmetry.

Everything else in the arc either was already carrier-general in its own file, or sorted to archive or
stays-live and was deliberately not generalized.

Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.ArcReadiness

/-! ### GRADUATED (Model/InformationOrder pass)

Into `Model/InformationOrder`, renamed to drop the generalization suffix:

  EquivariantG .................... EquivariantDeterminer
  determiner_output_invariant_G ... equivariant_determiner_invariant
  invariant_scale_constant_G ...... swap_invariant_scale_constant
  forced_at_bottom_G .............. fill_at_order_bottom_forced

The remaining generalizations here (`false_diagonal_survives_every_fill`, `present_forces_coord_eq`,
`cross_absence_carried_general`) reach `nary` or `presentCarried` and go with the NaryAssemblage and
AssemblageRelations groups. -/

/-! ### GRADUATED (Model/NaryAssemblage pass)

Into `Model/NaryAssemblage`: `present_forces_coord_eq`, same name, in this generalized form rather than
`PhysicsImport`'s original.

PLACEMENT CORRECTION: `false_diagonal_survives_every_fill` went to `Model/Moves`, not here. It reaches
`totalization` and nothing above it, so the graph placed it with the moves.

REMAINING: `cross_absence_carried_general` reaches `presentCarried` and goes with the AssemblageRelations
group. -/

/-! ### GRADUATED (Model/AssemblageRelations pass)

Into `Model/AssemblageRelations`: `cross_absence_carried_general`, renamed
`cross_absence_carried_of_absent_factor`.

Every generalization in this file has now graduated, to three different modules. -/



/-! ## G1: the flagged check. Does the graded-determination forcing survive the GROUPOID?

`ScaleIndependence` proved the forcing using CONSTANT carrier maps, available only because the combined
category's arrows are arbitrary maps. The check: restrict to the relabelling GROUPOID, bijections only, and see
whether the forcing survives. -/

section Groupoid

variable {Y : Type}


/-- Equivariance with respect to the GROUPOID: only bijections are allowed to act. -/
def EquivariantG (D : (Y → Y → Option Bool) → (Y → Nat)) : Prop :=
  ∀ (e : Y ≃ Y) (A : Y → Y → Option Bool), D (relabel e A) = D A ∘ e

theorem determiner_output_invariant_G (D : (Y → Y → Option Bool) → (Y → Nat))
    (hD : EquivariantG D) (e : Y ≃ Y) (A : Y → Y → Option Bool) (hA : relabel e A = A) :
    D A ∘ e = D A := by
  rw [← hD e A, hA]

/-- **A TRANSPOSITION already collapses the scale.** Invariance under the two-element swaps alone forces a
scale to be constant, so the constant carrier maps `ScaleIndependence` used were not doing the work. -/
theorem invariant_scale_constant_G [DecidableEq Y] (s : Y → Nat)
    (h : ∀ e : Y ≃ Y, s ∘ e = s) (x y : Y) : s x = s y := by
  have hc : s (Equiv.swap x y x) = s x := congrFun (h (Equiv.swap x y)) x
  rw [Equiv.swap_apply_left] at hc
  exact hc.symm

/-- **THE CHECK, AND THE FORCING SURVIVES.** At the order bottom, which every relabelling fixes, every
groupoid-equivariant determiner outputs a constant scale and therefore the all-true fill. So the graded
determination law is not an artifact of allowing arbitrary carrier maps as arrows: bijections suffice. -/
theorem forced_at_bottom_G [DecidableEq Y] (D : (Y → Y → Option Bool) → (Y → Nat))
    (hD : EquivariantG D) :
    totalization (D (botC Y)) (botC Y) = fun _ _ => some true := by
  funext a b
  have hconst : ∀ x y : Y, D (botC Y) x = D (botC Y) y :=
    invariant_scale_constant_G _ (fun e => determiner_output_invariant_G D hD e (botC Y) rfl)
  simp only [totalization, botC, Option.getD_none]
  rw [hconst b a]
  simp

end Groupoid

/-! ## G4: the law behind the completeness-kills-content refutation

`PhysicsRegister` refuted "a complete theory is degenerate" with a `Fin 2` witness. The law behind it is
carrier-general: two rows carrying a FALSE verdict on their own diagonal and abstaining on the other's cannot
be merged by any fill, because a scale cannot order two points both ways. -/

theorem false_diagonal_survives_every_fill {Y : Type} (c : Y → Y → Option Bool) (x x' : Y)
    (hxx : c x x = some false) (hx'x : c x' x = none)
    (hx'x' : c x' x' = some false) (hxx' : c x x' = none) (s : Y → Nat) :
    totalization s c x ≠ totalization s c x' := by
  intro heq
  have e1 : (some ((c x x).getD (decide (s x ≤ s x))) : Option Bool)
      = some ((c x' x).getD (decide (s x ≤ s x'))) := congrFun heq x
  have e2 : (some ((c x x').getD (decide (s x' ≤ s x))) : Option Bool)
      = some ((c x' x').getD (decide (s x' ≤ s x'))) := congrFun heq x'
  rw [hxx, hx'x, Option.getD_some, Option.getD_none] at e1
  rw [hxx', hx'x', Option.getD_none, Option.getD_some] at e2
  have h1 : ¬ (s x ≤ s x') := by
    have := Option.some_inj.mp e1
    exact of_decide_eq_false this.symm
  have h2 : ¬ (s x' ≤ s x) := by
    have := Option.some_inj.mp e2
    exact of_decide_eq_false this
  omega

/-! ## G7: the absent-factor carriage law, lifted off `Fin 3` and off two coordinates

`PhysicsImport` proved that an absence-carried factor at one coordinate hands the cross carriage to the
import, on a two-coordinate three-point carrier. The general law holds at every `n` and every carrier. -/

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- **Presence forces agreement at the absent coordinate.** Over the empty import, if the factor at `i`
abstains off its diagonal, then wherever the composite holds a verdict the two points agree at `i`: the only
cells it holds are its own region-`i` cells at equal coordinate values, and there are none, plus the other
regions where agreement at `i` is forced by differ-in-one. -/
theorem present_forces_coord_eq (c : ∀ i, X i → X i → Option Bool) (i : Fin n)
    (habs : ∀ x y, x ≠ y → c i x y = none) (a b : ∀ k, X k)
    (h : nary c (botC (∀ k, X k)) a b ≠ none) : a i = b i := by
  by_contra hne
  by_cases hex : ∃ j, differsInOne a b j
  · obtain ⟨j, hj⟩ := hex
    have hji : j = i := by
      by_contra hji
      exact hne (hj.2 i (fun hc => hji hc.symm))
    subst hji
    rw [nary_apply_differ c _ hj] at h
    exact h (habs _ _ hne)
  · rw [nary_apply_imp c _ hex] at h
    exact h rfl

/-- **So no distinction across the absent coordinate is present-carried.** The carriage of every such
distinction is left entirely to the import. Carrier-general, uniform in `n`, and it uses ONE property of ONE
factor: absence off its diagonal. -/
theorem cross_absence_carried_general (c : ∀ i, X i → X i → Option Bool) (i : Fin n)
    (habs : ∀ x y, x ≠ y → c i x y = none) (a a' : ∀ k, X k) (hne : a i ≠ a' i) :
    ¬ presentCarried (nary c (botC (∀ k, X k))) a a' := by
  rintro ⟨b, v, v', h1, h2, _⟩
  have e1 := present_forces_coord_eq c i habs a b (by rw [h1]; exact Option.some_ne_none v)
  have e2 := present_forces_coord_eq c i habs a' b (by rw [h2]; exact Option.some_ne_none v')
  exact hne (e1.trans e2.symm)

/-! ## The generalizations, and what they settle

G1 SETTLES THE FLAGGED RISK IN FAVOUR OF THE RESULT. `invariant_scale_constant_G` shows a transposition alone
collapses a scale to a constant, so the constant carrier maps `ScaleIndependence` relied on were doing no work.
`forced_at_bottom_G` then reproves the forcing with only bijections acting. The graded-determination law is NOT
an artifact of the permissive arrow choice and stays a graduates-candidate.

G4 REPLACES A WITNESS BY A LAW. The `Fin 2` refutation of completeness-kills-content becomes
`false_diagonal_survives_every_fill`, carrier-general, and the specific classification demotes to a cited
instance.

G7 LIFTS THE ONE NON-GENERIC PHYSICS-FACING RESULT off its carrier. `cross_absence_carried_general` holds at
every `n` and every carrier, using one property of one factor. The `Fin 3` version demotes to an instance. -/

#print axioms determiner_output_invariant_G
#print axioms invariant_scale_constant_G
#print axioms forced_at_bottom_G
#print axioms false_diagonal_survives_every_fill
#print axioms present_forces_coord_eq
#print axioms cross_absence_carried_general

end Chiralogy.ArcReadiness
