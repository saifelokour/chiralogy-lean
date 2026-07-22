import Chiralogy

/-! # Consolidation lift: the difference theory, generalized before graduation

Not a new experiment. This file holds the general re-proofs of the two difference-theory results that were
universal in intent but proven instance-bound, so that the graduation to canonical imports no enumeration wall. The
already-universal results (`DifferenceCondition.exceeding_requires_location`,
`DifferenceCondition.cross_is_free_over_all_factors` and its `ForcedCell` twin, `ForcedCell.no_factor_forces_the_cross`)
are untouched and graduate verbatim; the existential witnesses (`DifferenceCondition.location_is_not_sufficient`,
`sufficiency_is_the_import`, the `NonDegenerate` witness in `Arity`) are untouched, being the correct form. Only two
things are lifted here:

- `Arity`'s collapse, proven at `X2 = Fin 1`, generalized to **any `Subsingleton` second carrier**.
- `InterDifference`'s swap-fixes-the-cross, proven at `Fin 2` with two same-shape factors, generalized to
  **arbitrary same carrier**.

Stays in `Experiments/`; nothing graduates in this pass. -/

open Chiralogy

namespace Chiralogy.DifferenceLift

/-- **The collapse, at any trivial second factor.** When the second carrier is a subsingleton, no two pairs differ
in both components, so the cross-region is empty and the assemblage is independent of the import, over arbitrary
carriers with decidable equality. Generalizes `Arity.product_collapses` from `Fin 1` to any `Subsingleton`. -/
theorem collapse_at_trivial_factor {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2] [Subsingleton X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp imp' : (X1 × X2) → (X1 × X2) → Option Bool) :
    (∀ a b : X1 × X2, ¬ (a.1 ≠ b.1 ∧ a.2 ≠ b.2))
    ∧ (assembleClassify c1 c2 imp = assembleClassify c1 c2 imp') := by
  refine ⟨?_, ?_⟩
  · rintro a b ⟨_, h2⟩; exact h2 (Subsingleton.elim a.2 b.2)
  · funext a b
    exact construction_takes_two_objects_and_a_cross_map c1 c2 imp imp'
      (fun a b _ h2 => absurd (Subsingleton.elim a.2 b.2) h2) a b

/-- **Exceeding is vacuous at a trivial second factor.** With a subsingleton second carrier the assemblage equals
its empty-cross juxtaposition for every import, so it never exceeds. Generalizes the `Arity` verdict; the
non-degenerate factor witnessing that intra survives where inter is vacuous stays an existential in `Arity`. -/
theorem exceeding_vacuous_at_trivial_factor {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2] [Subsingleton X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) :
    assembleClassify c1 c2 imp = assembleClassify c1 c2 (fun _ _ => none) :=
  (collapse_at_trivial_factor c1 c2 imp (fun _ _ => none)).2

/-- **The factor-swap fixes the cross.** For two factors on the same carrier, on a fully-cross pair both orderings
give the import, so swapping the factors leaves the cross-region unchanged, permuting only the determined regions.
Generalizes `InterDifference.what_is_fixed_by_the_swap` from `Fin 2` to an arbitrary carrier with decidable
equality. -/
theorem swap_fixes_the_cross {X : Type} [DecidableEq X] (c1 c2 : X → X → Option Bool)
    (imp : (X × X) → (X × X) → Option Bool) (a b : X × X) :
    a.1 ≠ b.1 → a.2 ≠ b.2 → assembleClassify c1 c2 imp a b = assembleClassify c2 c1 imp a b := by
  intro h1 h2
  rw [import_is_the_complement c1 c2 imp a b h1 h2, import_is_the_complement c2 c1 imp a b h1 h2]

end Chiralogy.DifferenceLift
