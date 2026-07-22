import Chiralogy

/-! # Experiment: is the inter-object-forced cell empty by construction, quantified?

`InterDifference` found the inter-object-forced cell empty by enumeration, out of `decide` reach at scale;
`DifferenceCondition` showed for specific located factors that sufficiency is the free import. The remaining gap is
the fully general, quantified statement: no factor pair forces the cross, because the cross is a free parameter.
`import_is_the_complement` fixes the cross value to exactly the import, unconstrained by the factors. Prove the
quantified freedom and its consequence, and contrast it modally with the empty center: this emptiness is
realizability, not a Lawvere impossibility. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.ForcedCell

/-- Located difference: the cross-region is non-empty. -/
def located (X1 X2 : Type) : Prop := ∃ a b : X1 × X2, a.1 ≠ b.1 ∧ a.2 ≠ b.2

/-! ## Part 1: the quantified freedom -/

/-- **The cross is free over all factors.** For any factors and any target relation on the fully-cross pairs, an
import realizes it, the witness being the target itself, since the cross value is exactly the import. No enumeration
and no hypothesis on the target beyond its being a classification into the value space; location is not needed, the
realization holding vacuously where the cross is empty. -/
theorem cross_is_free_over_all_factors {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (r : (X1 × X2) → (X1 × X2) → Option Bool) :
    ∃ imp : (X1 × X2) → (X1 × X2) → Option Bool,
      ∀ a b, a.1 ≠ b.1 → a.2 ≠ b.2 → assembleClassify c1 c2 imp a b = r a b :=
  ⟨r, fun a b h1 h2 => import_is_the_complement c1 c2 r a b h1 h2⟩

/-! ## Part 2: from freedom to empty forced cell -/

/-- **No factor forces the cross.** For all located factors, over arbitrary carriers with decidable equality, two
imports give assemblages differing on the cross, so the factors do not determine the cross value. This is the
quantified, construction-level version of the enumerated result and of `DifferenceCondition`'s specific witnesses;
the only hypothesis is decidable equality on the carriers, inherent to the construction, not finiteness. -/
theorem no_factor_forces_the_cross {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool) :
    located X1 X2 →
      ∃ imp imp' : (X1 × X2) → (X1 × X2) → Option Bool,
        assembleClassify c1 c2 imp ≠ assembleClassify c1 c2 imp' := by
  rintro ⟨a0, b0, h1, h2⟩
  refine ⟨(fun _ _ => none), (fun _ _ => some true), ?_⟩
  intro heq
  have hval := congrFun (congrFun heq a0) b0
  rw [import_is_the_complement c1 c2 (fun _ _ => none) a0 b0 h1 h2,
      import_is_the_complement c1 c2 (fun _ _ => some true) a0 b0 h1 h2] at hval
  exact absurd hval (by decide)

/-! ## Part 3: realizability, not impossibility -/

/-- **Empty by construction, not by obstruction.** The empty center is an impossibility, forced by Lawvere, no
object's ends can coincide; the empty forced cell is realizability, for any located factors both cross-values are
reachable. The modality differs, one a negated existential, the other a universal existential, so the emptiness is
that the cross is a free parameter, not that anything is impossible. -/
theorem empty_by_construction_not_by_obstruction :
    (¬ ∃ X : Type, Nonempty (X ≃ (X → Bool)))
    ∧ (∀ (c1 c2 : Fin 2 → Fin 2 → Option Bool), located (Fin 2) (Fin 2) →
        ∃ imp imp' : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool,
          assembleClassify c1 c2 imp ≠ assembleClassify c1 c2 imp') :=
  ⟨center_is_empty, fun c1 c2 hl => no_factor_forces_the_cross c1 c2 hl⟩

/-! ## The verdicts

Part 1: the cross is realizable for any target over all factors, the witness the target itself
(`cross_is_free_over_all_factors`); no target hypothesis beyond value-space membership, and location unneeded.

Part 2: the quantified no-forcing holds, over arbitrary carriers with decidable equality, needing no finiteness
(`no_factor_forces_the_cross`).

Part 3: the emptiness is realizability, both cross-values reachable, not a Lawvere impossibility
(`empty_by_construction_not_by_obstruction`).

The verdict: the inter-object-forced cell is empty by construction and quantifiedly, not merely by enumeration,
because the cross is a free parameter no factor pair constrains, and this emptiness is realizability rather than
obstruction. For any factors and any target relation on the fully-cross pairs there is an import realizing it,
witnessed by the target itself, since the cross value is exactly the import by `import_is_the_complement`; the
realization needs no enumeration, no hypothesis on the target beyond its being a classification, and not even
location, holding vacuously where the cross is empty. From this the forced cell's emptiness follows generally: for
all located factors, over arbitrary carriers, two imports give assemblages that differ on the cross, so no factor
pair entails one cross-value over another, and the only hypothesis is decidable equality on the carriers, inherent
to the construction and not finiteness, so the claim does not silently specialize back to finite carriers. This is
the delta over the settled ground. `DifferenceCondition` proved the same for specific `Fin 2` factors by exhibited
imports; this quantifies it over all factors, and that quantification is the whole new content, the earlier
specific-witness statements not re-proved but subsumed. And the modality is on the record: the empty center is an
impossibility, a negated existential forced by Lawvere, while the empty forced cell is a universal existential,
realizability, both cross-values reachable for any located factors, so the two emptinesses are opposite in kind, one
a wall and the other an open field. Empty by construction here means the cross is a free parameter, that within the
assemblage no factor forces the cross; it does not mean nothing could ever force inter-object difference, since an
extension adding structure to the cross, a constraint or a further factor-level fact, is not ruled out by this, and
that ceiling is kept in the doc and out of the names. Per the counter-bias, `DifferenceCondition` was not re-proved,
its specific witnesses subsumed under the quantified statement and named as the delta; freedom was not merely
restated, the free parameter connected to the forced cell being empty over all factors, which is the content; and
impossibility was not overclaimed, the emptiness stated as realizability and the extension ceiling flagged. There
is no emergence here, only the construction-internal freedom of the cross. Reported per part. Nothing here is
resolved. -/

end Chiralogy.ForcedCell
