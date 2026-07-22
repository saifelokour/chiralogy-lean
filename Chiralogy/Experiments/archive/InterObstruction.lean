import Chiralogy

/-! # Experiment: does the product carrier's empty center forbid any cross-configuration?

The difference arc closed with the cross free and no factor forcing it. The open question: is the
inter-object-forced position empty as a theorem or only as an observation, is there any forced inter-object
obstruction the way the empty center forces the ends' non-coincidence? The product carrier `X1 × X2` is still a
classification, so it carries the empty center, forced and inherited; `import_is_the_complement` makes the cross
value exactly the import; `cross_is_free_over_all_factors` realizes any cross-target by taking the import to be it.
A forced obstruction is a cross-configuration no import can realize, arising from the structure, not stipulated; an
imposed constraint, violable by another import, is not one. Compute both directions, aim at neither. Stays in
`Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.InterObstruction

/-! ## Direction A: is any cross-configuration forbidden by the product's empty center? -/

/-- **The center does not constrain the cross.** The product carries the empty center, `X1 × X2` no more isomorphic
to its own function space than any type is, forced; yet every cross-target is realizable, the import being the
target itself. The empty center is a type-level fact about the carrier's ends, the cross a value-level
configuration of verdicts, and realizing a cross-target produces no such isomorphism, so the center forbids no
cross-configuration: the two are orthogonal. -/
theorem does_the_center_constrain_the_cross {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool) :
    (¬ ∃ Y : Type, Nonempty (Y ≃ (Y → Bool)))
    ∧ (∀ r : (X1 × X2) → (X1 × X2) → Option Bool,
        ∃ imp, ∀ a b, a.1 ≠ b.1 → a.2 ≠ b.2 → assembleClassify c1 c2 imp a b = r a b) :=
  ⟨center_is_empty, fun r => cross_is_free_over_all_factors c1 c2 r⟩

/-! ## Direction B: does the cross's freedom foreclose any forced obstruction? -/

/-- **Freedom forecloses obstruction.** No cross-configuration is unrealizable: there is no target `r` that every
import misses on the cross, since for any `r` an import realizes it. So no cross-relation is forbidden, and no
forced inter-object obstruction exists. -/
theorem does_freedom_foreclose_obstruction {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool) :
    ¬ ∃ r : (X1 × X2) → (X1 × X2) → Option Bool,
        ∀ imp, ∃ a b, a.1 ≠ b.1 ∧ a.2 ≠ b.2 ∧ assembleClassify c1 c2 imp a b ≠ r a b := by
  rintro ⟨r, hr⟩
  obtain ⟨imp, himp⟩ := cross_is_free_over_all_factors c1 c2 r
  obtain ⟨a, b, h1, h2, hne⟩ := hr imp
  exact hne (himp a b h1 h2)

/-- **Any candidate obstruction is violable.** For any cross-relation proposed as an obstruction, an import
realizes it and so escapes it: no cross-relation is beyond reach, so any candidate obstruction is imposed, not
forced. -/
theorem any_candidate_is_violable {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (r : (X1 × X2) → (X1 × X2) → Option Bool) :
    ∃ imp, ∀ a b, a.1 ≠ b.1 → a.2 ≠ b.2 → assembleClassify c1 c2 imp a b = r a b :=
  cross_is_free_over_all_factors c1 c2 r

/-! ## The verdict -/

/-- **The inter-object-forced cell is forced-empty.** The empty center is forced, inherited by the product, yet it
forbids no cross-configuration; and realizability is total, no cross-relation being unreachable. So no forced
inter-object obstruction exists, and the cell is provably empty, not merely observed so: the assemblage forces no
inter-object obstruction the way the empty center forces the ends' non-coincidence. -/
theorem inter_forced_cell_status {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool) :
    (¬ ∃ Y : Type, Nonempty (Y ≃ (Y → Bool)))
    ∧ (¬ ∃ r : (X1 × X2) → (X1 × X2) → Option Bool,
          ∀ imp, ∃ a b, a.1 ≠ b.1 ∧ a.2 ≠ b.2 ∧ assembleClassify c1 c2 imp a b ≠ r a b) := by
  refine ⟨center_is_empty, ?_⟩
  rintro ⟨r, hr⟩
  obtain ⟨imp, himp⟩ := cross_is_free_over_all_factors c1 c2 r
  obtain ⟨a, b, h1, h2, hne⟩ := hr imp
  exact hne (himp a b h1 h2)

/-! ## The verdicts

Direction A: the product's empty center forbids no cross-configuration. The center holds, forced, and every
cross-target is realizable (`does_the_center_constrain_the_cross`); the center is orthogonal to the cross.

Direction B: realizability is total. No cross-configuration is unrealizable, no target beyond reach
(`does_freedom_foreclose_obstruction`), and any candidate obstruction is violable by some import
(`any_candidate_is_violable`).

Verdict: the inter-object-forced cell is forced-empty (`inter_forced_cell_status`). The empty center is inherited
and forced but does not reach the cross, and realizability being total, no forced inter-object obstruction exists.

The verdict: the product carrier's empty center forbids no cross-configuration, realizability is total, and the
inter-object-forced cell is provably empty, forced-empty and not merely observed, so the assemblage is provably not
a kernel extension in the sense of forcing an inter-object obstruction. The product carrier does carry a forced
obstruction, its own empty center, since it is still a classification and no type is isomorphic to its function
space; but that obstruction is intra-object, a fact about the assemblage's two ends, the same one every object
carries, inherited from the kernel and not new. It is orthogonal to the cross: the empty center is a type-level
impossibility about the carrier and its function space, while a cross-configuration is a value-level assignment of
verdicts on the fully-cross pairs, and realizing any such configuration is choosing the import to be it, which
constructs no isomorphism and so cannot violate the center. This is Direction A: the center does not constrain the
cross. Direction B computes the same emptiness from the other side: realizability is total, every cross-relation
reachable by some import, so no cross-relation is forbidden, and there is no target that every import misses. The
two directions agree, and the verdict is the forced-empty disjunct, not a population and not an only-imposed-found:
no obstruction was exhibited because none exists, and any relation proposed as an obstruction is violable, an import
realizing it, so it would be imposed and not forced. The counter-bias holds throughout: nothing imposed was read as
forced, since nothing was imposed at all, the result being that no import is forbidden any cross-value; the probe
did not aim, computing both directions and reporting the disjunct the math gives, a clean forced-empty as complete
a finding as a population would have been; and no mirror was mistaken for an obstruction, the point being that no
configuration forbids anything, the cross echoing or exceeding freely as the import chooses. So the assemblage
inherits the kernel's obstruction as its own intra-object empty center but adds no inter-object one; the difference
arc's realizability was not an observation but a theorem, and the inter-object-forced cell is empty by
construction. Emergence, the imported reading, would name a whole exceeding its parts, but there is no forced
whole-level obstruction here to carry it, only the free cross and the inherited center. Reported per direction.
Nothing here is resolved. -/

end Chiralogy.InterObstruction
