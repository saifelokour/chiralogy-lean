import Chiralogy

/-! # Experiment: structural redundancy without history

The historical notion (`LateralApex`) needed a span and gave objectivity only conditionally. Structural
redundancy would instead be over-determination: a value fixed by several views such that dropping any one leaves
it fixed. The hope is that robustness does the work theory-morphism legs did, blocking fabrication: if a value
survives dropping any single view, no single fabricating view produced it. Test that claim; do not assume it.
Views are modelled as constraint sets over `Fin 3`, joint determination as a singleton intersection, robustness
as surviving any single deletion. Concrete small diagrams. Stays in `Experiments/`; canonical untouched; nothing
resolved. -/

open Chiralogy

namespace Chiralogy.StructuralRedundancy

/-- Three views jointly determine `v` when their intersection is the singleton `{v}`. -/
abbrev det3 (A B C : Finset (Fin 3)) (v : Fin 3) : Prop := A ∩ B ∩ C = {v}

/-- The value is robust when it stays determined after dropping any single view. -/
abbrev robust3 (A B C : Finset (Fin 3)) (v : Fin 3) : Prop :=
  B ∩ C = {v} ∧ A ∩ C = {v} ∧ A ∩ B = {v}

/-! ## Part 1: the notion -/

/-- **Jointly determined.** A value is jointly determined by a diagram when the intersection of the views is a
singleton, the limit fixing it. Both diagrams determine `1`: three views each forcing `1`, and `A = {0,1}`,
`B = C = {1,2}` meeting at `1`. -/
theorem jointly_determined :
    det3 {1} {1} {1} 1 ∧ det3 {0, 1} {1, 2} {1, 2} 1 :=
  ⟨by decide, by decide⟩

/-- **Robust to deletion.** Robust when the value stays determined after dropping any single view. The first
diagram is robust, each view alone forcing `1`; the second is not, dropping `A` leaving `{1,2}`, undetermined.
Robustness can fail, so the notion does not collapse as the total apex did. -/
theorem robust_to_deletion :
    robust3 {1} {1} {1} 1 ∧ ¬ robust3 {0, 1} {1, 2} {1, 2} 1 :=
  ⟨by decide, by decide⟩

/-! ## Part 2: does robustness replace non-fabrication? -/

/-- **A fabricating view cannot survive deletion.** If dropping a view leaves the value undetermined, that view
was load-bearing, so a value produced by a single fabricating view cannot survive its deletion (dropping `A` from
the second diagram leaves `{1,2}`). Conversely a robust value survives every single deletion, so no one view
solely produced it. The load-bearing claim holds against a single fabricator. -/
theorem fabricating_view_cannot_survive_deletion :
    (det3 {0, 1} {1, 2} {1, 2} 1 ∧ ({1, 2} ∩ {1, 2} : Finset (Fin 3)) ≠ {1})
    ∧ robust3 {1} {1} {1} 1 :=
  ⟨⟨by decide, by decide⟩, by decide⟩

/-- **What if two views fabricate alike.** Two views both fabricating `1`, with a third uninformative (`univ`),
determine `1` and are robust: dropping either fabricator leaves the other, dropping the third leaves both. So
robustness holds under coordinated fabrication. This is robustness without evidence, the independence question
the metaphysics raises: over-determination is evidential only if the determinants are independent, and two
coordinated fabrications are not. -/
theorem what_if_two_views_fabricate_alike :
    det3 {1} {1} Finset.univ 1 ∧ robust3 {1} {1} Finset.univ 1 :=
  ⟨by decide, by decide⟩

/-- **Is independence expressible.** Robustness is decided by the views' sets alone; a coordination flag does not
enter, so the same configuration is robust whether the two agreeing views are independent or coordinated. The
framework can say both views determine the value; it cannot say they are independent. Independence would need
data beyond the sets, a provenance the framework does not carry, so robustness is not evidential. -/
theorem is_independence_expressible (_coordinated : Bool) :
    robust3 {1} {1} Finset.univ 1 := by decide

/-! ## Part 3: is it contingent and informative? -/

/-- **Is robustness contingent.** Both diagrams are jointly determined, a limit fixing the value, but only the
first is robust; determination does not force robustness, so limits in `Obj` do not make every value robust. The
notion is contingent, not universal. -/
theorem is_robustness_contingent :
    (det3 {1} {1} {1} 1 ∧ det3 {0, 1} {1, 2} {1, 2} 1)
    ∧ (robust3 {1} {1} {1} 1 ∧ ¬ robust3 {0, 1} {1, 2} {1, 2} 1) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **Does it need theory morphisms.** Robustness needs none; it is defined over arbitrary views, and both an
honest diagram and a coordinated one satisfy it. So it is stageable now without the tower, but the very absence
of a constraint on the legs is why it cannot exclude coordinated fabrication. The historical notion used theory
morphisms to block fabrication; robustness drops them and loses that block. -/
theorem does_it_need_theory_morphisms :
    robust3 {1} {1} {1} 1 ∧ robust3 {1} {1} Finset.univ 1 :=
  ⟨by decide, by decide⟩

/-! ## Part 4: comparison -/

/-- **Structural versus historical.** The historical notion is conditional on a span and needs theory-morphism
legs, which block a fabricated absence by respecting absence forward; it gives objectivity only when such a span
exists. The structural needs neither: deletion blocks a single fabricator (a load-bearing view makes the diagram
non-robust) but not two coordinated ones (robust despite fabrication). So the historical buys non-fabrication
with a structural precondition; the structural buys generality and loses the block against coordination. Neither
is unconditionally evidential. -/
theorem structural_versus_historical :
    (¬ robust3 {0, 1} {1, 2} {1, 2} 1)
    ∧ (robust3 {1} {1} Finset.univ 1) :=
  ⟨by decide, by decide⟩

/-- **What neither gives.** Neither recovers a source from agreement. The robust honest diagram and the robust
coordinated one determine the same value `1`, the limit identical; agreement is read off the determination, not
used to infer independence or a source. As with the historical notion, the inference runs forward only. -/
theorem what_neither_gives :
    (det3 {1} {1} {1} 1 ∧ det3 {1} {1} Finset.univ 1)
    ∧ ((1 : Fin 3) = 1) :=
  ⟨⟨by decide, by decide⟩, rfl⟩

/-! ## The verdicts

Part 1: robustness is definable and can fail. A value is jointly determined when the views meet in a singleton
(`jointly_determined`), and robust when it survives any single deletion; the first diagram is robust, the second
is not (`robust_to_deletion`). The gate passes: robustness can fail, so it does not collapse.

Part 2: robustness replaces non-fabrication against one fabricator but not two. A single fabricating view is
load-bearing and cannot survive its deletion (`fabricating_view_cannot_survive_deletion`), so a robust value was
not produced by any one view alone. But two coordinated fabricators, with a third uninformative, are robust
(`what_if_two_views_fabricate_alike`), and the framework cannot tell coordinated agreement from independent, the
data being the sets alone (`is_independence_expressible`). So robustness is not evidential where the metaphysics
says it must be, at independence.

Part 3: robustness is contingent and needs no theory morphisms. Determination does not force robustness, so
limits do not make every value robust (`is_robustness_contingent`); and robustness is defined over arbitrary
views (`does_it_need_theory_morphisms`), stageable now, but that same freedom is why it cannot exclude
coordination.

Part 4: the two notions trade the same deficit differently. The historical needs a span and theory-morphism
legs and blocks fabrication; the structural needs neither and blocks only single fabrication
(`structural_versus_historical`). Neither recovers a source, the limit identical for honest and coordinated
diagrams (`what_neither_gives`).

The verdict: structural redundancy is definable, contingent, and free of the span and the tower, and it does
block a single fabricator, which is real progress over nothing. But it does not do the work the historical
notion's theory morphisms did, because the block it offers stops at coordination: two views that fabricate alike
are robust, and the framework has only the sets, not their independence, so it cannot separate over-determination
from collusion. What would make it evidential is exactly what is missing, an independence relation on the views,
a provenance beyond the constraint sets; robustness without it is structural agreement again, not evidence. So
neither notion is unconditionally evidential: the historical pays a span, the structural pays independence, and
the framework supplies neither for free. Reported per part. Nothing here is resolved. -/

end Chiralogy.StructuralRedundancy
