import Chiralogy

/-! # Experiment: is inter-object differentiation the empty center one level up?

The framework has difference-notions at the object level: non-degeneracy (a protocol requirement), the empty center
(proven from Lawvere, the two ends cannot coincide), chirality (op relates the ends, the hole surviving it). The
assemblage requires the cross-region to differ from the mirror or it does not exceed. Test whether these are the
same condition at different levels or analogous but distinct. Do not coin a term; report what would need naming.
Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.InterDifference

/-- Saturated and present classifications on `Fin 2`, and the mirroring import of the saturated one. -/
def s : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none
def p : Fin 2 → Fin 2 → Option Bool := fun x y => some (decide (x = y))
def mir : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool := fun a b => s a.1 b.1

/-! ## Part 1: is cross-differentiation a non-coincidence condition? -/

/-- **Mirroring is coincidence.** Mirroring extends one factor's classification across the cross, treating the two
factors as though they were one; the assemblage then equals the juxtaposition and does not exceed. The failure to
exceed is the failure of the two factors to be two. -/
theorem mirroring_is_coincidence :
    assembleClassify s s mir = assembleClassify s s (fun _ _ => none) := by decide

/-- **Compared to the empty center.** The empty center forbids one object's two ends coinciding, `X ≃ (X → Bool)`,
and it is proven; cross-differentiation requires the two factors not be treated as coinciding, mirroring being the
coincidence that collapses. Same non-coincidence shape, one forbidden and proven, the other required and
definitional. -/
theorem compare_to_the_empty_center :
    (¬ ∃ X : Type, Nonempty (X ≃ (X → Bool)))
    ∧ (assembleClassify s s mir = assembleClassify s s (fun _ _ => none)) :=
  ⟨center_is_empty, by decide⟩

/-! ## Part 2: theorem or condition? -/

/-- **Cross-differentiation is not forced.** Mirroring is a valid assemblage, the payload firing, not forbidden; it
is merely non-exceeding, equal to the juxtaposition. Unlike the empty center, which forbids coincidence,
cross-differentiation only fails to reward it. -/
theorem is_cross_differentiation_forced :
    (¬ Function.Surjective (assembleClassify s s mir))
    ∧ (assembleClassify s s mir = assembleClassify s s (fun _ _ => none)) := by
  refine ⟨hole_uniform _, by decide⟩

/-- **The split is theorem versus requirement.** The empty center is proven, holding of every object;
cross-differentiation is a requirement, failing for mirroring, which is a valid non-exceeding assemblage. So the two
are analogous, not identical, the same split as ceiling and floor: one forced, one imposed. -/
theorem the_split_is_theorem_versus_requirement :
    (¬ ∃ X : Type, Nonempty (X ≃ (X → Bool)))
    ∧ (¬ Function.Surjective (assembleClassify s s mir)
        ∧ assembleClassify s s mir = assembleClassify s s (fun _ _ => none)) :=
  ⟨center_is_empty, hole_uniform _, by decide⟩

/-! ## Part 3: does chirality reach the assemblage? -/

/-- **Factor-swap is op-analogous without op's force.** The hole survives factor-swap, both orderings firing the
payload, and for unlike factors the swap is non-trivial, relating two distinct factors as op relates the two ends.
But it lacks op's enforced non-coincidence: op's ends cannot coincide, proven, while the factors can, a like pair
making the swap the identity. -/
theorem is_there_an_op_between_factors :
    (∀ imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool,
        ¬ Function.Surjective (assembleClassify s p imp) ∧ ¬ Function.Surjective (assembleClassify p s imp))
    ∧ (assembleClassify s p (fun _ _ => none) ≠ assembleClassify p s (fun _ _ => none))
    ∧ (¬ ∃ X : Type, Nonempty (X ≃ (X → Bool))) := by
  refine ⟨fun _ => ⟨hole_uniform _, hole_uniform _⟩, by decide, center_is_empty⟩

/-- **The swap fixes the cross-region.** On a fully-cross pair both orderings give the import, so factor-swap leaves
the cross-region unchanged, permuting only the determined regions. As op fixes the empty center, factor-swap fixes
the cross-region, the free part between the factors. -/
theorem what_is_fixed_by_the_swap (imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool) (a b : Fin 2 × Fin 2) :
    a.1 ≠ b.1 → a.2 ≠ b.2 → assembleClassify s p imp a b = assembleClassify p s imp a b := by
  intro h1 h2
  rw [import_is_the_complement s p imp a b h1 h2, import_is_the_complement p s imp a b h1 h2]

/-! ## Part 4: the verdict -/

/-- **Analogous, not the same.** The empty center is forced, a theorem; cross-differentiation is a condition,
mirroring valid and non-exceeding; and non-degeneracy is the intra-object required difference, a condition too. So
cross-differentiation has the empty center's non-coincidence shape but non-degeneracy's conditional force, at the
inter-object level: a distinct notion. -/
theorem same_or_analogous :
    (¬ ∃ X : Type, Nonempty (X ≃ (X → Bool)))
    ∧ (¬ Function.Surjective (assembleClassify s s mir)
        ∧ assembleClassify s s mir = assembleClassify s s (fun _ _ => none))
    ∧ (¬ NonDegenerate (fun _ _ => none : Fin 2 → Fin 2 → Option Bool)) := by
  refine ⟨center_is_empty, ⟨hole_uniform _, by decide⟩, ?_⟩
  unfold NonDegenerate; decide

/-- **The conditional vocabulary extends, not the forced.** Non-degeneracy, the intra-object required difference,
can fail; exceeding, the inter-object one, can fail too, for mirroring, so exceeding is non-degeneracy one level up.
The empty center is a theorem and does not extend to the conditional case. What would need naming is the
inter-object required difference in general; the corpus calls it exceeding, the standard candidate emergence being
the imported domain reading rather than a framework term, so no term is coined. -/
theorem does_the_vocabulary_extend :
    (¬ NonDegenerate (fun _ _ => none : Fin 2 → Fin 2 → Option Bool))
    ∧ (assembleClassify s s mir = assembleClassify s s (fun _ _ => none)) := by
  refine ⟨?_, by decide⟩
  unfold NonDegenerate; decide

/-! ## The verdicts

Part 1: cross-differentiation is a non-coincidence condition. Mirroring is the coincidence claim, treating the two
factors as one and collapsing to the juxtaposition (`mirroring_is_coincidence`); the empty center forbids one
object's ends coinciding, proven, while cross-differentiation requires two factors not coincide, definitional
(`compare_to_the_empty_center`).

Part 2: it is a condition, not a theorem. Mirroring is not forbidden, only non-exceeding
(`is_cross_differentiation_forced`); the empty center is proven while cross-differentiation is a requirement that
fails for mirroring (`the_split_is_theorem_versus_requirement`).

Part 3: factor-swap is op-analogous without op's force. The hole survives it and it relates distinct factors, but
the factors can coincide where op's ends cannot (`is_there_an_op_between_factors`); and it fixes the cross-region,
permuting only the determined regions (`what_is_fixed_by_the_swap`).

Part 4: analogous, not the same, and the conditional vocabulary extends. Cross-differentiation has the empty
center's shape but non-degeneracy's force (`same_or_analogous`); exceeding is non-degeneracy one level up, the empty
center a theorem that does not extend (`does_the_vocabulary_extend`).

The verdict: inter-object differentiation is not the empty center at another level but a distinct condition sharing
its non-coincidence shape, and it is non-degeneracy one level up rather than the empty center. Mirroring states the
coincidence, the cross treated as though the two factors were one, and the assemblage then collapses to the
juxtaposition, so the failure to exceed is exactly the failure of two factors to be two, which is the empty
center's shape, two things not coinciding. But the modality differs: the empty center is proven, no object's ends
can coincide, forced by Lawvere, while cross-differentiation is only a requirement, mirroring being a valid
assemblage that simply does not exceed, not a forbidden one. This is the theorem-versus-requirement split that has
separated three pairs already, ceiling from floor and the rest, appearing here between the empty center and
cross-differentiation. So cross-differentiation carries the empty center's non-coincidence shape with
non-degeneracy's conditional force, and it is the inter-object analogue of non-degeneracy, exceeding standing to
two objects as distinguishing stands to one, both requirements that fail rather than theorems that hold. Chirality
reaches the assemblage only partway: factor-swap is op-analogous, an involution relating the two factors under
which the hole survives, and for unlike factors it is non-trivial as op is between the ends, and it fixes the
cross-region as op fixes the empty center, permuting only the determined regions; but it lacks op's enforced
non-coincidence, since a like pair makes the swap the identity, the factors coinciding where op's ends, forbidden
by the empty center, cannot. So the vocabulary that extends is non-degeneracy's, the conditional one, not the empty
center's, the forced one: the inter-object required difference is the corpus's exceeding, and the standard term for
a whole differing from its juxtaposition, emergence, is the imported domain reading rather than a framework term,
so the gap for a framework name is reported and none is coined. Per the counter-bias, the identification was not
assumed, the theorem-versus-condition split found again and the notion placed with non-degeneracy not the empty
center; factor-swap was not assumed to be op, checked and found op-analogous but without op's force; and no term
was proposed, the gap reported and the imported candidate named as imported. Reported per part. Nothing here is
resolved. -/

end Chiralogy.InterDifference
