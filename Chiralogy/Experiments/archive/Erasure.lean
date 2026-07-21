import Chiralogy

/-! # Experiment: is the floor derived or stipulated?

The ceiling is derived: totalization taken to its limit collides with faithfulness
(`complete_and_faithful_is_impossible`, a kernel theorem). Test whether the floor is derived the same way,
partialization taken to its limit colliding with something the kernel proves, or whether it merely fails an imposed
entry condition. The parallel: totalization fabricates, filling absences, and filling all while faithful is
contradictory; partialization erases, opening absences, and opening all leaves a classification distinguishing
nothing. Is the second failure a collision or a definition? The discriminating criterion: a collision contradicts
something the kernel proves, a stipulation fails something the protocol requires. Member's non-degeneracy is a
requirement, not a theorem, so failing it is stipulated unless the total opening also contradicts a kernel result.
Concrete instances. Domain content IMPORTED. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Erasure

/-! ## Part 1: what total opening does to the kernel's structure -/

/-- **The transpose goes constant.** At the total opening every row is the same, so the transpose `fun x => c x`
sends every element to one row: no element is distinguished from any other. -/
theorem total_opening_makes_the_transpose_constant :
    ∀ x y : Fin 3, (fun _ _ => none : Fin 3 → Fin 3 → Option Bool) x
      = (fun _ _ => none : Fin 3 → Fin 3 → Option Bool) y :=
  fun _ _ => rfl

/-- **Two-endedness is not contradicted.** `one_map_two_ends` holds at the total opening: the apophatic
obstruction stands and the cataphatic build exists. A constant transpose still has a domain and a codomain, so the
kernel theorem does not fail. -/
theorem does_it_contradict_two_endedness :
    (∀ g : Option Bool → Option Bool, (∀ b, g b ≠ b) →
        ¬ Function.Surjective (fun _ _ => none : Fin 3 → Fin 3 → Option Bool))
    ∧ (∃ build : Fin 3 → (Fin 3 → Option Bool), ∀ x,
        build x = (fun _ _ => none : Fin 3 → Fin 3 → Option Bool) x) :=
  one_map_two_ends _

/-- **The hole is not contradicted.** `hole_uniform` holds at the total opening: the map is not surjective, the
payload fires. The hole is present, the statement unchanged; a constant map is no more surjective than any other. -/
theorem does_it_contradict_the_hole :
    ¬ Function.Surjective (fun _ _ => none : Fin 3 → Fin 3 → Option Bool) :=
  hole_uniform _

/-! ## Part 2: is there a collision at all? -/

/-- **What partialization wants.** Partialization wants emptiness, every pair absent, which the total opening
reaches; the other demand is Member's, to distinguish something, which it fails. Whether this is a collision turns
on the status of the second demand, a requirement rather than a kernel theorem. -/
theorem what_partialization_wants :
    (∀ x y : Fin 3, (fun _ _ => none : Fin 3 → Fin 3 → Option Bool) x y = none)
    ∧ (¬ NonDegenerate (fun _ _ => none : Fin 3 → Fin 3 → Option Bool)) := by
  refine ⟨fun _ _ => rfl, ?_⟩; unfold NonDegenerate; decide

/-- **No erasure collision.** The total opening is a classification, the payload firing, and distinguishes nothing,
both at once, with no contradiction: a constant map is consistent. Contrast the ceiling, where complete and
faithful cannot both hold. There is no pair of kernel demands the total opening cannot jointly satisfy. -/
theorem erasure_collision :
    (¬ Function.Surjective (fun _ _ => none : Fin 3 → Fin 3 → Option Bool))
    ∧ (¬ NonDegenerate (fun _ _ => none : Fin 3 → Fin 3 → Option Bool))
    ∧ (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2) := by
  refine ⟨hole_uniform _, ?_, complete_and_faithful_is_impossible⟩
  unfold NonDegenerate; decide

/-- **The floor condition is internal.** Non-degeneracy compares the map's own rows, with no external target, as
the ceiling collision needs none. So were the floor a bound it would be internal, not imported; the difference
between the bounds is not internal versus external but theorem versus requirement. -/
theorem is_the_collision_internal :
    (∀ (X : Type) (c : X → X → Option Bool), NonDegenerate c ↔ ∃ x x', c x ≠ c x')
    ∧ (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2) :=
  ⟨fun _ _ => Iff.rfl, complete_and_faithful_is_impossible⟩

/-! ## Part 3: the verdict -/

/-- **The floor is stipulated.** At the total opening every kernel theorem holds, two-endedness and the hole; it
fails only Member's non-degeneracy, a requirement not a theorem. The floor follows from failing a protocol
condition, not from a kernel contradiction. -/
theorem floor_is_stipulated :
    ((∀ g : Option Bool → Option Bool, (∀ b, g b ≠ b) →
        ¬ Function.Surjective (fun _ _ => none : Fin 3 → Fin 3 → Option Bool))
      ∧ (∃ build : Fin 3 → (Fin 3 → Option Bool), ∀ x,
          build x = (fun _ _ => none : Fin 3 → Fin 3 → Option Bool) x))
    ∧ (¬ Function.Surjective (fun _ _ => none : Fin 3 → Fin 3 → Option Bool))
    ∧ (¬ NonDegenerate (fun _ _ => none : Fin 3 → Fin 3 → Option Bool)) := by
  refine ⟨one_map_two_ends _, hole_uniform _, ?_⟩
  unfold NonDegenerate; decide

/-- **The bounds are not the same status.** The ceiling is a kernel theorem, a collision proved of every object;
the floor is a protocol condition, the total opening satisfying the kernel while failing the requirement. So the
region is bounded above by a prohibition and below by a definition. -/
theorem are_the_bounds_the_same_status :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2)
    ∧ ((∀ g : Option Bool → Option Bool, (∀ b, g b ≠ b) →
          ¬ Function.Surjective (fun _ _ => none : Fin 3 → Fin 3 → Option Bool))
        ∧ ¬ NonDegenerate (fun _ _ => none : Fin 3 → Fin 3 → Option Bool)) := by
  refine ⟨complete_and_faithful_is_impossible, fun _ _ => hole_uniform _, ?_⟩
  unfold NonDegenerate; decide

/-! ## The verdicts

Part 1: the total opening satisfies every kernel theorem. Its transpose is constant, no element distinguished
(`total_opening_makes_the_transpose_constant`); yet two-endedness holds, a constant transpose still having a domain
and a codomain (`does_it_contradict_two_endedness`), and the hole holds, the map not surjective
(`does_it_contradict_the_hole`). No kernel theorem fails.

Part 2: there is no collision. Partialization wants emptiness and fails to distinguish, but the second is a
requirement not a theorem (`what_partialization_wants`); the total opening is a classification and distinguishes
nothing at once, no contradiction, where the ceiling's complete and faithful cannot coexist (`erasure_collision`).
The floor condition, non-degeneracy, is internal, comparing the map's own rows with no target
(`is_the_collision_internal`), so the difference from the ceiling is not internal versus external.

Part 3: the floor is stipulated (`floor_is_stipulated`), and the bounds are not the same status
(`are_the_bounds_the_same_status`): the ceiling a theorem, the floor a condition.

The verdict: the floor is stipulated, not derived, and the two bounds are not the same status. At the total opening
every kernel theorem holds, two-endedness and the hole, and the transpose merely goes constant, which is
consistent, not contradictory: a constant map is a classification, has two ends, and carries the hole. The failure
is only of Member's non-degeneracy, and non-degeneracy is a protocol requirement, not something the kernel proves,
so failing it is a stipulation, an object dropping below an imposed entry condition, not a collision with a kernel
result. There is no erasure collision to match complete-and-faithful: complete and faithful cannot both hold, a
theorem, while a classification and distinguishing nothing hold together freely. The floor's condition is internal,
comparing the map's own rows with no external target, so it is not imported and the disqualifier is not that; the
difference is theorem versus requirement. So the parallel between the bounds is a resemblance, not an identity: the
region is bounded above by a prohibition, a collision the kernel forces, and below by a definition, a condition the
protocol imposes. Per the counter-bias, the gate was run and no kernel theorem fails at the total opening, so the
stipulation is not dressed in kernel vocabulary; the floor condition needs no target, so it is not an imported
standard; and the constant map is read as consistent, uninteresting but not contradictory. The attractive symmetry
does not complete: one bound is earned, the other declared. Reported per part. Nothing here is resolved. -/

end Chiralogy.Erasure
