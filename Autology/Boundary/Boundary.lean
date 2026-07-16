import Autology.Model.Moves
import Autology.Protocol.Payload

/-! # The boundary: the one prohibition

The framework hands back the ethics: no target, no valuation. It issues exactly one judgment without a
target, and only one. The attempt to totalize a self-classification into completeness aims at a
destination the boundary proves empty, and reaches for it by trading a true absence for a false verdict.
That move is self-defeating by its own goal: an idolatry of the empty center. The prohibition follows
from an impossibility, not from a value; it attaches only to the claim of completeness; and every
reachable target, and whether any cost matters, is handed back.

This is the interpretive edge of the kernel. The theorems below carry it; the prose is a reading. -/

namespace Autology

/-- **Completeness is unreachable.** The success condition of the totalizing attempt, a surjective
self-classification, is provably unsatisfiable. -/
theorem completeness_is_unreachable {X : Type} (c : X → X → Option Bool) :
    ¬ Function.Surjective c :=
  hole_uniform c

/-- **The internal contradiction.** A total map that is also faithful to a constitutive absence is
impossible: totality needs a verdict where faithfulness needs the absence. The self-defeat is by the
move's own goal: no external standard, no imported value, only the map's own absence against totality. -/
theorem complete_and_faithful_is_impossible :
    ¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2 := by
  rintro ⟨c, htotal, hfaithful⟩
  rw [show imprecise (0 : Fin 4) 2 = none from by decide] at hfaithful
  exact htotal 0 2 hfaithful

/-- **Totalization is self-defeating.** It fills the absences yet the totalized map still carries the hole
- it cannot reach the completeness it aims at. Its own success condition fails. -/
theorem totalization_is_self_defeating {X : Type} (s : X → Nat) (c : X → X → Option Bool) :
    (∀ x y, totalization s c x y ≠ none) ∧ ¬ Function.Surjective (totalization s c) :=
  ⟨totalization_totalizes s c, totalization_hole s c⟩

/-! ## Why the target is imported: no standard certifies itself -/

/-- **Every target is defeasible.** A target is itself a self-classification, subject to the same hole:
no standard is complete over itself. So no target certifies itself, and the target is handed back (○). -/
theorem every_target_is_defeasible {X : Type} (target : X → X → Bool) :
    ¬ Function.Surjective target :=
  no_reflexive_object (g := fun b => !b) (by decide) target

/-! ## The three limits: the prohibition does not swell -/

/-- Local partialization is not prohibited: a single local move is a valid, reachable operation: it does
not aim at the empty destination. -/
theorem local_partialization_not_prohibited :
    ∃ (w : Fin 4 → Fin 4 → Bool) (c : Fin 4 → Fin 4 → Option Bool),
      partialization w c 0 2 = none :=
  ⟨fun _ _ => true, fun _ _ => some true, by simp [partialization]⟩

/-- No reachable target is prohibited: moving toward any target is always a valid step. Every target
stays ○. -/
theorem reachable_targets_not_prohibited {X : Type} (c : X → X → Option Bool) (t : Option Bool) (x : X) :
    x ∈ targetCoalgebra c x t :=
  agreementLE_refl c t x

/-- Abstention is not prescribed: partialization's cost is target-dependent: a withdrawal is a loss only
relative to a target. The prohibition is one-sided, silent on everything reachable. -/
theorem prohibition_does_not_prescribe_abstention :
    ∃ (c : Fin 2 → Fin 2 → Option Bool) (w : Fin 2 → Fin 2 → Bool) (t1 t2 : Fin 2 → Fin 2 → Bool),
      c 0 1 = some (t1 0 1) ∧ assertsFalse c t2 0 1 ∧ partialization w c 0 1 = none :=
  ⟨(fun x y => if x = 0 ∧ y = 1 then some true else none),
   (fun x y => decide (x = 0 ∧ y = 1)),
   (fun _ _ => true), (fun _ _ => false),
   by decide, ⟨true, by decide, by decide⟩, by decide⟩

/-- **Autology falls under its own prohibition.** As an object of itself it is subject to the same hole:
it too cannot claim completeness. Nor does it install its register (category theory, type theory, Lean,
English) as the complete language: that would be the attempt performed on its own medium. The facts are
register-independent and multiply-verifiable, so no register is the complete one, and claiming otherwise is
the same prohibited totalization one level up. -/
theorem autology_under_its_own_boundary {X : Type} (c : X → X → Option Bool) :
    ¬ Function.Surjective c :=
  completeness_is_unreachable c

end Autology
