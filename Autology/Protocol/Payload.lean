import Autology.Protocol.Membership
import Autology.Kernel.Obstructions

/-! # The payload

The payload is a global absence, inherited by every member: no member has a complete self-account. It is
a gate, not a microscope: a property of the ambient category read at each object, not a per-object fact. -/

namespace Autology

/-- **The payload.** Every member's self-classification is not surjective: no complete self-account. -/
theorem payload (M : Member) : ¬ Function.Surjective M.classify := by
  obtain ⟨g, hg⟩ := fpf_of_canDiffer M.canDiffer
  exact no_reflexive_object hg M.classify

/-- The payload is inherited uniformly: it holds of any classification whose distinction space can differ,
independent of the object. -/
theorem payload_uniform {X B : Type} (hB : ∃ a b : B, a ≠ b) (c : X → X → B) :
    ¬ Function.Surjective c := by
  obtain ⟨g, hg⟩ := fpf_of_canDiffer hB
  exact no_reflexive_object hg c

end Autology
