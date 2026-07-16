import Autology.Kernel.Trichotomy

/-! # Membership

The object condition, as five data with two tests. The five data: a carrier, a distinction space, a proof
that space can differ, a self-classification, and non-degeneracy. The two tests: the payload fires (the
classification is not surjective), and non-degeneracy holds: the boundary of `Deg`. -/

namespace Autology

/-- A member: the five data of a conformant object. -/
structure Member where
  X : Type
  B : Type
  canDiffer : ∃ a b : B, a ≠ b
  classify : X → X → B
  nondegenerate : ∃ x y : X, classify x ≠ classify y

/-- From "the distinction space can differ" build a fixed-point-free endomap: the payload's hypothesis. -/
theorem fpf_of_canDiffer {B : Type} (h : ∃ a b : B, a ≠ b) : ∃ g : B → B, ∀ x, g x ≠ x := by
  obtain ⟨a, b, hab⟩ := h
  classical
  refine ⟨fun x => if x = a then b else a, fun x => ?_⟩
  by_cases hx : x = a
  · subst hx; simpa using hab.symm
  · simp only [if_neg hx]; exact Ne.symm hx

/-- Non-degeneracy (the second test) is exactly membership outside the degenerate subcategory. -/
theorem nondegenerate_iff_not_degenerate {X B : Type} (c : X → X → B) :
    (∃ x y : X, c x ≠ c y) ↔ NonDegenerate c := Iff.rfl

end Autology
