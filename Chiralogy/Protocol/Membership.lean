import Chiralogy.Kernel.Apophatic

/-! # Membership

The object condition, as five data with two tests. The five data: a carrier, a distinction space, a proof
that space can differ, a self-classification, and non-degeneracy. The two tests: the payload fires (the
classification is not surjective), and non-degeneracy holds: the boundary of `Deg`. -/

namespace Chiralogy

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

/-- **Two axes.** Error (a constitutive absence is present) and degeneracy (the self is idle,
`¬ NonDegenerate`) are orthogonal: all four combinations are realized. -/
theorem four_quadrants :
    (∃ c : Fin 2 → Fin 2 → Option Bool, ¬ NonDegenerate c ∧ ∀ x y, c x y ≠ none) ∧
    (∃ c : Fin 2 → Fin 2 → Option Bool, ¬ NonDegenerate c ∧ ∃ x y, c x y = none) ∧
    (∃ c : Fin 2 → Fin 2 → Option Bool, NonDegenerate c ∧ ∀ x y, c x y ≠ none) ∧
    (∃ c : Fin 2 → Fin 2 → Option Bool, NonDegenerate c ∧ ∃ x y, c x y = none) :=
  ⟨⟨fun _ _ => some true, fun ⟨_, _, h⟩ => h rfl, fun _ _ => by simp⟩,
   ⟨fun _ _ => none, fun ⟨_, _, h⟩ => h rfl, 0, 0, rfl⟩,
   ⟨fun x y => some (decide (x = y)), ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩,
     fun _ _ => by simp⟩,
   ⟨fun x y => if x = y then some true else none,
     ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩, 0, 1, by decide⟩⟩

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

end Chiralogy
