import Chiralogy.Kernel.Apophatic

/-! # Membership

The conformance interface: the object condition a domain submits to in order to enter, invoking the kernel's
payload. Not a stage of the derivation but the entry point beside the spine, its only dependency the kernel
(for the payload's hypothesis) and its only dependent a register. A domain presents itself as five data with
two tests. The five data: a carrier, a distinction space, a proof that space can differ, a self-classification,
and non-degeneracy. The two tests: the payload fires (the classification is not surjective), and non-degeneracy
holds: the boundary of `Deg`. A register may classify into a level with structured absence; it enters through
this same fixed interface (`register_at_a_level`). -/

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

/-- A register whose classification lands in a structured-absence level (Except, `Bool ⊕ Bool`, two reasons). -/
def leveledMember : Member where
  X := Fin 2
  B := Bool ⊕ Bool
  canDiffer := ⟨Sum.inl true, Sum.inr false, by decide⟩
  classify := fun x y => if x = y then Sum.inl true else Sum.inr false
  nondegenerate := ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩

/-- **A register conforms at a level.** A classification landing in a structured-absence level enters through
the unchanged protocol: only can-differ and non-degeneracy are asked, and the payload fires. The level's
permitted lattice, fragmented center, and per-reason totalizations are then inherited below the payload; the
interface stayed fixed through the model layer's elaboration, demanding nothing of the level. -/
theorem register_at_a_level : ¬ Function.Surjective leveledMember.classify :=
  payload leveledMember

end Chiralogy
