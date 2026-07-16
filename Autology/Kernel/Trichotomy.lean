import Autology.Kernel.Hole

/-! # The three modes

By whether the self enters the classification, every object is: no-self-model (the first argument is
idle), total-self-model, or partial-self-model. The degenerate objects form a full subcategory `Deg`,
whose boundary is non-degeneracy. The lift onto `Deg` is a full functor but not a reflection: its
degenerate shadow is parametric in a basepoint. `Deg` is nonetheless reflective, via the codomain quotient. -/

namespace Autology

/-- Non-degeneracy: the self enters the map: two carrier elements induce different classification rows. -/
def NonDegenerate {X B : Type} (c : X → X → B) : Prop := ∃ x x', c x ≠ c x'

/-- **The three modes are exhaustive.** No self-model (`¬ NonDegenerate`), total self-model, or partial
self-model. -/
theorem three_modes {X : Type} (c : X → X → Option Bool) :
    (¬ NonDegenerate c) ∨
      (NonDegenerate c ∧ ∀ x y, c x y ≠ none) ∨
      (NonDegenerate c ∧ ∃ x y, c x y = none) := by
  by_cases h : NonDegenerate c
  · by_cases ht : ∀ x y, c x y ≠ none
    · exact Or.inr (Or.inl ⟨h, ht⟩)
    · refine Or.inr (Or.inr ⟨h, ?_⟩)
      by_contra hc
      exact ht (fun x y hxy => hc ⟨x, y, hxy⟩)
  · exact Or.inl h

/-- A single external judge, the first argument idle, is degenerate. This is the boundary of `Deg`. -/
theorem external_judge_is_degenerate {X : Type} (j : X → Option Bool) :
    ¬ NonDegenerate (fun (_ : X) => j) := by
  rintro ⟨_, _, h⟩; exact h rfl

/-! ## The lift is not a reflection -/

/-- The lift onto `Deg` collapses to a degenerate shadow at a basepoint. Different basepoints give
different shadows; so the lift is parametric, not a canonical reflector. -/
theorem lift_is_basepoint_parametric :
    ∃ c : Fin 2 → Fin 2 → Bool,
      (fun (_ : Fin 2) y => c 0 y) ≠ (fun (_ : Fin 2) y => c 1 y) :=
  ⟨fun i j => decide (i = j), fun h => absurd (congrFun (congrFun h 0) 0) (by decide)⟩

/-! ## `Deg` is reflective, via the codomain quotient -/

/-- The reflector's distinction space: `B` quotiented so the rows collapse. -/
def reflValues {X B : Type} (c : X → X → B) : Type :=
  Quot (fun b b' => ∃ x x' y, b = c x y ∧ b' = c x' y)

/-- The reflected classification. -/
def reflClassify {X B : Type} (c : X → X → B) : X → X → reflValues c :=
  fun x y => Quot.mk _ (c x y)

/-- The reflector's target is degenerate. -/
theorem reflClassify_degenerate {X B : Type} (c : X → X → B) :
    ¬ NonDegenerate (reflClassify c) := by
  rintro ⟨x, x', h⟩
  exact h (funext fun y => Quot.sound ⟨x, x', y, rfl, rfl⟩)

/-- **`Deg` is reflective.** A morphism to a degenerate object forces its value map to equalize the rows;
every such map factors uniquely through the quotient. This is the reflection: the reflector is the
codomain quotient, not the basepoint shadow. -/
theorem reflector_universal {X B B' : Type} (c : X → X → B) (g : B → B')
    (hg : ∀ x x' y, g (c x y) = g (c x' y)) :
    ∃! gbar : reflValues c → B', ∀ b, gbar (Quot.mk _ b) = g b := by
  refine ⟨Quot.lift g ?_, fun _ => rfl, ?_⟩
  · rintro b b' ⟨x, x', y, rfl, rfl⟩; exact hg x x' y
  · intro h hh
    funext q
    induction q using Quot.ind
    exact hh _

end Autology
