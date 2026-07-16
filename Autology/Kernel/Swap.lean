import Autology.Kernel.Hole

/-! # The one canonical involution

Argument-swap, exchanging judge and judged, is the one canonical involution. It is meaningful: it
carries the first-argument absence to the second. Codomain-negation is not canonical: not every
fixed-point-free endomap is an involution. -/

namespace Autology

/-- Argument swap: exchange judge and judged. -/
def swap {X B : Type} (c : X → X → B) : X → X → B := fun x y => c y x

theorem swap_involution {X B : Type} (c : X → X → B) : swap (swap c) = c := rfl

/-- Swap acts non-trivially: on a non-symmetric classification it changes the map. -/
theorem swap_nontrivial : ∃ c : Fin 2 → Fin 2 → Bool, swap c ≠ c :=
  ⟨fun i j => decide (i = 0 ∧ j = 1), fun h => absurd (congrFun (congrFun h 1) 0) (by decide)⟩

/-- Swap carries the first-argument absence to the second: swapping a first-argument-idle map makes it
second-argument-idle. -/
theorem swap_relates_absences {X B : Type} (x₀ : X) (c : X → X → B) :
    swap (fun _ y => c x₀ y) = fun x _ => c x₀ x := rfl

/-- Codomain-negation is not a canonical involution: a fixed-point-free endomap need not be an involution
(a 3-cycle is not). -/
theorem codomain_negation_not_canonical :
    ∃ (B : Type) (g : B → B), (∀ b, g b ≠ b) ∧ g ∘ g ≠ id :=
  ⟨Option Bool, optCycle, optCycle_fixedpointfree,
    fun h => absurd (congrFun h none) (by decide)⟩

end Autology
