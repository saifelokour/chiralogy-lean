import Autology.Kernel.Obstructions
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

/-! # The hole

The hole is arity-1 and uniform: every object is subject to it, whatever its distinction space (as soon
as that space can differ). It transports across any change of distinction space carrying a fixed-point-free
endomap. The empty center is a corollary. -/

namespace Autology

/-- A fixed-point-free endomap of `Option Bool` (a 3-cycle): witnessing the hole on partial objects. -/
def optCycle : Option Bool → Option Bool
  | none => some true
  | some true => some false
  | some false => none

theorem optCycle_fixedpointfree : ∀ o, optCycle o ≠ o := by
  intro o; cases o with
  | none => decide
  | some b => cases b <;> decide

/-- **The hole, uniform.** Every object with distinction space `Option Bool`, total or partial, in any
mode, is subject to the hole: its classification is not surjective. Nothing changes this; the hole is
Cantor-uniform. -/
theorem hole_uniform {X : Type} (c : X → X → Option Bool) : ¬ Function.Surjective c :=
  no_reflexive_object optCycle_fixedpointfree c

/-- The hole transports: any distinction space carrying a fixed-point-free endomap inherits it. -/
theorem hole_transports {X : Type} {B : Type} {g : B → B} (hg : ∀ b, g b ≠ b)
    (c : X → X → B) : ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-- **The empty center.** No carrier is equivalent to its own classifier space `X → Bool`: the reflexive
site has empty fixed locus. A corollary of the hole. -/
theorem empty_center : ¬ ∃ X : Type u, Nonempty (X ≃ (X → Bool)) := by
  rintro ⟨X, ⟨e⟩⟩
  obtain ⟨b, hb⟩ := fixedPoint_of_surjection (⇑e) e.surjective (fun b => !b)
  exact absurd hb (by cases b <;> decide)

end Autology
