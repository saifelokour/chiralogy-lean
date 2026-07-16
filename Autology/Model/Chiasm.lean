import Autology.Model.Moves
import Autology.Kernel.Chiasm
import Autology.Boundary.Boundary

/-! # The model chiasm and the boundary pivot

The kernel chiasm (K15) is two inversions around the hole. This module tests two further things.

Part 1: the model layer has its own two-armed chiasm around the constitutive absence `none`. Totalization
fills a none (cost target-free) and partialization opens one (cost target-dependent): two distinct,
cost-inverted arms (`model_arms_invert`), both pivoting on the none, not the hole (`model_center_is_the_none`,
citing `ethical_center_is_distinct`). Totalization is irreversible, so partialization is a genuine second
move, not its inverse by definition.

Part 2: the one prohibition invokes both absences. B1 (the destination is empty) routes through the kernel
hole `no_reflexive_object`; B2 (complete-and-faithful is impossible) routes through the model none. The
Boundary is where the two layer-centers meet (`boundary_braids_both_absences`).

● boundary_is_the_pivot: the kernel chiasm (center: hole) and the model chiasm (center: none) cross at the
Boundary, where B1 and B2 are the two arms. The Boundary is the pivot of the two sub-chiasms, the χ of the
two χ's.

○ double_chiasm_does_not_totalize: this proves two layer-chiasms and that the Boundary braids their
centers. It does not prove the framework is doubly chiastic as a whole, because the two chiasms do not share
a uniform generator: their centers, the hole and the none, are different kinds of absence
(`Boundary/DoubleChiasm`). The whole figure is a reading (●), not one object. -/

namespace Autology

/-- **The model's two arms invert at the none.** Totalization fills a none (none ↦ some) and partialization
opens one (some ↦ none): opposite directions on the none-axis, exhibited on one object. Their costs invert:
totalization falsifies against every target (target-free), partialization asserts no falsehood against any
target (target-dependent). Two distinct arms, not one move twice. -/
theorem model_arms_invert :
    (∃ (s : Fin 4 → Nat) (w : Fin 4 → Fin 4 → Bool),
        (imprecise 0 2 = none ∧ totalization s imprecise 0 2 ≠ none) ∧
        (imprecise 0 1 ≠ none ∧ partialization w imprecise 0 1 = none)) ∧
    (∀ t : Fin 4 → Fin 4 → Bool,
        assertsFalse (totalization (fun _ => 0) imprecise) t 0 2 ∨
          assertsFalse (totalization (fun i => if i = 2 then 1 else 0) imprecise) t 0 2) ∧
    (∀ (w : Fin 4 → Fin 4 → Bool) (c : Fin 4 → Fin 4 → Option Bool)
        (t : Fin 4 → Fin 4 → Bool) (x y : Fin 4),
        assertsFalse (partialization w c) t x y → assertsFalse c t x y) :=
  ⟨⟨fun _ => 0, fun x y => decide (x = 0 ∧ y = 1),
      ⟨⟨by decide, totalization_totalizes _ _ 0 2⟩, ⟨by decide, by decide⟩⟩⟩,
   totalization_falsifies_against_every_target,
   fun w c t x y => partialization_asserts_no_falsehood w c t x y⟩

/-- **The model center is the none.** Both arms pivot on the constitutive absence: totalization changes
only the none entries (present verdicts pass through), and partialization's product is a none. This center
is distinct from the kernel hole: a total object carries the hole with no none (`ethical_center_is_distinct`). -/
theorem model_center_is_the_none :
    (∀ (X : Type) (s : X → Nat) (c : X → X → Option Bool) (x y : X) (b : Bool),
        c x y = some b → totalization s c x y = some b) ∧
    (∀ (X : Type) (w : X → X → Bool) (c : X → X → Option Bool) (x y : X),
        w x y = true → partialization w c x y = none) ∧
    (∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ ¬ Function.Surjective c) := by
  refine ⟨fun X s c x y b h => ?_, fun X w c x y h => ?_, ethical_center_is_distinct⟩
  · simp [totalization, h]
  · simp [partialization, h]

/-- **The Boundary braids both absences.** The one prohibition invokes each layer-center: B1 (the
destination is empty) routes through the kernel hole `no_reflexive_object`; B2 (complete-and-faithful is
impossible) routes through the model none (`imprecise 0 2 = none`). The two centers meet at the Boundary. -/
theorem boundary_braids_both_absences :
    (∀ (X : Type) (c : X → X → Option Bool), ¬ Function.Surjective c) ∧
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2) :=
  ⟨fun _ c => no_reflexive_object optCycle_fixedpointfree c, complete_and_faithful_is_impossible⟩

end Autology
