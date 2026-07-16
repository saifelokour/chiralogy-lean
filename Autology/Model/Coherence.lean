import Autology.Model.Arrangement
import Autology.Kernel.Hole

/-! # Coherence

Comparability intransitivity is a genuine derived structure: measure-free, and routing through neither
obstruction. The directed cycle is not the hole (a map can carry the hole with no cycle, and one with a
cycle) and it is not a measure, being a first-order relational condition. -/

namespace Autology

/-- A cyclic classification: `0` over `1` over `2` over `0`: each pair ranked, the order inconsistent. -/
def cyclic : Fin 3 → Fin 3 → Option Bool := fun x y =>
  if x = y then none
  else if y = x + 1 then some true
  else some false

/-- The cycle: each pair is ranked, the order inconsistent. -/
theorem cyclic_witness :
    cyclic 0 1 = some true ∧ cyclic 1 2 = some true ∧ cyclic 2 0 = some true :=
  ⟨by decide, by decide, by decide⟩

/-- The cycle needs no absence: it is comparable everywhere off the diagonal. -/
theorem cyclic_is_total : ∀ x y : Fin 3, x ≠ y → cyclic x y ≠ none := by decide

/-- The coherence content: no maximum: every element is beaten by another, no global order though every
pairwise verdict is present. -/
theorem cyclic_no_maximum : ∀ x : Fin 3, ∃ y, cyclic y x = some true := by decide

/-- A transitive order, for the separation. -/
def linear : Fin 3 → Fin 3 → Option Bool := fun x y =>
  if x = y then none else if x < y then some true else some false

/-- **The cycle is not the hole.** The transitive order carries the hole yet has no 3-cycle: the hole does
not entail the cycle. So the cycle is arity-3 among distinct elements: it routes through neither
obstruction. -/
theorem cycle_is_not_the_hole :
    (¬ Function.Surjective linear) ∧
      (¬ ∃ a b c : Fin 3, linear a b = some true ∧ linear b c = some true ∧ linear c a = some true) :=
  ⟨hole_uniform linear, by decide⟩

/-- Both maps carry the hole; only one cycles: coherence-failure and incompleteness are independent. -/
theorem cyclic_also_has_hole : ¬ Function.Surjective cyclic :=
  hole_uniform cyclic

/-- Comparability transitivity is measure-free: a decidable first-order relational condition, no count. -/
def intransitivity_is_measure_free (c : Fin 3 → Fin 3 → Option Bool) :
    Decidable (∀ x y z : Fin 3, Comparable c x y → Comparable c y z → Comparable c x z) := by
  unfold Comparable; infer_instance

end Autology
