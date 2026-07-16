import Autology.Kernel.TargetDynamics
import Autology.Kernel.Hole

/-! # Scope

Three structures, three scopes. The hole is uniform (every object). The target-flow is global (it crosses
mode boundaries). Self-entry is regional (confined to the self-model region). -/

namespace Autology

/-- A mixed object: a no-self-model block `{0,1}`, a total block `{2,3}`, a partial block `{4,5}`, coupled
by cross-block verdicts on one carrier. -/
def mixed : Fin 6 → Fin 6 → Option Bool := fun x y =>
  if x.val / 2 ≠ y.val / 2 then some (decide (x.val < y.val))
  else if y.val < 2 then some (decide (y.val = 0))
  else if y.val < 4 then some (decide (x = y))
  else if x = y then some true else none

/-- **The hole is uniform**: present on the mixed object as on every object. -/
theorem hole_scope_uniform : ¬ Function.Surjective mixed := hole_uniform mixed

/-- **Self-entry is regional.** The first argument is idle on the no-self-model block; the total and
partial blocks are non-degenerate. Self-entry is confined to those regions. -/
theorem self_entry_regional :
    (∀ x x' y : Fin 6, x.val < 2 → x'.val < 2 → y.val < 2 → mixed x y = mixed x' y) ∧
      (∃ x x' y : Fin 6, 2 ≤ x.val ∧ x.val < 4 ∧ 2 ≤ x'.val ∧ x'.val < 4 ∧ 2 ≤ y.val ∧ y.val < 4 ∧
        mixed x y ≠ mixed x' y) ∧
      (∃ x x' y : Fin 6, 4 ≤ x.val ∧ 4 ≤ x'.val ∧ 4 ≤ y.val ∧ mixed x y ≠ mixed x' y) := by
  refine ⟨by decide, ⟨2, 3, 2, by decide⟩, ⟨4, 5, 5, by decide⟩⟩

/-- **The target-flow is global.** It crosses mode boundaries: a no-self-model state is `⊑_t`-below a
total-self-model state. Not confined like self-entry. -/
theorem flow_global :
    ∃ (t : Option Bool) (x x' : Fin 6),
      x.val / 2 ≠ x'.val / 2 ∧ agreementLE mixed t x x' := by
  refine ⟨none, 0, 2, by decide, ?_⟩
  unfold agreementLE
  decide

end Autology
