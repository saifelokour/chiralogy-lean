import Chiralogy.Protocol.Membership
import Chiralogy.Model.Cataphatic
import Chiralogy.Model.Boundary

/-! # Register: physics (GR / QM)   [READING]

There is one physical object, and it is partial. Measurement is the classification
`c(observer, system) = outcome`; the object carries a constitutive `none` (superposition) and the observer
enters it (non-degenerate). GR and QM are not two objects. They are two demands on the one object: that it
be total (every outcome definite), and that it keep its constitutive `none`.

Quantum gravity, posed as one complete deterministic account that also keeps the indefiniteness, asks the
one object to satisfy both demands. `complete_and_faithful_is_impossible` forbids that of any object: at the
pair where the `none` lives, totality requires a value and faithfulness requires its absence. So quantum
gravity is not hard, it is the attempt, on the physical object, to fill the center that cannot be filled.
GR is the totality demand the one partial object cannot meet without fabricating its `none`; QM is the
demand that it keep the `none`. The GR/QM boundary is the open seam: approachable from either side, never
closing, because closing it is complete-and-faithful.

This is a READING, defeasible: that physics has this shape is a domain reading, not a theorem about
physics. A different physics register may map differently and is equally Chiralogy. The register stays in
this chart and never enters the derived layers.
-/

namespace Chiralogy.Physics

/-- The one physical object: partial (superposition is the constitutive `none`), non-degenerate (the
observer enters). A single member. -/
def phys : Member where
  X := Fin 4
  B := Option Bool
  canDiffer := ⟨some true, none, by decide⟩
  classify := imprecise
  nondegenerate := imprecise_is_partial_mode.1

/-- The GR demand: totality, every outcome definite, no absence. -/
def gr_demand {X : Type} (c : X → X → Option Bool) : Prop := ∀ x y, c x y ≠ none

/-- The QM demand: faithfulness, the constitutive `none` is kept. -/
def qm_faithful {X : Type} (c : X → X → Option Bool) : Prop := ∃ x y, c x y = none

/-- The one object meets the QM demand: it keeps its `none` (superposition). -/
theorem phys_qm_faithful : qm_faithful phys.classify := imprecise_is_partial_mode.2

/-- **Quantum gravity is the attempt.** No object is both total (the GR demand) and faithful to the
constitutive `none` where physics carries it (`c 0 2 = imprecise 0 2`, and `imprecise 0 2` is `none`, the
QM demand). This is `complete_and_faithful_is_impossible` verbatim: the two demands contradict at the pair
where the `none` lives. -/
theorem quantum_gravity_is_the_attempt :
    ¬ ∃ c : Fin 4 → Fin 4 → Option Bool, gr_demand c ∧ c 0 2 = imprecise 0 2 :=
  complete_and_faithful_is_impossible

/-- **The GR/QM boundary is the open seam.** Approachable from either side, never closing. Toward the
GR demand, totalization fabricates (`totalization_not_faithful`); toward the QM demand, the collapse admits
no recovery (`no_recovery`). The crossing does not close, because closing it is complete-and-faithful, the
empty center (`the_open_seam`, `quantum_gravity_is_the_attempt`). -/
theorem gr_qm_boundary :
    (∃ c c' : Fin 2 → Fin 2 → Option Bool, c ≠ c' ∧
        totalization (fun _ => 0) c = totalization (fun _ => 0) c') ∧
      (¬ ∃ recover : (Fin 2 → Fin 2 → Bool) → (Fin 2 → Fin 2 → Bool), ∀ c, recover (lift 0 c) = c) :=
  ⟨totalization_not_faithful, no_recovery⟩

/-- **The cataphatic half of physics**: the transpose of its own self-classification, one map read at two
ends. Not a forced construction; it is `phys.classify`, the map that carries the apophatic hole. -/
def phys_has_cataphatic_half : CataphaticConformant :=
  ⟨phys.X, phys.X → phys.B, fun s => phys.classify s⟩

/-- **Physics conforms to both arms.** It passes `Member` (apophatic, the contentful hole) and
`CataphaticConformant` (cataphatic, its own transpose). The domain layer is shared, and lopsided: the
cataphatic conformance is the loose gate, the free transpose rather than an independent structure. -/
theorem phys_conforms_to_both :
    (phys.classify = phys.classify) ∧
      phys_has_cataphatic_half.build = fun s => phys.classify s :=
  ⟨rfl, rfl⟩

end Chiralogy.Physics
