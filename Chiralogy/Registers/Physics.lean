import Chiralogy.Protocol.Membership
import Chiralogy.Model.Cataphatic
import Chiralogy.Model.Apophatic.Instances
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

The register is layered, three strata, three statuses. Stratum 1 (THEOREM): the measurement schema entails
`quantum_gravity_is_the_attempt`, by `complete_and_faithful_is_impossible`. Stratum 2 (IMPORTED): the literal
GR determinism and QM superposition demands, stated as domain content. Stratum 3 (READING, defeasible): the
fidelity, that the imported demands instantiate the schema. The entailment is entailed given the schema, the
equations are imported, and only the identification is the reading, the hinge a physicist's objection lands
on. `quantum_gravity_is_the_attempt` is asserted as entailment-given-schema, never as QG impossible
simpliciter, and its carrier is the schema, not the equations. A different physics register may map
differently and is equally Chiralogy; the register stays in this chart and never enters the derived layers.

The ethics abstracts over levels (`ethics_abstracts_over_levels`): a register receives its level's structure
and supplies only the reading of the reasons. Physics offers one ground, so its lattice is the base binary
(`physics_has_one_ground`, READING); the base's single prohibition and physics's single ground are one fact
from two sides (`base_matches_its_founding_register`, READING).
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

/-! ## Stratum 1: the measurement schema and the entailment (THEOREM) -/

/-- **The measurement schema** (register-native): one measurement classification
`c(observer, system) = outcome` under both demands, GR totality (`gr_demand c`, reused) and QM a kept none at
the measurement pair (`c 0 2 = imprecise 0 2`, `qm_faithful` at that pair). -/
structure MeasurementSchema (c : Fin 4 → Fin 4 → Option Bool) : Prop where
  gr : gr_demand c
  qm : c 0 2 = imprecise 0 2

/-- **The schema entails the attempt.** Given the measurement schema on one classification, QG as posed is
impossible: `complete_and_faithful_is_impossible` applied to the schema's two demands. The schema is the
antecedent, and appears in the proof. -/
theorem measurement_entails_attempt (c : Fin 4 → Fin 4 → Option Bool) : ¬ MeasurementSchema c :=
  fun s => complete_and_faithful_is_impossible ⟨c, s.gr, s.qm⟩

/-! ## Stratum 2: the literal demands as IMPORTED witnesses

Domain content, imported not derived. Physlib (PhysLean) is not added here: it requires a mathlib revision
incompatible with this project's pinned `v4.31.0`, so the demands stay bare unit-free imports. They are
opaque predicates, so Stratum 2 alone is consistent; the tension appears only under the Stratum 3 reading. -/

/-- IMPORTED: GR's determinism demand, as a domain predicate on the measurement classification. -/
axiom GRDeterminism : (Fin 4 → Fin 4 → Option Bool) → Prop

/-- IMPORTED: QM's superposition demand, as a domain predicate on the measurement classification. -/
axiom QMSuperposition : (Fin 4 → Fin 4 → Option Bool) → Prop

/-- IMPORTED: GR demands determinism of the measurement classification (a definite outcome everywhere). -/
axiom gr_determinism_demand : GRDeterminism phys.classify

/-- IMPORTED: QM demands superposition of the measurement classification (a kept none until measurement). -/
axiom qm_superposition_demand : QMSuperposition phys.classify

/-! ## Stratum 3: the fidelity claim (READING, the defeasible hinge) -/

/-- **The fidelity reading**, ●: the imported demands are the schema's demands, GR determinism is totality
and QM superposition is the kept none. This is the defeasible hinge, stated not asserted. Disputing it
denies that GR and QM are demands on one classification (holding, say, that they are different theories on
different domains, so no single map bears both). All the register's defeasibility lives here: Stratum 1 is
entailed, Stratum 2 is imported. -/
def schema_is_physics_reading : Prop :=
  (∀ c, GRDeterminism c ↔ gr_demand c) ∧ (∀ c, QMSuperposition c ↔ c 0 2 = imprecise 0 2)

/-! ## The ethics abstracts over levels

Physics sits at the base, one ground. A register may instead classify into a level with structured absence; the
structure it then carries is the level's, and the domain supplies only the reading of what the reasons are. -/

/-- A second register at the same level as `leveledMember`, a different carrier reading the reasons at the
opposite cells. -/
def secondLeveledMember : Member where
  X := Fin 3
  B := Bool ⊕ Bool
  canDiffer := ⟨Sum.inl true, Sum.inr false, by decide⟩
  classify := fun x y => if x = y then Sum.inr true else Sum.inl false
  nondegenerate := ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩

/-- **The ethics abstracts over levels.** Two registers at one level (Except, two reasons) coincide on every
structural ethical feature, the permitted count (`3`), the prohibition (the unique full closure), and the
center (two distinct reason-parts), and differ only in which absence sits where. The level shapes the ethics,
the domain names the reasons: structure derived, content imported, the register-import pattern. -/
theorem ethics_abstracts_over_levels :
    (¬ Function.Surjective leveledMember.classify ∧ ¬ Function.Surjective secondLeveledMember.classify)
    ∧ (Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3
    ∧ (Finset.univ.filter (fun close : Fin 2 → Bool => ∀ r, close r = true)).card = 1
    ∧ (exceptAbsence.absent (Sum.inr false) ∧ exceptAbsence.absent (Sum.inr true)
        ∧ (Sum.inr false : Bool ⊕ Bool) ≠ Sum.inr true)
    ∧ (leveledMember.classify (0 : Fin 2) (1 : Fin 2)
        ≠ secondLeveledMember.classify (0 : Fin 3) (1 : Fin 3)) := by
  refine ⟨⟨payload leveledMember, payload secondLeveledMember⟩, by decide, by decide,
    ⟨⟨false, rfl⟩, ⟨true, rfl⟩, by decide⟩, ?_⟩
  show (Sum.inr false : Bool ⊕ Bool) ≠ (Sum.inl false : Bool ⊕ Bool)
  decide

/-- **Physics has one ground** (READING, defeasible). Physics offers a single natural ground of absence, the
constitutive none (superposition), so its lattice is the base binary: keep-open or totalize, no intermediate,
the one-reason permitted count. A second physically distinguishable ground is not forced; a physicist urging
one maps differently. Stated, not asserted, as the register's fidelity is. -/
def physics_has_one_ground : Prop :=
  QMSuperposition phys.classify
    ∧ (Finset.univ.filter (fun close : Fin 1 → Bool => ¬ ∀ r, close r = true)).card = 1

/-- **The base matches its founding register** (READING, defeasible). The base's single prohibition and
physics's single ground are one fact from two sides: the canonical register has one ground
(`physics_has_one_ground`), and the base is the free theory on one constant (`base_is_free_on_one_constant`).
The framework's base is shaped by its founding register. Stated as a reading, not a theorem. -/
def base_matches_its_founding_register : Prop :=
  physics_has_one_ground
    ∧ (∀ v : Option Bool, v = none ↔ ∃ u : Unit, failMaybe u = v)

/-! ## Provisional

When Physlib formalizes the field equations and the measurement postulate as theorems, `GRDeterminism` and
`QMSuperposition` can be replaced by derived statements in physical units, upgrading Stratum 2 from
stated-import to formalized-import. Carried for coverage, not asserted. -/

end Chiralogy.Physics
