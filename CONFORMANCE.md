# Conformance: chiralogy-lean against the Chiralogy specification

This chart realizes the Chiralogy specification in Lean 4 with mathlib. Each item of the specification is
mapped below to the theorem or definition that realizes it, with the module and the `#print axioms` result.

- Register: category theory and English, realized in Lean 4 with mathlib.
- Baseline: `{propext, Classical.choice, Quot.sound}`. Every realized item stays within it.
- Notation: "axioms: none" means the item depends on no axioms at all; a listed set is a subset of the
  baseline. The object condition `c : X → X → B` is `Obj` (Kernel/Apophatic.lean); the transpose `ĉ` is
  surjectivity of `c` read as `X → (X → B)`.

## Verdict: FULL

Every item is realized at its stated status, with axioms within baseline and no sorry. Three items were
first unrealized (3.3, 4.3, and the universal-property part of 5.1); each was then proven and now stands as
THEOREM. One item (3.8) was reworded during validation: the code proves more than the specification first
claimed, and the specification was corrected to match the code. No item is contradicted by the code.

## Kernel

- 3.1 THEOREM. `no_reflexive_object` (Kernel/Apophatic.lean). axioms: none.
- 3.2 THEOREM. `no_universe_classifier` (axioms: none) and `no_right_adjoint` (axioms:
  {propext, Classical.choice, Quot.sound}) (Kernel/Apophatic.lean).
- 3.3 THEOREM. `obstructions_independent` (Kernel/Apophatic.lean). axioms: {propext, Quot.sound}. The
  reflexive-object obstruction is codomain-relative (holds on `Bool`, fails on `Unit`); the size
  obstruction (`no_small_universe`) is universe-absolute. Neither reduces to the other.
- 3.4 THEOREM. `hole_transports` (Kernel/Apophatic.lean). axioms: none. Relabeling invariance; arity-one is
  inherent in the transpose form (the hole lives on `ĉ : X → Bˣ`, one argument).
- 3.5 THEOREM. `hole_uniform` (Kernel/Apophatic.lean). axioms: none.
- 3.6 THEOREM. `empty_center` (Kernel/Apophatic.lean). axioms: {Quot.sound}.
- 3.7 THEOREM. `three_modes` (Kernel/Apophatic.lean). axioms: {propext, Classical.choice, Quot.sound}.
- 3.8 THEOREM. `lift_is_basepoint_parametric` (axioms: {propext}) and `reflector_universal`
  (Kernel/Apophatic.lean). The lift needs a chosen basepoint; the degenerate objects are reflective via
  the codomain quotient. See Changes.
- 3.9 THEOREM. `swap_involution` and `codomain_negation_not_canonical` (Kernel/Apophatic.lean). axioms: none.
- 3.10 MIXED. `order_canonical` (THEOREM, axioms: none) with `targetCoalgebra`; the rate is IMPORTED,
  witnessed by `rate_imported` (axioms: {propext}) (Kernel/Apophatic.lean).
- 3.11 THEOREM. `hole_scope_uniform` (axioms: none), `flow_global` and `self_entry_regional` (axioms:
  {propext}) (Kernel/Apophatic.lean).
- 3.12 MIXED. `no_recovery` with `lift_not_injective` (THEOREM: irreversibility; axioms:
  {propext, Classical.choice, Quot.sound}) (Kernel/Apophatic.lean). "Time's arrow" is the READING.
- 3.13 THEOREM. `no_generation` (Kernel/Apophatic.lean). axioms: none.
- 3.14 MIXED. `self_account_has_hole` (THEOREM, axioms: none) (Kernel/Apophatic.lean); the identity
  `𝒜 = Chiralogy` is IMPORTED, refused (not stated or proven).
- 3.15 THEOREM. `two_inversions_share_center` (axioms: none), `ethical_center_is_distinct` (axioms: none),
  `center_is_empty` (axioms: {Quot.sound}) (Kernel/Center.lean).
- 3.16 MIXED. `two_inversions_share_center` (THEOREM) (Kernel/Center.lean). "Chiasm" is the READING.

## Protocol

- 4.1 THEOREM. `Member` with `nondegenerate_iff_not_degenerate` (axioms: none) (Protocol/Membership.lean).
- 4.2 THEOREM. `payload` (Protocol/Membership.lean). axioms: {propext, Classical.choice, Quot.sound}.
- 4.3 THEOREM. `four_quadrants` (Protocol/Membership.lean). axioms: {propext}. All four combinations of
  error (constitutive absence) and degeneracy (self idle) are inhabited by explicit witnesses.

## Model

- 5.1 MIXED. `maybe_free_pointed` (THEOREM: the universal property, `B + 1` is the free pointed object;
  axioms: {Quot.sound}), with `payload_survives` and `example : Monad Option` (the extension exists and the
  payload survives) (Model/Apophatic.lean). Canonicity is the READING.
- 5.2 THEOREM. `the_diagonal_is_copy` and `stochastic_collapses` (Model/Apophatic.lean). axioms: none.
- 5.3 MIXED. `imprecise_is_partial_mode` (THEOREM: one occupant, incomparability is a `none`, not a tie;
  axioms: {propext}) (Model/Apophatic.lean). Rarity is the READING.
- 5.4 THEOREM. `comparability_federates`, `comparability_has_cut_vertex`, `total_comparability_complete`
  (axioms: {propext}) (Model/Apophatic.lean). "Magnitude requires a measure" defers to 8.1 (IMPORTED).
- 5.5 THEOREM. `cycle_is_not_the_hole`, `cyclic_also_has_hole`, `intransitivity_is_measure_free`
  (Model/Apophatic.lean).
- 5.6 MIXED. `model_arms_invert` (THEOREM: the arms and costs invert; axioms: {propext}) (Model/Apophatic.lean).
  The naming is the READING.
- 5.7 MIXED. `model_arms_invert` and `model_center_is_the_none` (THEOREM: center distinct from 3.16; axioms:
  {propext}) (Model/Apophatic.lean). "Chiasm" is the READING.

## Boundary

- 6.1 THEOREM. `completeness_is_unreachable` (Model/Boundary.lean). axioms: none.
- 6.2 MIXED. `complete_and_faithful_is_impossible` (THEOREM; axioms: {propext}) (Model/Boundary.lean).
  "Self-defeat" is the READING.
- 6.3 MIXED. `totalization_is_self_defeating` (THEOREM core; axioms: {propext}) (Model/Boundary.lean).
  "Ethical claim" is the READING.
- 6.4 THEOREM. `local_partialization_not_prohibited`, `reachable_targets_not_prohibited`,
  `prohibition_does_not_prescribe_abstention` (Model/Boundary.lean).
- 6.5 READING. `chiralogy_under_its_own_boundary` (axioms: none) (Model/Boundary.lean) realizes the
  payload one level up; the distinctive claim (installing neither itself nor its register as complete) is
  the reading.
- 6.6 MIXED. `self_account_has_hole` (THEOREM; axioms: none) (Kernel/Apophatic.lean, read at the
  Boundary); the whole is not the representation, IMPORTED.
- 6.7 MIXED. `the_open_seam` (axioms: {propext}) (Model/Boundary.lean), re-presenting
  `boundary_braids_both_absences` (THEOREM: both centers braided). The pivot is a READING; the far side is
  IMPORTED.
- 6.8 THEOREM. `double_chiasm_does_not_compose` (Model/Boundary.lean). axioms: {propext}.

## The figure

- 7.1 MIXED. `double_chiasm_conjunction` (parts are THEOREM; axioms: {propext})
  (Model/Boundary.lean). The unified figure is a READING resting on 6.8, for a structural reason, not
  on incompleteness. `chiasm_of` shows the two chiasms admit only a dispatch, not a shared generator.

## Imported

- 8.1 IMPORTED. Located, not proven. The target and the rate: `rate_imported` (Kernel/Apophatic.lean),
  `every_target_is_defeasible` (Model/Boundary.lean); the harm and every magnitude are supplied per
  register and never enter the derived layers.

## Registers

Domain instances, marked READING, defeasible, kept in this chart. A register instantiates the structure by
membership; it never enters the derived layers, and that a domain has this shape is a reading, not a
theorem about the domain.

- Physics (GR / QM), READING (Registers/Physics.lean; investigated in Experiments/archive/PhysicsRegister.lean).
  One object: `phys : Member`, partial (`phys_qm_faithful`, the constitutive `none` = superposition),
  non-degenerate (the observer enters). GR and QM are not two objects but two demands on the one object:
  `gr_demand` (totality) and `qm_faithful` (keep the `none`). Inherited by membership, not new:
  `quantum_gravity_is_the_attempt` is 6.2 verbatim (no object is both total and faithful to the `none`, so
  a unified physics object is the attempt to fill the empty center, impossible not hard); `gr_qm_boundary`
  is 6.7, the open seam (toward totality fabricates via `totalization_not_faithful`, keeping the `none`
  admits no recovery via `no_recovery`, the crossing does not close). All axioms within baseline. Graduates
  nothing to the derived layers.

## Changes reconciled during validation

- 3.3, 4.3, and the free-pointed-object part of 5.1 were first unrealized. Each was then proven and added
  to the chart: `obstructions_independent` (independence as a codomain-versus-universe separation),
  `four_quadrants` (the two axes as four inhabited quadrants), and `maybe_free_pointed` (the universal
  property of `B + 1`). All three now stand as THEOREM, so the verdict is FULL.
- 3.8. The specification first claimed the degenerate subcategory has "no reflector." The code proves
  `reflector_universal`: the degenerate objects are reflective via the codomain quotient, while the lift is
  not the reflector. The specification was reworded to match the code.

The bound held: no imported content was added to the derived layers, the register disclaimer stands, the
one prohibition and the open seam stand, and 6.8 stands (the two chiasms do not compose into one figure).
