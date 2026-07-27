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

## Derived

Structure graduated from the live experiments after the specification was written. These are not specification
items; they are results the derived layers proved and now carry, held to the same baseline and the same
discipline. Graduated in the Model/Moves pass.

- 9.1 THEOREM. The relabelling and its forcedness: `relabel`, `relabelW`, `relabel_id`, `relabel_comp`,
  `relabelW_comp`, `relabelW_or`, and `relabel_unique` (among operations reading each cell of the relabelled
  object off a single cell of the original, only precomposition by the same map in both arguments reproduces
  the action, so nothing was chosen) (Model/Moves.lean). axioms: none.
- 9.2 THEOREM. The transport laws: `transport_law` and `transport_law_fill` (Model/Moves.lean). Both hold by
  computation, so relabelling-equivariance of the two moves is an identity already present at every carrier,
  not a condition imposed. axioms: none.
- 9.3 THEOREM. The combined arrows and the category on classifications: `Arrow`, `act`, `arrowComp`,
  `arrowId`, `act_id`, `act_comp`, `arrowComp_id_left`, `arrowComp_id_right`, `arrowComp_assoc`, and the
  packaged `Arr`, `arrId`, `arrComp`, `arr_id_left`, `arr_id_right`, `arr_assoc` (Model/Moves.lean). The
  composition law is forced by 9.2 clause by clause. axioms: {propext, Quot.sound}.
- 9.4 THEOREM. The hom-sets, and the action is not faithful: `act_hom_iff`, `mask_hom_iff`,
  `mask_hom_freedom` (two masks between the same pair differ only where both ends already abstain), and
  `action_not_faithful` (Model/Moves.lean). axioms: {propext, Quot.sound}.
- 9.5 THEOREM. The two arms' categorical asymmetry: `partialization_union` and `partialization_id` (the open
  arm accumulates by mask-union and has an identity), against `fill_has_no_identity` (the fill arm has no
  identity at any object carrying an absence, so only the mask arm forms a category) (Model/Moves.lean).
  axioms: {propext, Quot.sound} and {propext}.
- 9.6 THEOREM. Nondegeneracy under fills: `cResist` and `nondegeneracy_survives_every_fill` (Model/Moves.lean).
  A classification with every distinction absence-carried that EVERY scale leaves non-degenerate, so absence of
  presence-protection does not imply destroyability. axioms: {propext, Quot.sound}.

Graduated in the Model/InformationOrder pass. These reach `cLE`, `optLE`, `botC`, `cTrue` or `fillCell`, so
they sit above the moves.

- 9.7 THEOREM. The minimal mask and the order-collapse of the mask hom-set: `minMask`, `minMask_realizes`
  (whenever `B` sits below `A`, opening `A` by the minimal mask gives exactly `B`, so every downward step in
  the order is a mask arrow) and `minMask_least` (every mask carrying `A` to `B` fires wherever the minimal one
  does, so the plurality of 9.4 is removable by choosing a representative), with `optMeet_self`
  (Model/InformationOrder.lean). axioms: {propext, Quot.sound}.
- 9.8 THEOREM. Relabelling against the order, and the kernel of the arrow action: `relabel_preserves_order`
  (axioms: none) and `act_eq_iff` (two arrows act identically iff their masks agree and their carrier maps
  agree wherever the mask does not fire, which is exactly why 9.4's action is not faithful)
  (Model/InformationOrder.lean). axioms: {propext, Quot.sound}.
- 9.9 THEOREM. The fill at the order bottom: `EquivariantDeterminer`, `equivariant_determiner_invariant`,
  `swap_invariant_scale_constant` (a transposition already collapses a scale) and `fill_at_order_bottom_forced`
  (Model/InformationOrder.lean). Every relabelling fixes the empty classification, so a determiner that reads
  the object rather than the labelling must be constant there and the fill is the all-true map whichever
  determiner was supplied. Bijections suffice. Stated as a fact about this construction; NO novelty is claimed
  for the underlying up-to-automorphism argument, and the literature check on that point has not been run.
  axioms: {propext, Classical.choice, Quot.sound}.
- 9.10 THEOREM. Operator faithfulness of the two arms: `OperatorFaithful`, `open_operator_faithful` and
  `fill_operator_ext_iff` (Model/InformationOrder.lean). These concern the PARAMETER, where
  `totalization_not_faithful` concerns the OBJECT, so they sharpen rather than repeat it: the open arm's mask
  is recovered from the operator, while the fill arm's scale is recovered only up to the comparison it induces.
  axioms: {propext, Quot.sound}.
- 9.11 THEOREM. The single-cell fill algebra: `fills_at_different_cells_commute` and
  `fills_at_same_cell_absorb` (Model/InformationOrder.lean). Single-cell fills commute except at a shared cell,
  where the first one wins. axioms: {propext, Quot.sound}.

Graduated in the Model/NaryAssemblage pass. These reach `nary` and `differsInOne`, so they sit above the order.
The `Classical.choice` in most of them comes from `nary`'s `Exists.choose` and is within baseline.

- 9.12 THEOREM. The regions and the cross: `Pt`, `IsCross` (an `abbrev`, so instance search unfolds it for the
  decidable witnesses), `diagAt`, and `present_forces_coord_eq` (a present verdict at a cell of the empty-import
  assembly forces the two points to agree at that coordinate) (Model/NaryAssemblage.lean). axioms: none for the
  first three, {propext, Classical.choice, Quot.sound} for the last.
- 9.13 THEOREM. The import carries the order: `import_order_embeds` (with the factors fixed, one assembly sits
  below another exactly when the imports are ordered on the cross, so the construction is an order embedding),
  `nary_meet`, `import_bottom`, `bottom_is_unique`, `maxima_are_plural`, and
  `composite_fill_not_a_factor_operation` (Model/NaryAssemblage.lean). The free region is an ordered space in
  its own right, with a unique bottom and plural maxima. axioms: {propext, Classical.choice, Quot.sound}.
- 9.14 THEOREM. The fibre-preserving symmetries: `Fib`, `Fib_differsInOne`, `Fib_cross`, `fib_fixes_iff` (a
  coordinatewise map fixes an assembly exactly when it fixes each factor off that factor's own diagonal and
  fixes the import on the cross), `factor_condition_is_local`, `full_product_when_unconstrained`,
  `region_verdict_factors_through_coord` (the region blow-up: a region verdict factors through its coordinate
  pair) and `rigid_factors_force_identity` (Model/NaryAssemblage.lean). The blow-up repeats each factor cell
  across the other fibres but leaves the factor's own partition untouched, so it forces no symmetry.
  axioms: {propext, Classical.choice, Quot.sound}; the `Fib` lemmas axiom-free.
- 9.15 THEOREM. The full symmetry group of a classification: `cellMap`, `Level`, `fixes_iff_levels` (a carrier
  map fixes a classification exactly when the induced cell map preserves every level set), and
  `aut_invariant_under_value_relabel` (relabelling the verdicts by any injection leaves the group unchanged, so
  absence is not distinguished among them) (Model/NaryAssemblage.lean). Witnesses `mixing_not_closed` (the
  non-fibre-preserving elements are not closed under composition, so there is no subgroup complement) and
  `full_group_not_determined_by_factors` (two assemblies with the same factors and different imports have
  different automorphism groups). No assembly structure is used in the characterization itself.
  axioms: {Quot.sound} for the two general results, baseline for the witnesses.
- 9.16 THEOREM. The assembly as a cone over its pieces: `regionMask`, `crossMask`, `absenceMask`, `regionSlice`,
  `crossSlice`, `regionSlice_apply`, `crossSlice_apply`, `regionSlice_reads_factor`, `crossSlice_reads_import`,
  `leg_of_total`, `mediator_exists`, `mediator_unique`, `lazy_leg_no_mediator`,
  `automorphism_breaks_existence` (Model/NaryAssemblage.lean). Each piece is the assembly opened by a mask
  written in `differsInOne`, so a piece is a value of the down-move and a projection is a mask arrow by
  definition.

  POSITIVE HALF: under two restrictions, to mask arrows and to total sources, the cone IS a limit
  (`mediator_exists` with `mediator_unique`), and uniqueness needs no totality.

  NEGATIVE HALF, and its place in the literature. The setting is the known one for cones that fail to be limits
  once the ambient structure is enriched or 2-categorical: weighted, lax and pseudo limits, and the
  2-categorical failure of terminal cones analysed by Clingman and Moser. The nearest named relative is an
  EQUIVARIANT universal property, universal up to a group action rather than up to unique isomorphism. What is
  proved here is an INSTANCE within that landscape and is not offered as new and is not a named theorem: the
  cone is jointly monic but not universal, the exact obstruction is the assembly's automorphism group
  (`automorphism_breaks_existence`, carrier-general and uniform in the coordinate), a second and independent
  obstruction is laziness (`lazy_leg_no_mediator`), and no forced enrichment repairs either.
  axioms: {propext, Quot.sound} and below; `automorphism_breaks_existence` axiom-free.
- 9.17 THEOREM. What no fill can merge: `false_diagonal_survives_every_fill` (Model/Moves.lean). Two rows
  carrying a false verdict on their own diagonal and abstaining on the other's cannot be merged by any fill,
  because a scale cannot order two points both ways. PLACEMENT CORRECTION: shelved for the NaryAssemblage
  group, it reaches `totalization` and nothing above it, so the graph put it with the moves.
  axioms: {propext, Quot.sound}.

Graduated in the Model/AssemblageRelations pass, the last of the four. These reach `presentCarried` in
Model/Apophatic as well as `nary` in Model/NaryAssemblage, and neither of those imports the other, so they are
forced up to the first module that sees both branches.

- 9.18 THEOREM. The import map and its embedding: `importMap`, `importMap_kernel` (two imports have the same
  image exactly when they agree on the cross, so the map is not injective on the nose and faithfulness means
  injectivity modulo cross-agreement), `CrossSupported`, `importMap_injective_on_crossSupported`,
  `importMap_is_a_meet_embedding`, and `importMap_singles_out_emptiness` (the empty import is least and there
  is NO greatest element at all) (Model/NaryAssemblage.lean). axioms: {propext, Classical.choice, Quot.sound}.
- 9.19 THEOREM. Absence carried through the import order: `presentCarried_mono` (axioms: none),
  `absence_carried_downward_closed` (at any fixed pair of assembly points the imports leaving the distinction
  absence-carried are downward closed, so the carriage split is order-theoretic) and
  `cross_absence_carried_of_absent_factor` (an absent factor hands its coordinate's carriage to the import)
  (Model/AssemblageRelations.lean). axioms: {propext, Classical.choice, Quot.sound}.
- 9.20 THEOREM. The structure of variance: `structure_of_variance` (Model/AssemblageRelations.lean). With fixed
  factors over an arbitrary finite product carrier, the free region is a faithful order-copy of the
  classification space one level in: a meet-embedding with kernel exactly cross-agreement, injective on
  cross-supported representatives, whose image carries a bottom, that bottom alone, plural incomparable maxima,
  and a downward-closed present-and-absence split. Variance is not a second axis; it is the same structure
  re-entering at the cross region.

  TWO HOMES, and the split is real. The embedding half needs nothing from the absence shelf and lives in
  Model/NaryAssemblage as 9.18; the carriage clause needs `presentCarried` and lives here; the conjunction that
  is the theorem lands here, in the first module that sees both. The generality minimum over the clauses is
  `Inhabited` fibres, contributed by the maxima clause alone. axioms: {propext, Classical.choice, Quot.sound}.
- 9.21 THEOREM. The one feature that is not a copy: `TwoCoord`, `swapP`, `swapP_involutive`,
  `swapP_differsInOne`, `swap_fixes_cross`, `swapImp`, `swapFactors`, and `swap_transport`
  (Model/AssemblageRelations.lean). Relabelling an assembly by the coordinate swap equals the assembly of the
  swapped import under the SWAPPED FACTORS, so the swap is not a symmetry at fixed factors: it relates the
  construction over one factor family to the construction over another. That is a statement about the pair of
  parts, not structure inside the free part, which is why it does not join the package. Stated on a homogeneous
  two-coordinate carrier, in its own section. axioms: {propext, Classical.choice, Quot.sound}.

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
