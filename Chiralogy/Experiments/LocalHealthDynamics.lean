import Chiralogy.Model.Stance
import Chiralogy.Model.NaryAssemblage
import Chiralogy.Model.Moves
import Chiralogy.Kernel.Apophatic
import Mathlib.Data.Fintype.Pi

/-! # The local health-dynamics survey

A SURVEY of the LOCAL dynamics around a configuration, a whole with its parts' statuses. Not global transfer
across a graph, which hit separability, but the immediate neighborhood: the moves available FROM a
configuration and which adjacent ones they reach, and the whole/part LOCAL interplay.

The health/pathology asymmetry is partly proven already: `at_the_committed_death_every_change_is_a_withdrawal`
is a LOCAL all-inward statement. Build on it. Guard: the local gradient at the deaths is real; do not inflate
it into a global forced flow, the arc says none. Characterize the local structure honestly and report
FORCED/FREE/DEAD per feature.

Register neutral: readings are prose only. Nothing touches canonical or the stance core.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Chiralogy
namespace LocalHealthDynamics

/-! ## PART A: the local neighborhood of each configuration-type -/

section Neighborhoods

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

/-- **HEALTH IS A LOCAL INTERIOR POINT.** From any mobile configuration there is a strictly inward move, a
release that drops a held cell and lands strictly below, AND a strictly outward move, a fill that closes an
open cell and lands strictly above. So health escapes in BOTH directions: it is an interior point of the
information order, not a boundary. This is also the local isotropy of C1, no preferred local direction.
Carrier-general. -/
theorem health_is_a_local_interior {c : Pt X → Pt X → Option Bool} (h : Mobile c) :
    (∃ w : Pt X → Pt X → Bool, cLE (partialization w c) c ∧ partialization w c ≠ c)
      ∧ (∃ s : Pt X → Nat, cLE c (totalization s c) ∧ c ≠ totalization s c) := by
  obtain ⟨⟨x0, y0, hx0⟩, ⟨x1, y1, hx1⟩⟩ := mobile_iff.mp h
  refine ⟨⟨fun x y => decide (x = x0 ∧ y = y0), partialization_le_c _ c, ?_⟩,
    ⟨fun _ => 0, c_le_totalization _ c, ?_⟩⟩
  · have hzero : partialization (fun x y => decide (x = x0 ∧ y = y0)) c x0 y0 = none := by
      simp [partialization]
    exact fun heq => hx0 (by rw [← congrFun (congrFun heq x0) y0]; exact hzero)
  · exact fun heq => (totalization_totalizes (fun _ => 0) c x1 y1) (by rw [← heq]; exact hx1)

/-- **THE COMMITTED DEATH IS A LOCAL CORNER.** At a total configuration every release lands at or below,
`partialization_le_c`, so every move is inward, and the fill fixes it, `formAll_fixes_the_saturated`, so
there is no outward move at all. Escape is one-directional: the committed death is a boundary corner, its
sole exit toward opening. This is the local content of `at_the_committed_death_every_change_is_a_withdrawal`.
Carrier-general. -/
theorem the_committed_death_is_a_local_corner {c : Pt X → Pt X → Option Bool} (h : isTotal c) :
    (∀ w : Pt X → Pt X → Bool, cLE (partialization w c) c)
      ∧ applyStance (formAll : Stance X) c = c :=
  ⟨fun w => partialization_le_c w c, formAll_fixes_the_saturated h⟩

/-- **THE WITHDRAWN DEATH IS THE OPPOSITE LOCAL CORNER.** At the empty configuration every release does
nothing, it is already open everywhere, and one fill carries it all the way up to a total configuration. So
escape is again one-directional, toward committing: the opposite corner. The two deaths are the two local
corners, and health is the interior between them. Carrier-general. -/
theorem the_withdrawn_death_is_a_local_corner (s : Pt X → Nat) :
    (∀ w : Pt X → Pt X → Bool, partialization w (botC (Pt X)) = botC (Pt X))
      ∧ isTotal (totalization s (botC (Pt X))) := by
  refine ⟨fun w => ?_, totalization_totalizes s _⟩
  funext x y
  simp only [partialization]
  cases w x y <;> rfl

/-- **THE BAND HAS EXACTLY THE TWO CORNERS AS ITS EXITS.** Non-mobility is precisely being at one of the two
deaths, canonical `the_band_has_two_exits`. So every non-corner configuration is a mobile interior point:
health is the whole interior, the deaths its only two boundary points. Carrier-general. -/
theorem the_neighborhood_types_are_interior_or_corner (c : Pt X → Pt X → Option Bool) :
    ¬ Mobile c ↔ (c = botC (Pt X) ∨ isTotal c) :=
  the_band_has_two_exits c

end Neighborhoods

/-! ## PART A3: local saddles, mixed neighborhoods

A two-factor Bool assemblage whose factors are withdrawn and whose import commits everything. The import
axis is fully committed, inward-only there, while the region axes are fully open, outward-only there. A
single configuration with one axis at a commitment-extreme and another free: a local saddle. -/

section Saddle

abbrev V : Fin 2 → Type := fun _ => Bool
abbrev p0 : Pt V := fun _ => false
abbrev pq : Pt V := fun i => decide (i = 0)

/-- The assemblage with both factors withdrawn and every import committed to `some true`. -/
noncomputable def saddleCfg : Pt V → Pt V → Option Bool :=
  nary (fun _ => botC Bool) (cTrue : Pt V → Pt V → Option Bool)

/-- **A LOCAL SADDLE EXISTS.** The saddle configuration holds every import cell, its cross cells return the
committed import, so on the import axis only withdrawal is available, while it opens every region cell, so on
a region axis only filling is available. Both a held cell and an open cell are present, so the configuration
is mobile, yet its two live directions lie on DIFFERENT axes: committed on import, open on region. A mixed
local neighborhood, inward-only on one axis and outward-only on another. FREE, as a genuine configuration. -/
theorem a_local_saddle_exists :
    saddleCfg p0 p0 = some true
      ∧ saddleCfg p0 pq = none
      ∧ Mobile saddleCfg := by
  have hcross : saddleCfg p0 p0 = some true :=
    nary_apply_imp (fun _ => botC Bool) (cTrue : Pt V → Pt V → Option Bool) (diagAt p0)
  have hdiff : differsInOne p0 pq 0 := by decide
  have hregion : saddleCfg p0 pq = none :=
    nary_apply_differ (fun _ => botC Bool) (cTrue : Pt V → Pt V → Option Bool) hdiff
  refine ⟨hcross, hregion, mobile_iff.mpr ⟨⟨p0, p0, ?_⟩, ⟨p0, pq, hregion⟩⟩⟩
  rw [hcross]; exact Option.some_ne_none _

end Saddle

/-! ## PART B: the whole/part local interplay -/

section WholePart

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- **THE WHOLE HAS A LOCAL MOVE NO PART SEES: THE CROSS CELL.** A diagonal cell is a cross cell, in no
region, so the whole assemblage holds there whatever the import holds, `nary_apply_imp`, while every region
slice is open there, `regionSlice_apply` with `differsInOne a a i` false. So a release or a fill at that
cross cell changes the WHOLE at a cell no part contributes and no part's local neighborhood contains. A
whole-local-only move: the assembly manufactures local structure absent from every part. Carrier-general,
given the import holds the diagonal. -/
theorem the_whole_has_a_cross_local_move_no_part_sees (c : ∀ i, X i → X i → Option Bool)
    (imp : Pt X → Pt X → Option Bool) (a : Pt X) (himp : imp a a ≠ none) :
    nary c imp a a ≠ none ∧ ∀ i, regionSlice i (nary c imp) a a = none := by
  refine ⟨?_, fun i => ?_⟩
  · rw [nary_apply_imp c imp (diagAt a)]; exact himp
  · rw [regionSlice_apply, if_neg]; rintro ⟨h, -⟩; exact h rfl

end WholePart

section CornerWithOpenParts

/-- **THE WHOLE CAN BE A LOCAL CORNER WHILE EVERY PART IS A LOCAL INTERIOR.** The wholly committed assemblage
is total, so as a whole it is at the committed death, a local corner with only-inward moves. Yet each region
slice is mobile, `mobile_regionSlice_iff` supplying a held region cell against the always-open diagonal, so
each part is a local interior point with both-direction escape. The whole is locally stuck where every part
is locally open: the LOCAL form of whole/part non-additivity, the assembly having its own local pathology no
part carries. -/
theorem the_whole_can_be_a_corner_with_open_parts :
    isTotal (cTrue : Pt V → Pt V → Option Bool)
      ∧ (∀ w : Pt V → Pt V → Bool, cLE (partialization w (cTrue : Pt V → Pt V → Option Bool)) cTrue)
      ∧ Mobile (regionSlice 0 (cTrue : Pt V → Pt V → Option Bool))
      ∧ Mobile (regionSlice 1 (cTrue : Pt V → Pt V → Option Bool)) := by
  have e0 : differsInOne p0 pq 0 := by decide
  have e1 : differsInOne p0 (fun i => decide (i = 1)) 1 := by decide
  refine ⟨fun _ _ => Option.some_ne_none _, fun w => partialization_le_c w cTrue, ?_, ?_⟩
  · exact (mobile_regionSlice_iff 0 cTrue p0).mpr ⟨p0, pq, e0, Option.some_ne_none _⟩
  · exact (mobile_regionSlice_iff 1 cTrue p0).mpr
      ⟨p0, fun i => decide (i = 1), e1, Option.some_ne_none _⟩

end CornerWithOpenParts

/-! ## PART B3: the local coupling -/

section Coupling

/-- **A MOVE AT ONE CELL LEAVES EVERY OTHER CELL'S LOCAL NEIGHBORHOOD UNCHANGED.** A targeted release at one
named cell changes only that cell: at any other cell the configuration keeps its value, hence keeps its
held-or-open status, hence keeps exactly the moves locally available there. So the moves are cell-local and
DECOUPLED, a move nowhere reshapes another cell's neighborhood. Local coupling is DEAD at the cell level,
matching the no-status-transfer finding. Carrier-general. -/
theorem a_move_at_one_cell_leaves_another_cells_status_unchanged {X : Type} [DecidableEq X]
    (A : X → X → Option Bool) (a b : X) {x y : X} (h : ¬ (x = a ∧ y = b)) :
    partialization (fun p q => decide (p = a ∧ q = b)) A x y = A x y := by
  simp only [partialization]
  rw [if_neg (by simp [h])]

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

/-- **THE ONE COUPLING IS GLOBAL, NOT LOCAL: THE BAND EXIT.** Whether a configuration is a mobile interior or
a corner is a GLOBAL predicate of the whole, being empty everywhere or total everywhere, canonical
`the_band_has_two_exits`. So while per-cell moves are decoupled, the last release that empties the final held
cell flips the whole neighborhood from interior to corner. The only coupling reshaping neighborhoods is this
global band-membership threshold, not a local per-cell influence. Carrier-general. -/
theorem the_only_coupling_is_the_global_band_exit (c : Pt X → Pt X → Option Bool) :
    ¬ Mobile c ↔ (c = botC (Pt X) ∨ isTotal c) :=
  the_band_has_two_exits c

end Coupling

/-! ## PART C: the local flow structure -/

section Flow

/-- **RELABELLING IS A LOCALLY REVERSIBLE DIRECTION.** Relabelling by a bijection is undone by relabelling by
its inverse, so around any configuration the relabelling directions are reversible: the register can be moved
and moved back. Carrier-general. -/
theorem relabel_is_locally_reversible {X : Type} (e : X ≃ X) (A : X → X → Option Bool) :
    relabel e.symm (relabel e A) = A := by
  funext a b; simp [relabel, e.apply_symm_apply]

/-- The one-cell configuration holding `some false`, over a one-factor Bool carrier. -/
abbrev W : Fin 1 → Type := fun _ => Bool
abbrev wf : Pt W := fun _ => false

/-- **BUT A RELEASE IS A LOCALLY IRREVERSIBLE DIRECTION.** Release a cell that held `some false`; the
affirming fill, the canonical outward move, refills it with `some true`, not the value that was there. The
withdrawn value is not recoverable from the configuration, canonical `totalization_irreversible` says no
operation recovers it in general. So the local neighborhood is a MIX: relabelling reversible, release and
fill not, some escapes undoable and some not. -/
theorem a_release_is_not_inverted_by_the_affirming_fill :
    let A : Pt W → Pt W → Option Bool := fun _ _ => some false
    A wf wf = some false
      ∧ applyStance (formAll : Stance W)
          (partialization (fun p q => decide (p = wf ∧ q = wf)) A) wf wf ≠ A wf wf := by
  intro A
  refine ⟨rfl, ?_⟩
  have hrel : partialization (fun p q => decide (p = wf ∧ q = wf)) A wf wf = none := by
    simp [partialization, A]
  rw [applyStance_formAll, if_pos hrel]
  show (some true : Option Bool) ≠ some false
  decide

end Flow

/-! ## The verdict, as prose

PART A, the local neighborhoods. HEALTH is a local INTERIOR point: from any mobile configuration there is a
strictly inward release and a strictly outward fill (`health_is_a_local_interior`), escape in both
directions. The two DEATHS are local CORNERS: at the committed death every move is inward and the fill fixes
it (`the_committed_death_is_a_local_corner`, the local content of the canonical all-inward statement); at the
withdrawn death every release does nothing and one fill escapes upward (`the_withdrawn_death_is_a_local_corner`).
And these corners are the band's only two exits (`the_neighborhood_types_are_interior_or_corner`), so health
is the entire interior. A3, SADDLES exist: a configuration committed on the import axis and open on the region
axes is mobile with its two live directions on different axes (`a_local_saddle_exists`), a mixed neighborhood
inward-only on one axis and outward-only on another. So the local shape is FORCED and asymmetric: interior
versus corner, with genuine saddles between.

PART B, the whole/part local interplay, is where the local structure is RICH. B1, the whole has WHOLE-LOCAL-ONLY
moves: the diagonal cross cell is held by the whole yet lies in no region slice
(`the_whole_has_a_cross_local_move_no_part_sees`), so a move there belongs to no part, the assembly
manufacturing local structure absent from every part. B2, the whole can be a local CORNER while every part is
a local INTERIOR: the wholly committed assemblage is total, a corner, yet each region slice is mobile
(`the_whole_can_be_a_corner_with_open_parts`), the whole locally stuck where each part is locally open, the
LOCAL form of whole/part non-additivity. B3, local COUPLING at the cell level is DEAD: a move at one cell
leaves every other cell's value, and hence its available moves, unchanged
(`a_move_at_one_cell_leaves_another_cells_status_unchanged`), so moves are decoupled, matching the
no-status-transfer finding; the only coupling that reshapes neighborhoods is GLOBAL, the band-exit threshold
(`the_only_coupling_is_the_global_band_exit`), the last release flipping interior to corner, not a local
per-cell influence.

PART C, the local flow. C1, the GRADIENT is real only at the corners: the deaths have all moves one way
(`the_committed_death_is_a_local_corner`, `the_withdrawn_death_is_a_local_corner`), while the interior is
locally ISOTROPIC, both directions available with no preferred one (`health_is_a_local_interior`). So there is
a local gradient at the boundary and none in the interior, and this is NOT a global forced flow: the interior
being isotropic is exactly the no-arrow finding, the boundary gradient does not propagate inward. C2,
REVERSIBILITY is mixed: relabelling is locally reversible (`relabel_is_locally_reversible`), while a release
is not inverted by the affirming fill (`a_release_is_not_inverted_by_the_affirming_fill`), canonical
`totalization_irreversible` confirming the fill loses information; so the local neighborhood mixes reversible
relabel directions with irreversible commitment directions.

THE VERDICT: RICH. The local dynamics has real structure, not merely the product of the parts'. Health is a
local interior with both-direction escape; the deaths are one-directional corners; saddles mix the two axes.
And the whole/part local interplay is genuinely non-additive: the whole has cross-cell moves no part has, and
the whole can sit at a local corner while every part is a local interior. Local coupling at the cell level is
DEAD, moves are decoupled, but that is itself informative: the only coupling is the global band threshold. The
local flow has a gradient at the corners and an isotropic interior, so the boundary orientation does not become
a global arrow, and reversibility is mixed, relabel undoable and commitment not. The neighborhood is thus richly
shaped at each point and in the whole/part relation, while remaining directionless in its interior, consistent
with the whole arc: real local geometry, no forced global flow.

Register readings, output only. Around a healthy system every small change is possible in both directions, it
can lose a little or gain a little, while a fully committed or fully empty system can only move one way, back
toward the middle. A system committed on one aspect and open on another sits at a mixed point, stuck one way
and free another. A whole assembly has moves of its own that none of its parts have, at the seams where the
parts join, and a whole can be locally frozen while each of its parts is still locally free. Changing one part
does not change what moves are open elsewhere, the parts are locally independent, and the only thing that
reshapes the whole neighborhood is crossing all the way to an extreme. There is a pull only at the extremes,
none in the healthy middle, and moving a system around is undoable while committing it is not.
-/

/-! ## The named targets -/

section Checks
#check @health_is_a_local_interior
#check @the_committed_death_is_a_local_corner
#check @the_withdrawn_death_is_a_local_corner
#check @the_neighborhood_types_are_interior_or_corner
#check @a_local_saddle_exists
#check @the_whole_has_a_cross_local_move_no_part_sees
#check @the_whole_can_be_a_corner_with_open_parts
#check @a_move_at_one_cell_leaves_another_cells_status_unchanged
#check @the_only_coupling_is_the_global_band_exit
#check @relabel_is_locally_reversible
#check @a_release_is_not_inverted_by_the_affirming_fill
end Checks

#print axioms health_is_a_local_interior
#print axioms the_committed_death_is_a_local_corner
#print axioms the_withdrawn_death_is_a_local_corner
#print axioms the_neighborhood_types_are_interior_or_corner
#print axioms a_local_saddle_exists
#print axioms the_whole_has_a_cross_local_move_no_part_sees
#print axioms the_whole_can_be_a_corner_with_open_parts
#print axioms a_move_at_one_cell_leaves_another_cells_status_unchanged
#print axioms the_only_coupling_is_the_global_band_exit
#print axioms relabel_is_locally_reversible
#print axioms a_release_is_not_inverted_by_the_affirming_fill

end LocalHealthDynamics
end Chiralogy
