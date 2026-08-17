import Chiralogy.Model.Stance
import Chiralogy.Model.NaryAssemblage
import Chiralogy.Model.Moves
import Chiralogy.Kernel.Apophatic
import Mathlib.Data.Fintype.Pi

/-! # The repair / healing and cross-scale-dynamics survey

A SURVEY. Two questions. REPAIR: from a pathology, a corner, is there a move that returns the system toward
health, the interior. Is repair always AVAILABLE but never FORCED, or is some pathology an irreversible trap.
CROSS-SCALE DYNAMIC: does a move at a lower scale CHANGE a higher scale's health-status, the one place a
genuine cross-scale dynamic, not static recursion, could live.

The arc is no-arrow, so spontaneous healing, a pull back to health, is expected DEAD, while repair as an
available move is expected RICH, the corners escaping toward opening. Distinguish AVAILABLE, a move exists,
from FORCED, a flow pulls. Guard the cross-scale part hardest: the multi-scale survey found recursion STATIC,
so a cross-scale dynamic would be the first coupling; expect RE-COMPUTATION, the outer status being a function
of inner cells, not causation. Do not report re-reading as coupling.

Register neutral: readings are prose only. Nothing touches canonical or the stance core.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Chiralogy
namespace RepairHealing

/-! ## PART A: repair as a move, available versus forced -/

section Repair

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

/-- **THE COMMITTED CORNER IS ALWAYS REPAIRABLE BY A RELEASE.** From a total configuration, releasing exactly
one off-diagonal cell reopens it while every other cell stays held, landing back in the mobile interior. So
repair from the committed death is AVAILABLE, and it is a RELEASE, the inward move the corner already permits.
Carrier-general, given two distinct points. -/
theorem committed_corner_can_be_repaired {c : Pt X → Pt X → Option Bool} (h : isTotal c)
    {a b : Pt X} (hab : a ≠ b) :
    Mobile (partialization (fun x y => decide (x = a ∧ y = b)) c) := by
  refine mobile_iff.mpr ⟨⟨a, a, ?_⟩, ⟨a, b, ?_⟩⟩
  · have hw : (fun x y => decide (x = a ∧ y = b)) a a = false :=
      decide_eq_false (fun hh => hab hh.2)
    unfold partialization
    rw [hw]
    simpa using h a a
  · have hw : (fun x y => decide (x = a ∧ y = b)) a b = true :=
      decide_eq_true ⟨rfl, rfl⟩
    unfold partialization
    rw [hw]
    simp

/-- **THE WITHDRAWN CORNER IS ALWAYS REPAIRABLE BY A TARGETED FILL.** From the empty configuration, committing
exactly one off-diagonal cell lands in the mobile interior, `oneCell_mobile`, and the empty configuration sits
below it, a fill upward. So repair from the withdrawn death is AVAILABLE, and it is a FILL. Carrier-general,
given two distinct points. -/
theorem withdrawn_corner_can_be_repaired {a b : Pt X} (hab : a ≠ b) :
    cLE (botC (Pt X)) (oneCell a b true) ∧ Mobile (oneCell a b true) :=
  ⟨fun _ _ => Or.inl rfl, oneCell_mobile hab true⟩

/-- **BUT THE BLUNT CANONICAL MOVES OVERSHOOT: THEY SWAP CORNERS, MISSING THE INTERIOR.** The blunt fill from
the empty configuration totalizes it straight to the committed corner, `filling_has_no_intermediate_step`,
still a corner, not the interior; symmetrically the blunt release, dropping everything, sends the committed
corner to the empty one. So repair to health needs a TARGETED move; the blunt extremes only exchange the two
deaths. Carrier-general. -/
theorem the_blunt_moves_overshoot_to_the_other_corner (s : Pt X → Nat)
    {c : Pt X → Pt X → Option Bool} (_h : isTotal c) :
    (isTotal (totalization s (botC (Pt X))) ∧ ¬ Mobile (totalization s (botC (Pt X))))
      ∧ applyStance (dropAll : Stance X) c = botC (Pt X) := by
  refine ⟨⟨totalization_totalizes s _, ?_⟩, applyStance_dropAll c⟩
  exact (the_band_has_two_exits _).mpr (Or.inr (totalization_totalizes s _))

/-- **NO CORNER IS AN IRREVERSIBLE TRAP: HEALTH IS ALWAYS RE-REACHABLE.** From either death a single move
reaches the mobile interior: an upward targeted fill from the empty corner, a downward release from the
committed corner. So on any carrier with two distinct points there is no pathology from which health cannot be
regained. Repair is universally AVAILABLE. Carrier-general. -/
theorem no_corner_is_a_trap {c : Pt X → Pt X → Option Bool} (hcorner : ¬ Mobile c)
    {a b : Pt X} (hab : a ≠ b) :
    ∃ c' : Pt X → Pt X → Option Bool, (cLE c' c ∨ cLE c c') ∧ Mobile c' := by
  rcases (the_band_has_two_exits c).mp hcorner with rfl | htot
  · exact ⟨oneCell a b true, Or.inr (fun _ _ => Or.inl rfl), oneCell_mobile hab true⟩
  · exact ⟨partialization (fun x y => decide (x = a ∧ y = b)) c,
      Or.inl (partialization_le_c _ c), committed_corner_can_be_repaired htot hab⟩

/-- **YET REPAIR IS NEVER FORCED: A CORNER CAN STAY.** The committed corner is a fixed point of forming
everywhere, `formAll_fixes_the_saturated`, and the empty corner is fixed by every release, so from either
death there is a move that does not repair. Nothing compels the return to health: repair is AVAILABLE, not
FORCED, matching the no-arrow arc. Carrier-general. -/
theorem repair_is_available_not_forced {c : Pt X → Pt X → Option Bool} (h : isTotal c)
    (w : Pt X → Pt X → Bool) :
    applyStance (formAll : Stance X) c = c
      ∧ partialization w (botC (Pt X)) = botC (Pt X) := by
  refine ⟨formAll_fixes_the_saturated h, ?_⟩
  funext x y
  simp only [partialization]
  cases w x y <;> rfl

end Repair

/-! ## PART B: the asymmetry, healing is not undoing -/

section Asymmetry

/-- **HEALING IS A NEW MOVE, NOT THE INVERSE OF THE DAMAGE.** Reaching the committed death by totalizing is
IRREVERSIBLE, `totalization_irreversible`, no operation recovers the pre-fill configuration, and the fill is
not faithful, `totalization_not_faithful`, distinct configurations totalize to the same corner, so the corner
forgets its origin. Thus repair cannot be the inverse of the totalization that caused the pathology; the
available repair, a RELEASE (Part A), is a DIFFERENT move that reaches health anew without restoring the prior
state. Dying and healing are not inverse: healing is doing something new, not undoing the damage. -/
theorem the_repair_asymmetry :
    (¬ ∃ recover : (Fin 2 → Fin 2 → Option Bool) → (Fin 2 → Fin 2 → Option Bool),
        ∀ c, recover (totalization (fun _ => 0) c) = c)
      ∧ (∃ c c' : Fin 2 → Fin 2 → Option Bool, c ≠ c' ∧
          totalization (fun _ => 0) c = totalization (fun _ => 0) c') :=
  ⟨totalization_irreversible, totalization_not_faithful⟩

end Asymmetry

/-! ## PART C: cross-scale repair, dynamic or re-computation -/

section CrossScale

abbrev Yb : Fin 2 → Type := fun _ => Bool
abbrev iA : Pt Yb := fun _ => false
abbrev iB : Pt Yb := fun _ => true
abbrev Oc : Fin 2 → Type := fun _ => Pt Yb
abbrev oA : Pt Oc := fun _ => iA
abbrev oB : Pt Oc := Function.update oA 0 iB

/-- The inner factor with one cell released, a holed classification. -/
abbrev innerHoled : Pt Yb → Pt Yb → Option Bool :=
  partialization (fun x y => decide (x = iA ∧ y = iB)) cTrue

theorem oB_zero : oB 0 = iB := Function.update_self 0 iB oA

theorem outer_differs : differsInOne oA oB 0 := by
  refine ⟨?_, fun j hj => (Function.update_of_ne hj iB oA).symm⟩
  rw [oB_zero]; decide

/-- **CROSS-SCALE REPAIR IS FUNCTORIAL RE-COMPUTATION, NOT A COUPLING.** The assembly map is MONOTONE in its
inner factor, `nary_mono`: if the inner factor is released, lowered in the information order, the outer whole
built from it is lowered too. So an inner release induces an outer release THROUGH the fixed assembly
function, order-preservingly. The outer status is a function of the inner factor, re-evaluated, not an inner
event causing an outer one. This is RE-COMPUTATION, and it is the honest content of cross-scale repair: no
genuine cross-scale dynamic, the fractal-static finding stands. Carrier-general in the inner data. -/
theorem an_inner_release_induces_an_outer_release
    {m : ℕ} {Y : Fin m → Type} [∀ j, DecidableEq (Y j)] [DecidableEq (Pt Y)]
    (f g : Pt Y → Pt Y → Option Bool)
    (impOuter : Pt (fun _ : Fin 2 => Pt Y) → Pt (fun _ : Fin 2 => Pt Y) → Option Bool)
    (h : cLE f g) :
    cLE (nary (fun _ : Fin 2 => f) impOuter) (nary (fun _ : Fin 2 => g) impOuter) :=
  nary_mono (fun _ => h) (fun _ _ => optLE_refl _)

/-- **AND THE FLIP IS WITNESSED, AS A RE-READING.** With a TOTAL inner factor the outer whole is total, a
corner; substituting the HOLED inner factor makes the same outer part cell open, so the outer whole is now
mobile, an interior. The outer health-status flipped from corner to interior, but only because the composite
was recomputed with a different inner factor: the outer whole is a fixed function of the inner data, and the
flip is that function re-evaluated, not an inner cell reaching up to change the outer. RE-COMPUTATION, not
causation. -/
theorem the_outer_flip_is_a_recomputation :
    ¬ Mobile (nary (fun _ : Fin 2 => (cTrue : Pt Yb → Pt Yb → Option Bool))
        (cTrue : Pt Oc → Pt Oc → Option Bool))
      ∧ Mobile (nary (fun _ : Fin 2 => innerHoled) (cTrue : Pt Oc → Pt Oc → Option Bool)) := by
  refine ⟨?_, ?_⟩
  · refine (the_band_has_two_exits _).mpr (Or.inr ?_)
    exact nary_isTotal (fun _ _ _ => Option.some_ne_none _) (fun _ _ => Option.some_ne_none _)
  · refine mobile_iff.mpr ⟨⟨oA, oA, ?_⟩, ⟨oA, oB, ?_⟩⟩
    · rw [nary_apply_imp (fun _ => innerHoled) (cTrue : Pt Oc → Pt Oc → Option Bool) (diagAt oA)]
      exact Option.some_ne_none _
    · rw [nary_apply_differ (fun _ => innerHoled) (cTrue : Pt Oc → Pt Oc → Option Bool) outer_differs]
      show innerHoled (oA 0) (oB 0) = none
      rw [oB_zero]
      have hw : (fun x y => decide (x = iA ∧ y = iB)) (oA 0) iB = true :=
        decide_eq_true ⟨rfl, rfl⟩
      unfold innerHoled partialization
      rw [hw]
      simp

end CrossScale

/-! ## The verdict, as prose

PART A, repair as a move. Repair is AVAILABLE from every corner and never FORCED. From the committed death a
RELEASE reopens a cell and returns to the interior (`committed_corner_can_be_repaired`); from the empty death
a TARGETED FILL commits a cell and returns to the interior (`withdrawn_corner_can_be_repaired`). No corner is
an irreversible trap: on any carrier with two distinct points health is always re-reachable
(`no_corner_is_a_trap`). But the blunt canonical extremes OVERSHOOT, swapping the two corners and missing the
interior (`the_blunt_moves_overshoot_to_the_other_corner`), so repair needs a targeted move. And nothing
compels it: each corner is a fixed point of some move (`repair_is_available_not_forced`), so repair is
AVAILABLE, not FORCED, exactly the no-arrow arc, no spontaneous healing pull, only an unforced path.

PART B, the asymmetry. Healing is a NEW move, not the inverse of the damage. Reaching the committed death by
totalizing is irreversible and the fill is not faithful, so the corner forgets its origin
(`the_repair_asymmetry`); the pre-pathology state cannot be recovered by undoing the fill. Repair is therefore
a DIFFERENT move, a release, that reaches health anew rather than restoring the prior state. Dying by
committing and healing by releasing are not inverse operations: healing is doing something new, and the damage
qua information loss is not undone by it.

PART C, cross-scale repair, guarded hardest. It is RE-COMPUTATION, not a genuine dynamic. The assembly map is
monotone in the inner factor (`an_inner_release_induces_an_outer_release`), so an inner release induces an
outer release order-preservingly, through the fixed composite. The outer health-status can flip from corner to
interior when the inner factor is replaced by a released one (`the_outer_flip_is_a_recomputation`), but only
because the outer whole is a fixed FUNCTION of the inner data, re-evaluated: the inner cell does not reach up
and cause an outer change, the composite is recomputed with a different input. So cross-scale repair is the
static assembly function re-read, NOT a coupling; the fractal-static finding stands, and no genuine cross-scale
dynamic exists.

THE VERDICT. Repair is AVAILABLE-not-forced: a move back to health exists from every corner, no pathology is a
trap, and nothing compels the return, but the blunt extremes overshoot so repair is a targeted move. The
asymmetry is real: healing is a DIFFERENT move than undoing the damage, since the damage is irreversible and
origin-forgetting, so healing does something new rather than reversing. And cross-scale repair is static
RE-COMPUTATION, the outer status a monotone function of the inner factor re-evaluated, not an inner-causes-outer
dynamic. So the framework heals freely but never spontaneously, forgets what it repairs, and couples nothing
across scale, a permissive, memoryless, decoupled repair structure consistent with the whole arc.

Register readings, output only. A system in a fully committed or fully empty state can always be brought back
to a working middle by the right small move, and there is always such a move, but nothing drives the system to
take it, so recovery is possible everywhere and automatic nowhere. Fixing a system is not the same as reversing
what broke it: once it has collapsed one way the original cannot be restored, so repair is a fresh act that
reaches a healthy state without recovering the old one. And when a system is built from sub-systems, mending a
part does change the health of the whole, but only in the sense that the whole is defined from its parts and is
simply re-read, not because the part sends any influence upward, so there is no genuine action of a part upon
the whole beyond recomputation.
-/

/-! ## The named targets -/

section Checks
#check @committed_corner_can_be_repaired
#check @withdrawn_corner_can_be_repaired
#check @the_blunt_moves_overshoot_to_the_other_corner
#check @no_corner_is_a_trap
#check @repair_is_available_not_forced
#check @the_repair_asymmetry
#check @an_inner_release_induces_an_outer_release
#check @the_outer_flip_is_a_recomputation
end Checks

#print axioms committed_corner_can_be_repaired
#print axioms withdrawn_corner_can_be_repaired
#print axioms the_blunt_moves_overshoot_to_the_other_corner
#print axioms no_corner_is_a_trap
#print axioms repair_is_available_not_forced
#print axioms the_repair_asymmetry
#print axioms an_inner_release_induces_an_outer_release
#print axioms the_outer_flip_is_a_recomputation

end RepairHealing
end Chiralogy
