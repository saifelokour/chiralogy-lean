import Chiralogy.Model.InformationOrder
import Chiralogy.Model.Moves
import Mathlib.Order.Basic

/-! # The import-overlay survey

A SURVEY. Can the framework host an abstract MAGNITUDE INTERFACE: a monotone map from the framework's own
order into an arbitrary register-supplied ordered carrier V, such that the framework proves
register-INDEPENDENT facts true of ANY such map, or does nothing non-trivial survive across all of them.

An overlay is a monotone `φ : (classifications, cLE) → V` with V an arbitrary preorder. The framework knows
neither V nor φ. The question is PARAMETRICITY: what holds for EVERY monotone φ into EVERY ordered V. This is
NOT universality, the closed no-import-free-universal-property result is not reopened; φ is a free input, not
derived.

No smuggled expectations. DEAD-vacuous, nothing non-trivial surviving, is a first-class outcome. A law that is
only monotonicity restated is vacuous, reported as such. The math decides.

Register neutral: readings are prose only. Nothing touches canonical or the stance core.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Chiralogy
namespace ImportOverlay

/-! ## PART A / B: what transports for ALL monotone φ into ALL ordered V

An overlay hypothesis is `hmono : ∀ c d, cLE c d → φ c ≤ φ d`. Every framework fact of the form `cLE a b`
transports to `φ a ≤ φ b`, and nothing else can, because a monotone map into an arbitrary preorder preserves
exactly the order relation. -/

section Transports

variable {X : Type} {V : Type} [Preorder V] (φ : (X → X → Option Bool) → V)
  (hmono : ∀ c d, cLE c d → φ c ≤ φ d)

include hmono

/-- **THE BOTTOM MAPS TO A LOWER BOUND OF THE IMAGE.** The all-absent classification is below every
classification (`botC_le`), so any monotone overlay sends it to a least element of its image. FORCED, but the
content is entirely the framework fact `botC_le` transported; the φ side is generic monotone behaviour. -/
theorem overlay_bottom_is_a_lower_bound (c : X → X → Option Bool) : φ (botC X) ≤ φ c :=
  hmono _ _ (botC_le c)

/-- **RELEASES DESCEND UNDER THE OVERLAY.** A partialization is below its input (`partialization_le_c`), so any
monotone overlay sends a release at or below where it started. FORCED, the framework's descent direction made
register-independent. -/
theorem overlay_release_descends (w : X → X → Bool) (c : X → X → Option Bool) :
    φ (partialization w c) ≤ φ c :=
  hmono _ _ (partialization_le_c w c)

/-- **FILLS ASCEND UNDER THE OVERLAY.** A totalization is above its input (`c_le_totalization`), so any
monotone overlay sends a fill at or above where it started. FORCED, the framework's ascent direction made
register-independent. -/
theorem overlay_fill_ascends (s : X → Nat) (c : X → X → Option Bool) :
    φ c ≤ φ (totalization s c) :=
  hmono _ _ (c_le_totalization s c)

end Transports

/-! ## PART A gate / PART C ceiling: what does NOT transport

A single collapsing overlay, monotone into ℕ but constant, witnesses that everything beyond the bare
order-relation is erased: strictness, distinctness, and incomparability all collapse. So the overlay preserves
`≤` and NOTHING finer, no gap, no metric, no distinctness. -/

section Collapse

/-- **THE COLLAPSING OVERLAY: MONOTONE YET ERASING EVERYTHING BUT `≤`.** The constant map into ℕ is a valid
monotone overlay. Under it the empty classification and the wholly affirming one, which are DISTINCT and
STRICTLY ordered in the framework, map to the SAME value. So distinctness does not transport, strictness does
not transport, and, since a collapsed image is totally comparable, incomparability does not transport either.
The overlay sees the direction of `≤` and no more: no strict gap, hence no distance or metric content is
register-independent. This is the ceiling. -/
theorem the_collapsing_overlay_erases_all_but_the_order :
    ∃ φ : (Fin 1 → Fin 1 → Option Bool) → Nat,
      (∀ c d, cLE c d → φ c ≤ φ d)
        ∧ (botC (Fin 1) ≠ (cTrue : Fin 1 → Fin 1 → Option Bool))
        ∧ (cLE (botC (Fin 1)) cTrue ∧ ¬ cLE (cTrue : Fin 1 → Fin 1 → Option Bool) (botC (Fin 1)))
        ∧ φ (botC (Fin 1)) = φ (cTrue : Fin 1 → Fin 1 → Option Bool) := by
  refine ⟨fun _ => 0, fun _ _ _ => le_refl 0, ?_, ⟨botC_le _, ?_⟩, rfl⟩
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [botC, cTrue] at this
  · intro h
    rcases h 0 0 with h1 | h1 <;> simp [botC, cTrue] at h1

end Collapse

/-! ## The verdict, as prose

PART A, the vacuity gate. Something survives, but it is exactly the framework's order relation and no more. A
monotone overlay into an arbitrary preorder preserves precisely the `cLE` relation, so every framework theorem
of the form `cLE a b` transports to `φ a ≤ φ b`, and nothing finer can, since the map is an arbitrary
order-homomorphism. The three basic transports are the bottom to a lower bound
(`overlay_bottom_is_a_lower_bound`, from `botC_le`), releases descending
(`overlay_release_descends`, from `partialization_le_c`), and fills ascending (`overlay_fill_ascends`, from
`c_le_totalization`). These are FORCED, but the content is entirely the framework's directional order-facts
transported; the φ side adds nothing. So the honest reading is NOT-vacuous-but-thin: what survives is the
ordinal direction of the two moves and the existence of the bottom, register-independently, and only that.

PART B, the boundary. A fact transports iff it holds for EVERY monotone φ into EVERY ordered V, which is iff it
is a `≤` fact of the framework's order. FORCED: `cLE`-comparabilities, the bottom as a lower bound, the two
move-directions. FREE, needing a specific overlay: DISTINCTNESS of the two deaths (a collapsing φ identifies
them, `the_collapsing_overlay_erases_all_but_the_order`), STRICTNESS (the same collapse sends a strictly-below
pair to an equal pair), and INCOMPARABILITY (a collapsed or linear image makes everything comparable). None of
these transport, so the register-independent overlay is strictly the `≤`-skeleton, weaker than the framework's
own order, which also knows `≠` and incomparability.

PART C, the ceiling. The overlay is ORDINAL-ONLY, and even less: it keeps `≤` but not `<`, so it carries no
gap and hence no DISTANCE or metric. A SUM or additive law is not even expressible, since V is a bare preorder
with no addition; stating φ additive would require V an additive monoid, a specific V, which is drift, not
overlay content. So the quadratic-not-tensor composition result is SILENT on overlay-additivity: additivity
lives in a richer signature the overlay does not have, and there is nothing for the quadratic count to
contradict. A specific VALUE is likewise unreachable, V having no distinguished elements. The ceiling: the
overlay reaches the `≤`-direction and stops, no strictness, no distance, no sum, no value.

PART D, drift. Every candidate law beyond `≤`-transport needs extra structure on V and is therefore a
register's import, not overlay content: distinctness needs a φ that separates (a specific overlay);
meet-preservation needs V a lattice; additivity needs V an additive monoid; a distance needs V a metric; a
value needs a distinguished element of V. Each such proof could not be carried out at the bare
`[Preorder V]` type-variable level, so each is flagged as drift and excluded.

THE VERDICT: PARTIAL, at the thin end. The overlay is not dead-vacuous, the two move-directions and the
order-bottom transport register-independently (`overlay_release_descends`, `overlay_fill_ascends`,
`overlay_bottom_is_a_lower_bound`); but the transported content is exactly the framework's `≤`-facts, the φ
side contributing nothing, and everything finer, distinctness, strictness, incomparability, distance, sum,
value, is FREE or inexpressible (`the_collapsing_overlay_erases_all_but_the_order`). So the framework hosts an
ordinal-direction interface and nothing more: a register may lay an ordered magnitude over the commitment
moves so that releases go down and fills go up, but the framework forces no gap, no distance, no sum, and no
value on it. Magnitude, beyond mere direction, stays entirely register-imported.

Register readings, output only. A system can be given an external scale that respects its direction of change,
so that letting go always scores at or below and committing always at or above, and this much holds no matter
what scale is chosen; but nothing more is guaranteed. The same scale may rate two genuinely different states
identically, may show no gap between a state and one strictly past it, and carries no notion of distance,
total, or absolute value unless the scale itself supplies that structure from outside. The framework fixes the
direction of the ruler, never its spacing.
-/

/-! ## The named targets -/

section Checks
#check @overlay_bottom_is_a_lower_bound
#check @overlay_release_descends
#check @overlay_fill_ascends
#check @the_collapsing_overlay_erases_all_but_the_order
end Checks

#print axioms overlay_bottom_is_a_lower_bound
#print axioms overlay_release_descends
#print axioms overlay_fill_ascends
#print axioms the_collapsing_overlay_erases_all_but_the_order

end ImportOverlay
end Chiralogy
