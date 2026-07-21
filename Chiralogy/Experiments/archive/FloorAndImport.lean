import Chiralogy

/-! # Experiment: where is the floor, and is the import constrained?

`SafeRegion` found the region bounded above and open below, testing only closure: closing moves over grounds and
never reached the floor. Two questions it left. First, whether opening has a bound: opening is partialization, a
move on classifications, the same space as non-degeneracy, so unlike closing it may reach the floor. Second,
whether an assemblage's import is constrained by its factors, `construction_takes_two_objects_and_a_cross_map`
having left the import free on the fully-cross region. Compute all candidates across the six registers before
judging. Domain content IMPORTED. Stays in `Experiments/`; canonical untouched; nothing resolved.

Carrier is the grounds, as in `SafeRegion`: physics `Fin 1`, the chain and mixed and fork orders `Fin 3`,
chemistry and trust `Fin 4`. -/

open Chiralogy

namespace Chiralogy.FloorAndImport

/-- The identity classifier on the grounds: non-degenerate for `n ≥ 2`. -/
def baseCls (n : ℕ) : Fin n → Fin n → Option Bool := fun i j => if i = j then some true else none

/-- Two factor classifications, for the import test. -/
def fc1 : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none
def fc2 : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none

/-! ## Part 1: floor candidates -/

/-- **Total opening.** The symmetric move to the ceiling: open every pair, returning an absence everywhere. It is
faithful, the payload firing, yet it distinguishes nothing, so it fails Member. The floor is reachable in the
opposite direction to closing. -/
theorem total_opening :
    (¬ Function.Surjective (fun _ _ => none : Fin 3 → Fin 3 → Option Bool))
    ∧ (¬ NonDegenerate (fun _ _ => none : Fin 3 → Fin 3 → Option Bool)) := by
  refine ⟨hole_uniform _, ?_⟩; unfold NonDegenerate; decide

/-- **Partialization is bounded by the total opening.** Opening every pair, the full partialization of any
classification, is the total opening: repeated opening has the total opening as its limit. -/
theorem partialization_bound {n : ℕ} (c : Fin n → Fin n → Option Bool) :
    partialization (fun _ _ => true) c = (fun _ _ => none) := by
  funext x y; simp [partialization]

/-- **The empty closure is merely the bottom.** Closing nothing is closeable, the bottom of the closure lattice,
but the base there is a member, non-degenerate, so the empty closure is not the floor; opening continues beneath
it, partializing the base down to the total opening. -/
theorem empty_closure :
    (closeable prereqChain3 (fun _ => false))
    ∧ (NonDegenerate (baseCls 3))
    ∧ (partialization (fun _ _ => true) (baseCls 3) = (fun _ _ => none)) := by
  refine ⟨by decide, ?_, ?_⟩
  · unfold NonDegenerate; decide
  · funext x y; simp [partialization]

/-- **Vacating is an exit only when constant.** Totalization reaches a total classification, no absence, by
movement; a constant total classification is degenerate, an exit; but a non-constant total classification is still
a member. So the total-classification end is an exit only when it collapses to a constant. -/
theorem vacating_as_exit :
    (∀ x y, totalization (fun _ => 0) (baseCls 3) x y ≠ none)
    ∧ (¬ NonDegenerate (fun _ _ => some true : Fin 3 → Fin 3 → Option Bool))
    ∧ (NonDegenerate (fun x _ => some (decide (x = (0 : Fin 3))) : Fin 3 → Fin 3 → Option Bool)) := by
  refine ⟨totalization_totalizes _ _, ?_, ?_⟩
  · unfold NonDegenerate; decide
  · unfold NonDegenerate; decide

/-- **No grounds at all.** A register with no declared grounds has a trivial closure lattice, a single point, no
movement; yet it can be a member, non-degeneracy being a condition on the carrier not the grounds. It sits as a
fixed point, neither near ceiling nor floor. -/
theorem no_grounds_at_all :
    ((Finset.univ.filter (fun S : Fin 0 → Bool => closeable prereqDiscrete S)).card = 1)
    ∧ (NonDegenerate (fun x _ => some (decide (x = (0 : Fin 2))) : Fin 2 → Fin 2 → Option Bool)) := by
  refine ⟨by decide, ?_⟩; unfold NonDegenerate; decide

/-- **Across the six.** The total opening fails Member on every carrier, physics `Fin 1`, the `Fin 3` orders, the
`Fin 4` orders; the empty closure is never the floor, its base a member for `n ≥ 2`; and physics is the exception,
its single ground leaving the base already degenerate. -/
theorem compute_across_the_six :
    (¬ NonDegenerate (fun _ _ => none : Fin 1 → Fin 1 → Option Bool))
    ∧ (¬ NonDegenerate (fun _ _ => none : Fin 3 → Fin 3 → Option Bool))
    ∧ (¬ NonDegenerate (fun _ _ => none : Fin 4 → Fin 4 → Option Bool))
    ∧ (NonDegenerate (baseCls 3))
    ∧ (NonDegenerate (baseCls 4))
    ∧ (¬ NonDegenerate (baseCls 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold NonDegenerate; decide)

/-! ## Part 2: is the region bounded twice after all? -/

/-- **The total opening is the floor.** It is reachable by opening moves, the full partialization of any
classification, and it fails Member, degenerate though faithful. So opening reaches the floor where closing did
not: the region is bounded below after all, by degeneracy through opening. -/
theorem is_total_opening_the_floor :
    (partialization (fun _ _ => true) (baseCls 3) = (fun _ _ => none))
    ∧ (¬ NonDegenerate (fun _ _ => none : Fin 3 → Fin 3 → Option Bool))
    ∧ (¬ Function.Surjective (fun _ _ => none : Fin 3 → Fin 3 → Option Bool)) := by
  refine ⟨?_, ?_, hole_uniform _⟩
  · funext x y; simp [partialization]
  · unfold NonDegenerate; decide

/-- **The two bounds are not symmetric.** The ceiling collides: complete and faithful together are impossible, so
closing everything is forbidden. The floor merely degenerates: the total opening is permitted, asserting no
falsehood against any target, yet it distinguishes nothing. The ceiling forbids, an overshoot into inconsistency;
the floor empties, a shortfall into indistinguishability. One collides, the other is merely degenerate. -/
theorem are_the_two_bounds_symmetric :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2)
    ∧ (∀ (t : Fin 3 → Fin 3 → Bool) (x y : Fin 3), ¬ assertsFalse (fun _ _ => none) t x y)
    ∧ (¬ NonDegenerate (fun _ _ => none : Fin 3 → Fin 3 → Option Bool)) := by
  refine ⟨complete_and_faithful_is_impossible, fun t x y => ?_, ?_⟩
  · simp [assertsFalse]
  · unfold NonDegenerate; decide

/-! ## Part 3: is the assemblage's import constrained? -/

/-- **The factors do not constrain the import.** For a concrete factor pair, two opposite imports, the absence and
a present verdict, both give a conforming assemblage, the payload firing and non-degeneracy inherited from the
factors: no import is unavailable, none makes conformance fail. -/
theorem do_the_factors_constrain_the_import :
    (NonDegenerate (assembleClassify fc1 fc2 (fun _ _ => none)))
    ∧ (NonDegenerate (assembleClassify fc1 fc2 (fun _ _ => some false)))
    ∧ (¬ Function.Surjective (assembleClassify fc1 fc2 (fun _ _ => none)))
    ∧ (¬ Function.Surjective (assembleClassify fc1 fc2 (fun _ _ => some false))) := by
  refine ⟨?_, ?_, hole_uniform _, hole_uniform _⟩ <;> (unfold NonDegenerate; decide)

/-- **The import is wholly free.** Every import gives a payload-firing assemblage, whatever the factors: the
conformance condition is independent of the import. So the capacity is supplied at the whole, not restricted by
the factors, and the strain in the capacity reading stands. -/
theorem is_the_import_wholly_free {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool) :
    ∀ imp : (X1 × X2) → (X1 × X2) → Option Bool, ¬ Function.Surjective (assembleClassify c1 c2 imp) :=
  fun _ => hole_uniform _

/-! ## The verdicts

Part 1: the floor candidates. The total opening, opening every pair, is faithful yet fails Member, distinguishing
nothing (`total_opening`), and it is the limit of partialization (`partialization_bound`). The empty closure is
merely the bottom of the closure lattice, its base a member, opening continuing beneath it (`empty_closure`).
Vacating, a total classification, is an exit only when constant, a non-constant total still a member
(`vacating_as_exit`). A register with no grounds is a fixed point, a member with no movement (`no_grounds_at_all`).
Across the six, the total opening fails Member on every carrier and the empty closure never does, physics the
exception at its single ground (`compute_across_the_six`).

Part 2: the region is bounded twice, but asymmetrically. The total opening is the floor, reachable by opening and
failing Member (`is_total_opening_the_floor`); yet the two bounds differ in kind, the ceiling a collision, complete
and faithful impossible, and the floor a mere degeneracy, the total opening permitted but vacuous
(`are_the_two_bounds_symmetric`).

Part 3: the import is free. Two opposite imports both conform (`do_the_factors_constrain_the_import`), and every
import gives a payload-firing assemblage (`is_the_import_wholly_free`): the factors do not constrain it.

The verdict: the floor is the total opening, and the region is bounded twice, but the two bounds are not
symmetric. `SafeRegion` tested only closing, which moves over grounds and could not reach the floor; opening moves
over classifications, the same space as non-degeneracy, and it does reach a floor, the total opening, an absence
everywhere, faithful but distinguishing nothing, the limit of partialization. So the region is bounded below after
all, and the annulus `SafeRegion` could not find exists once opening is admitted. But the two bounds are of
different kinds: the ceiling collides, complete and faithful being impossible together, so it is forbidden, an
overshoot into inconsistency; the floor merely degenerates, the total opening permitted and asserting no
falsehood, yet vacuous, a shortfall into indistinguishability. The ceiling stops you, the floor lets you through
but you are no longer a member. Physics sits at the degenerate edge structurally, its single ground leaving no
distinction; a register with no grounds is a member with no movement, a point; vacating collapses only when it
goes constant. And the assemblage's import is wholly free: no choice of import breaks conformance, so the capacity
is supplied at the whole rather than latent in the factors, and the strain in the capacity reading stands. Both
answers are the honest ones against the wish: the floor exits rather than degrades within, so the annulus is
lopsided, and the import is free, not constrained. Reported per part. Nothing here is resolved. -/

end Chiralogy.FloorAndImport
