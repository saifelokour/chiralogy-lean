import Chiralogy

/-! # Experiment: is the permitted region bounded twice?

The prohibition bounds above; non-degeneracy may bound below. Test whether the viable region is a two-bounded
space and whether the two bounds behave alike. Imported comparison (Raworth): a region bounded on the inside by a
social foundation and outside by an ecological ceiling, viability the annulus, shortfall below and overshoot above,
the dimensions multiple and independent. The framework has no measure, so any correspondence is topological, which
combinations are viable, with no distance from an edge. Domain content IMPORTED, the doughnut correspondence a
READING. Compute across all six registers before judging. Stays in `Experiments/`; canonical untouched; nothing
resolved.

The closure lattice is over grounds (`Fin n → Bool`), the full closure the prohibition. To test whether closing
can reach the floor, a closure acts on a classification on the carrier of grounds: `baseCls` is the identity
classifier (each ground true on its diagonal, absent elsewhere, non-degenerate for `n ≥ 2`), and closing a ground
totalizes its row (fills its absences, flat scale). -/

open Chiralogy

namespace Chiralogy.SafeRegion

/-- The identity classifier on the grounds: each ground true on its own diagonal, absent elsewhere. -/
def baseCls (n : ℕ) : Fin n → Fin n → Option Bool := fun i j => if i = j then some true else none

/-- Closing a ground totalizes its row: fill its absences with a verdict, keeping the present ones. -/
def fillClosure {n : ℕ} (S : Fin n → Bool) (c : Fin n → Fin n → Option Bool) : Fin n → Fin n → Option Bool :=
  fun i j => if S i then some ((c i j).getD true) else c i j

/-! ## Part 1: the two bounds -/

/-- **The ceiling is the prohibition.** The full closure is closeable and is the top of the inclusion order, every
closure below it, and it is the unique closure closing everything: an upper bound, beyond which is inconsistency. -/
theorem ceiling_is_the_prohibition :
    (closeable prereqChain3 (fun _ => true))
    ∧ (∀ S : Fin 3 → Bool, ∀ i, S i = true → (fun _ => true : Fin 3 → Bool) i = true)
    ∧ (∀ S : Fin 3 → Bool, (∀ i, S i = true) → S = (fun _ => true)) := by
  refine ⟨by decide, fun _ _ _ => rfl, ?_⟩
  intro S h; funext i; exact h i

/-- **The floor is non-degeneracy, an exit not a degradation.** A degenerate classification fails the
distinguishing requirement and is not a member at all; whereas below the ceiling a permitted closure is still
closeable, still in the lattice. Below the ceiling you are still an object; below the floor you are not a member.
The two bounds have different character. -/
theorem floor_is_non_degeneracy :
    (¬ NonDegenerate (fun _ _ => none : Fin 3 → Fin 3 → Option Bool))
    ∧ (closeable prereqChain3 (fun i : Fin 3 => decide (i = 0))
        ∧ ¬ (∀ i : Fin 3, (fun i : Fin 3 => decide (i = 0)) i = true)) := by
  unfold NonDegenerate; decide

/-- **The floor bounds a different space.** The ceiling is a predicate on closures `Fin n → Bool`, the floor a
predicate on classifications `X → X → Option Bool`: a permitted closure exists as movement in the lattice, while a
classification is a member or not independently of any closure. Permittedness and membership are conditions on
different objects, so the two are not two bounds on one region. -/
theorem is_the_floor_a_bound_on_the_same_space :
    (∃ S : Fin 3 → Bool, closeable prereqChain3 S ∧ ¬ (∀ i, S i = true))
    ∧ (NonDegenerate (baseCls 3))
    ∧ (¬ NonDegenerate (fun _ _ => none : Fin 3 → Fin 3 → Option Bool)) := by
  unfold NonDegenerate; decide

/-! ## Part 2: can a closure exit through the floor? -/

/-- **Closing reaches the floor only at the ceiling.** The full closure collapses the classification to a
constant, degenerate; a permitted (non-full) closure does not. So the one move that breaks non-degeneracy is the
prohibited one. -/
theorem does_closing_ever_break_non_degeneracy :
    (¬ NonDegenerate (fillClosure (fun _ => true) (baseCls 3)))
    ∧ (NonDegenerate (fillClosure (fun i => decide (i = 0)) (baseCls 3))) := by
  unfold NonDegenerate; decide

/-- **Across the six registers.** Physics has a single ground, its base already degenerate, no non-degeneracy to
break. For the others every permitted closure keeps non-degeneracy: type and cognition (chain), immunology (mixed),
chemistry, trust. Only the full closure, the ceiling, breaks it. No permitted closure reaches the floor. -/
theorem compute_across_the_registers :
    (¬ NonDegenerate (fillClosure (fun _ => false) (baseCls 1)))
    ∧ (∀ S : Fin 3 → Bool, closeable prereqChain3 S → ¬(∀ i, S i = true) →
        NonDegenerate (fillClosure S (baseCls 3)))
    ∧ (∀ S : Fin 3 → Bool, closeable prereqMixed3 S → ¬(∀ i, S i = true) →
        NonDegenerate (fillClosure S (baseCls 3)))
    ∧ (∀ S : Fin 4 → Bool, closeable prereqChemistry S → ¬(∀ i, S i = true) →
        NonDegenerate (fillClosure S (baseCls 4)))
    ∧ (∀ S : Fin 4 → Bool, closeable prereqTrust S → ¬(∀ i, S i = true) →
        NonDegenerate (fillClosure S (baseCls 4)))
    ∧ (¬ NonDegenerate (fillClosure (fun _ => true) (baseCls 3))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold NonDegenerate; decide)

/-! ## Part 3: dimensions -/

/-- **Grounds are the directions, the closeable family the viable combinations.** A register with `n` grounds has
`n` directions along which closure can proceed, and the closeable family, a subset of the `2^n` cube, says which
combinations are viable: the chain four of eight, the mixed order six of eight. -/
theorem grounds_are_the_dimensions :
    ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqChain3 S)).card = 4)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqMixed3 S)).card = 6)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable prereqChemistry S)).card = 8) := by decide

/-- **Viability is assessed per component, not per ground.** The closeable family factors over the connected
components: at the mixed order a closeable set is exactly the bound part's up-closure with the free ground
unconstrained, and the count is the product, six as three times two. So the independent dimensions are the
components, the bound chain one dimension (its grounds coupled) and the free ground another, assessed per component
and combined, not the individual grounds. -/
theorem per_dimension_assessment :
    (∀ S : Fin 3 → Bool, closeable prereqMixed3 S ↔ (S 1 = true → S 0 = true))
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqMixed3 S)).card = 3 * 2) := by decide

/-- **What the absent measure costs.** Viability is a predicate, closeable, a Bool with no magnitude. Two permitted
closures, one strictly closing more (nearer the ceiling in the inclusion order), are both simply closeable, and
nothing in the structure says how far either sits from the full closure or from degeneracy. There is no distance
from either bound and no ordering of nearness: the correspondence is topological, not metric. -/
theorem what_the_absent_measure_costs :
    (closeable prereqChain3 (fun i => decide (i = 0)))
    ∧ (closeable prereqChain3 (fun i => decide (i = 0 ∨ i = 1)))
    ∧ ((fun i => decide (i = 0)) ≠ (fun i : Fin 3 => decide (i = 0 ∨ i = 1)))
    ∧ (∀ i, (fun i => decide (i = 0)) i = true → (fun i : Fin 3 => decide (i = 0 ∨ i = 1)) i = true) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## Part 4: the verdict -/

/-- **Bounded above, open below.** Above, the prohibition bounds the closures, the full closure the unique top.
The floor is hit by movement only at that ceiling: the full closure is degenerate, every permitted closure a
member. And the floor is a condition on classifications, a different space from the closure lattice, where a
degenerate classification is simply not a member. So the region is bounded above by the prohibition and open below,
membership a separate condition, not a second bound on the same region. -/
theorem is_the_region_two_bounded :
    (closeable prereqChain3 (fun _ => true))
    ∧ (∀ S : Fin 3 → Bool, (∀ i, S i = true) → S = (fun _ => true))
    ∧ (¬ NonDegenerate (fillClosure (fun _ => true) (baseCls 3)))
    ∧ (∀ S : Fin 3 → Bool, closeable prereqChain3 S → ¬(∀ i, S i = true) →
        NonDegenerate (fillClosure S (baseCls 3)))
    ∧ (¬ NonDegenerate (fun _ _ => none : Fin 3 → Fin 3 → Option Bool)) := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · intro S h; funext i; exact h i
  · unfold NonDegenerate; decide
  · unfold NonDegenerate; decide
  · unfold NonDegenerate; decide

/-! ## The verdicts

Part 1: the two bounds have different character and lie on different spaces. The ceiling is the full closure, the
top of the closure lattice, beyond which is inconsistency (`ceiling_is_the_prohibition`); the floor is
non-degeneracy, whose failure is an exit not a degradation, a degenerate classification being not a member while a
permitted closure is still in the lattice (`floor_is_non_degeneracy`). And the ceiling is a predicate on closures,
the floor on classifications, permittedness and membership conditions on different objects
(`is_the_floor_a_bound_on_the_same_space`).

Part 2: no permitted closure reaches the floor. Closing collapses the classification only at the full closure
(`does_closing_ever_break_non_degeneracy`); across all six registers every permitted closure keeps
non-degeneracy, physics's single ground already degenerate at the base, and only the ceiling breaks it
(`compute_across_the_registers`). The gate closes: the floor is not reachable from inside by movement.

Part 3: the dimensions are components, and there is no measure. The grounds are the directions and the closeable
family the viable combinations (`grounds_are_the_dimensions`), but viability factors over the connected
components, so the independent dimensions are the components, not the individual grounds (`per_dimension_assessment`);
and viability is a predicate with no magnitude, no distance from either bound (`what_the_absent_measure_costs`).

Part 4: bounded above, open below (`is_the_region_two_bounded`). The prohibition bounds the closures; the floor is
a membership condition on a different space, reached by movement only at the ceiling.

The verdict: the viable region is bounded above and open below, not bounded twice in the same sense. The ceiling
is a genuine upper bound on movement, the full closure, the prohibition, the top of the closure lattice. The floor
is not a lower bound on that lattice: non-degeneracy is a condition on the classification, a different space from
the closures over grounds, and it is an exit rather than a degradation, below the ceiling you remain an object,
below the floor you are not a member at all. The one bridge between the spaces, closing as a fill, reaches
degeneracy only at the full closure, which is the ceiling itself, so across all six registers no permitted closure
crosses the floor. The floor and ceiling do not bound an annulus: the region is bounded above, open below, with
membership a separate condition, and physics sits at the degenerate edge structurally, its single ground leaving
no distinction for the self to enter. Even were the picture completed, the framework has no measure: viability is
a predicate factoring over components, with no distance from either edge, so the correspondence is topological or
nothing. This is the third time an attractive picture the imported term suggested has been revised at contact: the
doughnut has a ceiling but no floor on the same region. The correspondence is imported and a reading; the bounds
are theorems. Reported per part. Nothing here is resolved. -/

end Chiralogy.SafeRegion
