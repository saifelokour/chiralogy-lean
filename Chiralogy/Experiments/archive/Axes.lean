import Chiralogy

/-! # Experiment: the two axes

The bounds sit on two different axes. Absence axis: the total opening at one end, excluded by non-degeneracy, the
full closure at the other, prohibited by the collision, with totalization and partialization the moves and the
permitted lattice living here. Distinction axis: the transpose constant at one end, degenerate and excluded, the
transpose injective at the other, saturated and free. Describe both axes in their own terms. Compute all cases
before judging. Concrete small instances. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Axes

/-- The saturated classifier: injective transpose, each element its own row. -/
def satN {n : ℕ} : Fin n → Fin n → Option Bool := fun x y => if x = y then some true else none

/-- A total classification with distinct rows: total and saturated. -/
def totSat : Fin 2 → Fin 2 → Option Bool := fun x _ => if x = 0 then some true else some false

/-- A distinguishing scale on `Fin 2`. -/
def idScale : Fin 2 → Nat := fun i => (i : Nat)

/-! ## Part 1: does the distinction axis have moves? -/

/-- **There is no dedicated distinction move.** A value-space relabelling holds the absence pattern fixed and
preserves distinction, so it moves along neither axis; the operation that does change distinction, totalization,
removes all absence, so it is an absence move. Nothing changes distinction while holding absence fixed. -/
theorem is_there_a_distinction_move :
    ((∀ x y : Fin 2, (Option.map not (satN x y) = none) ↔ (satN x y = none))
      ∧ NonDegenerate (fun x y => Option.map not (satN x y) : Fin 2 → Fin 2 → Option Bool))
    ∧ (¬ NonDegenerate (totalization (fun _ => 0) (satN : Fin 2 → Fin 2 → Option Bool))
        ∧ (∀ x y, totalization (fun _ => 0) (satN : Fin 2 → Fin 2 → Option Bool) x y ≠ none)) := by
  refine ⟨⟨by decide, by unfold NonDegenerate; decide⟩,
          by unfold NonDegenerate; decide, fun x y => totalization_totalizes _ _ x y⟩

/-- **The absence moves change distinction, as a side effect.** Totalization can merge distinct rows, a saturated
map becoming degenerate when its distinctions rested on absences; but it preserves distinctions carried by present
verdicts. So distinction changes through the absence move, depending on whether the distinctions rest on absences. -/
theorem do_the_absence_moves_change_distinction :
    (NonDegenerate (satN : Fin 2 → Fin 2 → Option Bool)
      ∧ ¬ NonDegenerate (totalization (fun _ => 0) (satN : Fin 2 → Fin 2 → Option Bool)))
    ∧ NonDegenerate (totalization (fun _ => 0) totSat) := by
  refine ⟨⟨by unfold NonDegenerate; decide, by unfold NonDegenerate; decide⟩,
          by unfold NonDegenerate; decide⟩

/-- **The moves and the ethics are on the absence axis.** Totalization removes absence and partialization adds it,
the moves and the ethical acts; the distinction axis has none, a relabelling only preserving it. So the distinction
axis is a coordinate one occupies, not one one moves along, and the ethics is on the absence axis because only
there is there something to do. -/
theorem if_no_moves :
    ((∀ x y, totalization idScale (satN : Fin 2 → Fin 2 → Option Bool) x y ≠ none)
      ∧ partialization (fun _ _ => true) (satN : Fin 2 → Fin 2 → Option Bool) = fun _ _ => none)
    ∧ NonDegenerate (fun x y => Option.map not (satN x y) : Fin 2 → Fin 2 → Option Bool) := by
  refine ⟨⟨fun x y => totalization_totalizes _ _ x y, ?_⟩, by unfold NonDegenerate; decide⟩
  funext x y; simp [partialization]

/-! ## Part 2: are the axes independent? -/

/-- **Three corners inhabited, one empty.** Total and saturated, total and degenerate, open and degenerate all
exist; open and saturated is empty, since all-open forces every row to the same absence, hence degeneracy. At the
open end of absence only the degenerate end of distinction is available: the two floors coincide there. -/
theorem inhabit_the_corners :
    ((∀ x y, totSat x y ≠ none) ∧ NonDegenerate totSat)
    ∧ ((∀ x y : Fin 2, (fun _ _ => some true : Fin 2 → Fin 2 → Option Bool) x y ≠ none)
       ∧ ¬ NonDegenerate (fun _ _ => some true : Fin 2 → Fin 2 → Option Bool))
    ∧ ((∀ x y : Fin 2, (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) x y = none)
       ∧ ¬ NonDegenerate (fun _ _ => none : Fin 2 → Fin 2 → Option Bool))
    ∧ (∀ c : Fin 2 → Fin 2 → Option Bool, (∀ x y, c x y = none) → ¬ NonDegenerate c) := by
  refine ⟨⟨by decide, by unfold NonDegenerate; decide⟩,
          ⟨by decide, by unfold NonDegenerate; decide⟩,
          ⟨by decide, by unfold NonDegenerate; decide⟩, ?_⟩
  intro c h ⟨x, x', hne⟩; exact hne (by funext y; rw [h x y, h x' y])

/-- **The closed end can be saturated.** Totalizing with a distinguishing scale gives a total classification with
distinct rows, so the full closure does not force merging; the prohibition, a collision about faithfulness, is not
about distinction. The axes are independent at the closed end. -/
theorem is_the_prohibited_corner_saturated :
    (∀ x y, totalization idScale (satN : Fin 2 → Fin 2 → Option Bool) x y ≠ none)
    ∧ NonDegenerate (totalization idScale (satN : Fin 2 → Fin 2 → Option Bool)) := by
  refine ⟨fun x y => totalization_totalizes _ _ x y, by unfold NonDegenerate; decide⟩

/-- **Degenerate and total coexist.** A constant present classification returns a verdict everywhere, total, and
distinguishes nothing, degenerate. So degeneracy is independent of absence: it occurs at either end of the absence
axis. -/
theorem is_degenerate_compatible_with_total :
    (∀ x y : Fin 2, (fun _ _ => some true : Fin 2 → Fin 2 → Option Bool) x y ≠ none)
    ∧ ¬ NonDegenerate (fun _ _ => some true : Fin 2 → Fin 2 → Option Bool) := by
  refine ⟨by decide, by unfold NonDegenerate; decide⟩

/-! ## Part 3: where does the hole sit? -/

/-- **The hole is about range.** The transpose does not cover the function space; surjectivity is neither
distinction nor absence but range, a third thing. -/
theorem hole_is_about_range {X : Type} (c : X → X → Option Bool) :
    ¬ Function.Surjective c :=
  hole_uniform c

/-- **The hole bounds neither axis.** It holds at both ends of absence, the total opening and the totalized, and
at the saturated end of distinction, coexisting with injectivity. So non-surjectivity constrains neither how total
nor how distinguishing a classification is. -/
theorem does_the_hole_bound_either_axis :
    (¬ Function.Surjective (fun _ _ => none : Fin 2 → Fin 2 → Option Bool)
      ∧ ¬ Function.Surjective (totalization idScale (satN : Fin 2 → Fin 2 → Option Bool)))
    ∧ (¬ Function.Surjective (satN : Fin 2 → Fin 2 → Option Bool)
       ∧ Function.Injective (fun x : Fin 2 => satN x)) := by
  refine ⟨⟨hole_uniform _, hole_uniform _⟩, hole_uniform _, by decide⟩

/-- **Range is not a third axis.** The hole holds of every classification without exception, so it does not vary
and is not a coordinate one occupies; it is a property of every point, the codomain function space exceeding the
domain everywhere. Two axes, and a universal fact, not three. -/
theorem is_the_hole_a_third_axis {X : Type} :
    ∀ c : X → X → Option Bool, ¬ Function.Surjective c :=
  fun c => hole_uniform c

/-! ## The verdicts

Part 1: the distinction axis has no dedicated move. A relabelling holds the absence pattern fixed and preserves
distinction, while the operation that changes distinction, totalization, removes absence
(`is_there_a_distinction_move`); the absence moves change distinction only as a side effect, merging rows whose
distinctions rested on absences but preserving those carried by present verdicts
(`do_the_absence_moves_change_distinction`); so the moves and the ethics live on the absence axis, the distinction
axis a coordinate one occupies (`if_no_moves`).

Part 2: the axes are independent except at one corner. Total and saturated, total and degenerate, open and
degenerate are inhabited; open and saturated is empty, all-open forcing degeneracy (`inhabit_the_corners`). The
closed end can be saturated, the full closure not forcing merging (`is_the_prohibited_corner_saturated`), and
degeneracy coexists with totality (`is_degenerate_compatible_with_total`). The only coupling is at the total
opening, where the absence floor and the distinction floor coincide.

Part 3: the hole is about range and sits on neither axis. It is non-surjectivity, range not distinction or absence
(`hole_is_about_range`); it bounds neither, holding at both ends of absence and at the saturated end
(`does_the_hole_bound_either_axis`); and it holds of every classification, so range is a fact about the space, not
a third coordinate (`is_the_hole_a_third_axis`).

The verdict: there are two axes with different characters, coupled at one corner, and the hole is a fact about the
whole space rather than a third axis. The absence axis carries the moves, totalization and partialization, and the
ethics, since fabrication and erasure are acts one performs there; it runs from the total opening, excluded by
non-degeneracy, to the full closure, prohibited by the collision. The distinction axis has no dedicated move: a
relabelling preserves it and the absence moves touch it only as a side effect, merging rows when their distinctions
rested on absences, so it is a coordinate one occupies, from the degenerate transpose, excluded, to the saturated
transpose, free. The two are independent across three of the four corners, total-and-saturated, total-and-degenerate,
and open-and-degenerate all inhabited, and the closed end imposes nothing, being saturable; the single coupling is
at the total opening, where with no verdict present there is nothing to distinguish, so the absence floor and the
distinction floor are the same point. The hole is neither axis: it is about range, non-surjectivity of the
transpose, and it bounds neither how total nor how distinguishing a classification is, coexisting with injectivity
and holding at both ends of absence; and since it holds of every classification without exception it does not vary,
so it is not a position one occupies but a fact about every point, the codomain function space exceeding the domain
everywhere. Per the counter-bias, the distinction axis was searched before concluding it has no move, and the
absence moves were found to touch it; the corners were computed rather than assumed independent, and the one forced
coupling reported; and the hole was checked to hold everywhere and read as a fact rather than a coordinate. Two
axes and a universal fact. Reported per part. Nothing here is resolved. -/

end Chiralogy.Axes
