import Chiralogy

/-! # Experiment: is marking a second axis?

`valueCount_is_inert` showed marking does not change the permitted moves. `collision_without_concealment`
showed a marked level can record a fabrication while an unmarked one cannot. Test whether marking is a second
axis, governing whether a move is attributable, orthogonal to the ethical one.

From the literature: normative systems separate ability from permissibility, and epistemic norms are marked out
by how it is fitting to hold a subject accountable, which requires a record. Marking supplies one. So the
candidate axis is attributability, not truth: the framework has no notion of a classification being true, only
of a fabrication being recorded. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Marking

/-! ## Part 1: is marking orthogonal to the whole ethical structure? -/

/-- **Marking and the prohibition.** The prohibition is the full closure over the reasons: at two reasons one
is forbidden and three permitted, whether marked or not, since marking multiplies absent values (four) but not
reasons (two). -/
theorem marking_and_the_prohibition :
    (Finset.univ.filter (fun close : Fin 2 → Bool => ∀ r, close r = true)).card = 1
    ∧ (Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3
    ∧ (Finset.image (fun x : (Bool ⊕ Bool) × Bool => x.1)
         (Finset.univ.filter (fun x => ∃ e, x.1 = Sum.inr e))).card = 2 :=
  ⟨by decide, by decide, by decide⟩

/-- **Marking and the order.** The closeable family is over the reasons (three permitted at two reasons),
unchanged by marking; and marking passes uniformly (`grouping_respects_operations`), so the marked coordinate
opens no new closeable dimension, leaving the order, the family, and which positions are complemented
identical. -/
theorem marking_and_the_order :
    (Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3
    ∧ (¬ ∃ t, MarkingPassing t
        ∧ (¬ ∃ e, (t (Sum.inr false, false)).1 = Sum.inr e)
        ∧ (∃ e, (t (Sum.inr false, true)).1 = Sum.inr e)) :=
  ⟨by decide, grouping_respects_operations⟩

/-- **Marking and the collision.** The boundary collision holds at the unmarked value space
(`complete_and_faithful_is_impossible`) and identically at the marked one (`collision_without_concealment`):
total and faithful are incompatible regardless of the log. -/
theorem marking_and_the_collision :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2)
    ∧ (¬ ∃ c : Fin 4 → Fin 4 → Option Bool × List Bool, (∀ x y, (c x y).1 ≠ none) ∧ (c 0 2).1 = none) :=
  ⟨complete_and_faithful_is_impossible, collision_without_concealment.1⟩

/-- **Marking is orthogonal.** Every ethical feature, the single prohibition, the reason-count the order and
family track, and the collision, is identical at marked and unmarked levels with the same grounds. Marking is
orthogonal to the ethics entire, not only to the lattice. -/
theorem marking_is_orthogonal :
    (Finset.univ.filter (fun close : Fin 2 → Bool => ∀ r, close r = true)).card = 1
    ∧ (¬ ∃ c : Fin 4 → Fin 4 → Option Bool × List Bool, (∀ x y, (c x y).1 ≠ none) ∧ (c 0 2).1 = none)
    ∧ (Finset.image (fun x : (Bool ⊕ Bool) × Bool => x.1)
         (Finset.univ.filter (fun x => ∃ e, x.1 = Sum.inr e))).card = 2 :=
  ⟨by decide, collision_without_concealment.1, by decide⟩

/-! ## Part 2: what marking governs -/

/-- **Attributability.** At a marked level a fabricated verdict and a genuine one have the same value
(`some true`) but different logs, so the fabrication is attributable from the state. -/
theorem attributability :
    (recordingTotalize true (none, [])).1 = (recordingTotalize true (some true, ([] : List Bool))).1
    ∧ (recordingTotalize true (none, []) ≠ recordingTotalize true (some true, ([] : List Bool))) :=
  ⟨rfl, collision_without_concealment.2 true⟩

/-- An unmarked totalization: fill the absence, keep no log. -/
def unmarkedTotalize : Option Bool → Option Bool := fun v => some (v.getD true)

/-- **Unmarked is unattributable.** At an unmarked level the totalization of the absence equals the genuine
verdict, leaving no trace: the move is not attributable from the state. -/
theorem unmarked_is_unattributable :
    unmarkedTotalize none = unmarkedTotalize (some true) :=
  rfl

/-- **Attributability is not permissibility.** Recording is a level property, marked levels record a
fabrication and unmarked ones do not; permissibility is a move property, three permitted and one forbidden.
Level and move are independent choices, so all four combinations, permitted or forbidden by recorded or
unrecorded, are inhabited. -/
theorem attributability_is_not_permissibility :
    (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool)))
    ∧ (unmarkedTotalize none = unmarkedTotalize (some true))
    ∧ ((Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3
        ∧ (Finset.univ.filter (fun close : Fin 2 → Bool => ∀ r, close r = true)).card = 1) :=
  ⟨collision_without_concealment.2, rfl, ⟨by decide, by decide⟩⟩

/-! ## Part 3: is this a second ethical axis or a non-ethical one? -/

/-- **What marking adds.** The prohibition's ground is the collision, not the concealment: total and faithful
collide at the marked value space regardless of the log, and the marked variant records the fabrication instead
of hiding it. So marking adds only a record, changing what can be told about a move, not which moves are
forbidden. It is an epistemic axis beside the ethical one, not a second ethical dimension. -/
theorem what_marking_adds :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool × List Bool, (∀ x y, (c x y).1 ≠ none) ∧ (c 0 2).1 = none)
    ∧ (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool))) :=
  collision_without_concealment

/-! ## The verdicts

Part 1: marking is orthogonal to every ethical feature, not only the lattice. The single prohibition
(`marking_and_the_prohibition`), the order and closeable family (`marking_and_the_order`), and the boundary
collision (`marking_and_the_collision`) are identical at marked and unmarked levels with the same grounds
(`marking_is_orthogonal`). Marking multiplies values, not reasons, and every ethical feature tracks the reasons.

Part 2: the four combinations are inhabited. At a marked level a fabrication is attributable, the value the
same and the log different (`attributability`); at an unmarked level it is not, the fabrication equal to the
genuine verdict (`unmarked_is_unattributable`). Recording is a level property and permissibility a move
property, independent (`attributability_is_not_permissibility`), so permitted or forbidden combines freely with
recorded or unrecorded.

Part 3: marking adds an epistemic dimension, not an ethical one. The prohibition's ground is the collision, not
concealment (`what_marking_adds`): the ethics does not rest on hiding, and marking changes only what can be told
about a move, its attributability, leaving which moves are forbidden untouched. So marking is a second axis,
attributability, epistemic and orthogonal to the ethical axis of permissibility, matching the literature's
separation of ability from permissibility and its account of accountability as requiring a record. It records
that a fabrication occurred, not that a verdict is false. Nothing here is resolved. -/

end Chiralogy.Marking
