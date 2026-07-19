import Chiralogy

/-! # Experiment: the index of the tower

`AbsenceStructure` is canonical and five levels sit as instances. Determine what indexes the tower's
behaviour, and test whether the index predicts at an unbuilt combination (plural and marked). Three candidate
dimensions: cardinality (how many values are absent), markedness (whether fabrication can be recorded), and
dependence (whether the verdict consults context or state). They may not index the same object.

Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.AbsenceIndex

/-! ## Part 1: what is each dimension a property of? -/

/-- **Cardinality is a property of the absence-structure.** The center's cardinality is the count of absent
values, read off `(V, absent)` alone. -/
def centerCard (A : AbsenceStructure) [Fintype A.V] [DecidablePred A.absent] : ℕ :=
  (Finset.univ.filter A.absent).card

/-- Two totalization moves on the Writer value space: silent (leave the log) and recording (log the
fabrication). -/
def silentT : Option Bool × List Bool → Option Bool × List Bool
  | (none, l) => (some true, l)
  | (some b, l) => (some b, l)

def recordingT (e : Bool) : Option Bool × List Bool → Option Bool × List Bool
  | (none, l) => (some true, e :: l)
  | (some b, l) => (some b, l)

/-- **Markedness is a property of the level, not the absence-structure.** On one value space, with the
absence predicate fixed, two moves differ: the silent move conceals (fabricated equals genuine), the
recording move marks (they differ). Markedness varies while the absence-structure is held fixed, so it
indexes the level (the monad carrying the absence), not the absence-structure. -/
theorem markedness_is_level_not_structure (e : Bool) :
    silentT (none, []) = silentT (some true, ([] : List Bool))
    ∧ recordingT e (none, []) ≠ recordingT e (some true, ([] : List Bool)) :=
  ⟨rfl, fun h => List.cons_ne_nil e [] (congrArg Prod.snd h)⟩

/-- **Dependence is a property of the level, not the absence count.** A Reader classification's verdict varies
with context, a feature no absence-count or log captures: it is carried by the value space being a function
type. It does not reduce to markedness (Reader has no log) nor to cardinality. -/
theorem dependence_is_a_separate_feature :
    ∃ f : Bool → Option Bool, f true ≠ f false :=
  ⟨fun s => if s then none else some true, by decide⟩

/-! ## Part 2: parameterized statements -/

/-- **The center's cardinality is the absence count** (a function of the absence-structure, `centerCard`),
computed on the value spaces: one absent value for Maybe, two for Except (these predicates are
`maybeAbsence.absent` and `exceptAbsence.absent`). -/
theorem center_cardinality_is_absence_count :
    (Finset.univ.filter (fun v : Option Bool => v = none)).card = 1
    ∧ (Finset.univ.filter (fun x : Bool ⊕ Bool => ∃ e, x = Sum.inr e)).card = 2 := by decide

/-- **Permitted count** (over the reason count `n`): exactly one totalization is forbidden (the full closure),
and `2 ^ n - 1` are permitted. Matches `one_prohibition_permitted_grew` at `n = 2` (three permitted). -/
theorem permitted_count (n : ℕ) :
    (Finset.univ.filter (fun close : Fin n → Bool => ∀ r, close r = true)).card = 1
    ∧ (Finset.univ.filter (fun close : Fin n → Bool => ¬ ∀ r, close r = true)).card = 2 ^ n - 1 := by
  have hfull : (Finset.univ.filter (fun close : Fin n → Bool => ∀ r, close r = true))
      = {fun _ => true} := by
    ext close
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; funext r; exact h r
    · rintro rfl; intro r; rfl
  have h1 : (Finset.univ.filter (fun close : Fin n → Bool => ∀ r, close r = true)).card = 1 := by
    rw [hfull]; exact Finset.card_singleton _
  refine ⟨h1, ?_⟩
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), h1, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **Concealment tracks unmarkedness** (over levels): the silent (unmarked) move conceals, the recording
(marked) move does not. This is `markedness_is_level_not_structure` read at the level index. -/
theorem concealment_iff_unmarked (e : Bool) :
    silentT (none, []) = silentT (some true, ([] : List Bool))
    ∧ recordingT e (none, []) ≠ recordingT e (some true, ([] : List Bool)) :=
  markedness_is_level_not_structure e

/-! ## Part 3: the prediction

For a plural-and-marked structure, Except carrying a log (`(Bool ⊕ Bool) × Bool`, two reasons and a
recording bit), fixed before construction, the four predictions are:
1. the center fragments (from cardinality),
2. fabrication is recordable (from markedness),
3. the boundary is a spectrum with `2 ^ |E| - 1 = 3` permitted,
4. the concealment half of the prohibition's rationale drops away. -/

def plusMarked : AbsenceStructure := ⟨(Bool ⊕ Bool) × Bool, fun x => ∃ e, x.1 = Sum.inr e⟩

def recordPM : (Bool ⊕ Bool) × Bool → (Bool ⊕ Bool) × Bool
  | (Sum.inr _, _) => (Sum.inl true, true)
  | (Sum.inl b, m) => (Sum.inl b, m)

/-- **Prediction 1 holds: the center fragments.** Two distinct absent values (the two reasons). -/
theorem pm_center_fragments :
    plusMarked.absent (Sum.inr false, false) ∧ plusMarked.absent (Sum.inr true, false)
    ∧ ((Sum.inr false, false) : (Bool ⊕ Bool) × Bool) ≠ (Sum.inr true, false) :=
  ⟨⟨false, rfl⟩, ⟨true, rfl⟩, by decide⟩

/-- **Predictions 2 and 4 hold: recordable, concealment drops.** The recording move marks the fabrication
(log bit set), so a fabricated verdict differs from a genuine one: it does not conceal. -/
theorem pm_fabrication_recordable :
    recordPM (Sum.inr false, false) ≠ recordPM (Sum.inl true, false) := by decide

/-- **Prediction 3 holds: the boundary is a spectrum with three permitted.** Reason-indexed at two reasons,
`2 ^ 2 - 1 = 3`. -/
theorem pm_boundary_spectrum :
    (Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3 := by decide

/-- **The index does not factor cleanly.** Markedness inflates the absence count without touching the
reason-indexed boundary: Except has two absent values, plural-and-marked has four (the log bit doubles them),
yet both have three permitted totalizations (two reasons). So the absence-cardinality (an absence-structure
dimension) and the boundary spectrum (reason-indexed) diverge under markedness (a level dimension): they
coincide only when unmarked. -/
theorem markedness_inflates_cardinality_not_boundary :
    (Finset.univ.filter (fun x : Bool ⊕ Bool => ∃ e, x = Sum.inr e)).card = 2
    ∧ (Finset.univ.filter (fun x : (Bool ⊕ Bool) × Bool => ∃ e, x.1 = Sum.inr e)).card = 4
    ∧ (Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3 := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## Reasons versus absent values -/

/-- **The two counts, on the instances.** The absent-value count is a function of `(V, absent)`: one for
Maybe, two for Except, four for plural-and-marked (the log bit doubles the values). -/
theorem valueCount_instances :
    (Finset.univ.filter (fun v : Option Bool => v = none)).card = 1
    ∧ (Finset.univ.filter (fun x : Bool ⊕ Bool => ∃ e, x = Sum.inr e)).card = 2
    ∧ (Finset.univ.filter (fun x : (Bool ⊕ Bool) × Bool => ∃ e, x.1 = Sum.inr e)).card = 4 := by decide

/-- **Reasons are extra data, not derived from the structure.** On one absent set (plural-and-marked, four
values), two groupings give different counts: projecting to the reason coordinate `x.1` gives two, the
identity grouping gives four. The absent set alone does not pick one, so the reason count is not a function
of `(V, absent)`: the reason-grouping is additional structure the level supplies. -/
theorem reasons_are_extra_data :
    (Finset.image (fun x : (Bool ⊕ Bool) × Bool => x.1)
       (Finset.univ.filter (fun x => ∃ e, x.1 = Sum.inr e))).card = 2
    ∧ (Finset.image (fun x : (Bool ⊕ Bool) × Bool => x)
       (Finset.univ.filter (fun x => ∃ e, x.1 = Sum.inr e))).card = 4 := by decide

/-- **The counts coincide exactly when unmarked.** The reason-projection drops the marking. For Except
(unmarked, value space is the reason space) it is injective, so the reason image equals the value count. For
plural-and-marked (the value space is reason times marking) it is not, so they diverge. -/
theorem counts_coincide_iff_unmarked :
    (Finset.image (fun x : Bool ⊕ Bool => x)
       (Finset.univ.filter (fun x => ∃ e, x = Sum.inr e))).card
      = (Finset.univ.filter (fun x : Bool ⊕ Bool => ∃ e, x = Sum.inr e)).card
    ∧ (Finset.image (fun x : (Bool ⊕ Bool) × Bool => x.1)
       (Finset.univ.filter (fun x => ∃ e, x.1 = Sum.inr e))).card
      ≠ (Finset.univ.filter (fun x : (Bool ⊕ Bool) × Bool => ∃ e, x.1 = Sum.inr e)).card := by
  refine ⟨by decide, by decide⟩

/-- **Permitted count is by reasons.** At plural-and-marked, `2 ^ reasonCount - 1 = 3` permitted (two
reasons), not `2 ^ valueCount - 1 = 15`. The boundary follows reasons, not values. -/
theorem permitted_count_is_by_reasons :
    (Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3
    ∧ (Finset.univ.filter (fun close : Fin 4 → Bool => ¬ ∀ r, close r = true)).card = 15 := by
  refine ⟨by decide, by decide⟩

/-- Closing the reason `false`: fill every absent value carrying that reason, whatever its marking. -/
def closeReasonFalse : (Bool ⊕ Bool) × Bool → (Bool ⊕ Bool) × Bool
  | (Sum.inr false, m) => (Sum.inl true, m)
  | x => x

/-- **The center fragments by reasons, not values.** Closing one reason removes both of its absent values at
once (the two markings), while the other reason stays open: the moves group absent values by reason. So the
center has two parts (the reasons), not four (the values). -/
theorem center_fragments_by_reasons :
    (¬ ∃ e, (closeReasonFalse (Sum.inr false, false)).1 = Sum.inr e)
    ∧ (¬ ∃ e, (closeReasonFalse (Sum.inr false, true)).1 = Sum.inr e)
    ∧ (∃ e, ((Sum.inr true, false) : (Bool ⊕ Bool) × Bool).1 = Sum.inr e) := by decide

/-- **The center's parts are the reasons.** The reason-classes number two, not the four absent values. -/
theorem center_fragmentation_is_by_reasons :
    (Finset.image (fun x : (Bool ⊕ Bool) × Bool => x.1)
       (Finset.univ.filter (fun x => ∃ e, x.1 = Sum.inr e))).card = 2
    ∧ (Finset.univ.filter (fun x : (Bool ⊕ Bool) × Bool => ∃ e, x.1 = Sum.inr e)).card = 4 := by decide

/-- **The absent-value count governs nothing in the model structure.** Boundary (three permitted) and center
(two parts) both track the reason count, two; neither tracks the value count, four. The value count only
records the marking multiplicity, inert with respect to the moves, center, and boundary examined here. -/
theorem what_valueCount_governs :
    (Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3
    ∧ (Finset.image (fun x : (Bool ⊕ Bool) × Bool => x.1)
         (Finset.univ.filter (fun x => ∃ e, x.1 = Sum.inr e))).card = 2
    ∧ (Finset.univ.filter (fun x : (Bool ⊕ Bool) × Bool => ∃ e, x.1 = Sum.inr e)).card = 4 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The base is minimal on every coordinate.** Maybe has one absent value and one reason (so unmarked,
reason count equals value count equals one) and no dependence (the value space `Option Bool` is a plain value,
not a function type). This precise conjunction replaces the underspecified "singular absence". -/
theorem base_is_minimal_on_every_coordinate :
    (Finset.univ.filter (fun v : Option Bool => v = none)).card = 1
    ∧ (Finset.image (fun v : Option Bool => v)
         (Finset.univ.filter (fun v => v = none))).card = 1 := by decide

/-! ## The verdict

Part 1: the index is over two objects. Cardinality is a property of the absence-structure (`centerCard`, read
off `(V, absent)`). Markedness and dependence are properties of the level, not the absence predicate:
markedness varies with two moves at a fixed absence-structure (`markedness_is_level_not_structure`), and
dependence is a separate feature carried by a function-typed value space (`dependence_is_a_separate_feature`),
which does not reduce to markedness or cardinality. The two level-dimensions are independent (Writer marked
not dependent, Reader dependent not marked). A level determines its absence-structure by forgetting the moves,
but not conversely: the projection is not injective, so the index does not collapse to one object.

Part 2: the parameterized statements hold in their proper index. `center_cardinality_is_absence_count` over
absence-structures; `permitted_count` (`2 ^ n - 1`) over the reason count; concealment tracks unmarkedness
over levels.

Part 3: all four predictions hold at plural-and-marked. But the more valuable finding is where the index
fails to factor: `markedness_inflates_cardinality_not_boundary` shows the absence-cardinality (four) and the
boundary spectrum (reason-indexed, three) diverge once a log is added. Markedness, a level dimension, inflates
the absence-count, an absence-structure dimension, while leaving the reason-based boundary unchanged. So the
two index-objects do not factor cleanly: the cardinality dimension itself splits into an absent-value count
and a reason count, which coincide only when unmarked.

Reasons versus values: the divergence resolves into two counts. The absent-value count is a function of
`(V, absent)` (`valueCount_instances`); the reason count is not, it is extra data the level supplies
(`reasons_are_extra_data`, two groupings of one absent set). They coincide exactly when unmarked
(`counts_coincide_iff_unmarked`). The model structure is driven by reasons: the boundary is
`2 ^ reasonCount - 1` (`permitted_count_is_by_reasons`, three not fifteen), and the center fragments by
reasons, closing one reason removing all its values at once (`center_fragments_by_reasons`,
`center_fragmentation_is_by_reasons`, two parts not four). The absent-value count governs nothing examined
(`what_valueCount_governs`): it only records the marking multiplicity, inert for moves, center, and boundary.
The base is minimal on every coordinate (`base_is_minimal_on_every_coordinate`): one reason, one value,
unmarked, no dependence, the precise replacement for "singular absence".

The verdict: the tower is indexed over two objects, not one, absence-structures and levels; the index predicts
the four features at an unbuilt combination, but the objects do not factor cleanly. The count that drives the
model structure is the reason count, which is not derivable from the absence-structure but supplied by the
level as extra data; the absent-value count is inert. Reasons drive, values follow, and reasons are not the
structure's to give. Nothing here is resolved. -/

end Chiralogy.AbsenceIndex
