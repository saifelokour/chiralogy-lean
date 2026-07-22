import Chiralogy

/-! ARCHIVED (SPENT): the graduatable universal results of this investigation already reached
canonical in prior sessions, so nothing graduated in the graduate-now wave. Mapping:
  opening_is_monotone_on_distinction -> Model/Apophatic (opening_is_monotone_on_distinction, generalized to {X}); the ethics-half of does_this_explain_the_ethics -> partialization_asserts_no_falsehood (Model/Apophatic).
Remaining content is fixed-size witnesses and (where present) fragility/scale coordinates, kept as
the investigation record. Namespaced under Chiralogy.Opening, it typechecks standalone against canonical. -/

/-! # Experiment: what partialization does to distinction

Every distinction result so far tested totalization: it fills with a scale-dependent value, so it can destroy
distinctions and create them, the direction depending on the scale. Test partialization. It replaces a verdict
with the absence, and the absence has no parameter, so its fill may only ever merge rows. But its mask is
per-position and can discriminate rows, so the question is where separation can come from. Compute all cases before
judging. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Opening

def satN {n : ℕ} : Fin n → Fin n → Option Bool := fun x y => if x = y then some true else none
def idScale {n : ℕ} : Fin n → Nat := fun i => (i : Nat)

/-! ## Part 1: can partialization create a distinction? -/

/-- **Opening can separate, but only through the mask.** Opening one row's cell leaves the other untouched, so two
identical rows separate. This is not the fill separating them, the fill being the constant absence, but the mask
treating the rows differently. -/
theorem can_opening_separate :
    ((fun _ _ => some true : Fin 2 → Fin 2 → Option Bool) 0
        = (fun _ _ => some true : Fin 2 → Fin 2 → Option Bool) 1)
    ∧ (partialization (fun x y => decide (x = 0 ∧ y = 0)) (fun _ _ => some true : Fin 2 → Fin 2 → Option Bool) 0
        ≠ partialization (fun x y => decide (x = 0 ∧ y = 0)) (fun _ _ => some true : Fin 2 → Fin 2 → Option Bool) 1) := by
  refine ⟨rfl, by decide⟩

/-- **The fill is monotone on distinction.** Opening by a column-uniform mask never separates identical rows: the
fill is the parameterless absence, so on a column it maps both rows the same way. Partialization increases
distinction only through a row-discriminating mask, never through its fill. -/
theorem opening_is_monotone_on_distinction {n : ℕ} (wc : Fin n → Bool)
    (c : Fin n → Fin n → Option Bool) (x x' : Fin n) :
    c x = c x' → partialization (fun _ y => wc y) c x = partialization (fun _ y => wc y) c x' := by
  intro h; funext y; simp only [partialization, congrFun h y]

/-! ## Part 2: does it always reduce? -/

/-- **Opening can preserve.** Opening a pair where the distinction is not carried preserves it: rows differing at
column 0, opening column 1 leaves them distinct. -/
theorem can_opening_preserve :
    partialization (fun _ y => decide (y = 1))
        (fun x y => if y = 0 then some (decide (x = 0)) else some true : Fin 2 → Fin 2 → Option Bool) 0
      ≠ partialization (fun _ y => decide (y = 1))
        (fun x y => if y = 0 then some (decide (x = 0)) else some true : Fin 2 → Fin 2 → Option Bool) 1 := by
  decide

/-- **What opening destroys is dual to what totalization destroys.** Rows differing only at column 0 by present
verdicts merge when column 0 is opened; and that distinction is present-carried, so it survives totalization. The
two moves destroy dual kinds: totalization removes absences, destroying absence-carried distinctions, partialization
removes present verdicts, destroying present-carried ones at the opened pair. -/
theorem what_opening_destroys :
    (partialization (fun _ y => decide (y = 0))
        (fun x y => if y = 0 then some (decide (x = 0)) else none : Fin 2 → Fin 2 → Option Bool) 0
      = partialization (fun _ y => decide (y = 0))
        (fun x y => if y = 0 then some (decide (x = 0)) else none : Fin 2 → Fin 2 → Option Bool) 1)
    ∧ (totalization (fun _ => 0)
        (fun x y => if y = 0 then some (decide (x = 0)) else none : Fin 2 → Fin 2 → Option Bool) 0
      ≠ totalization (fun _ => 0)
        (fun x y => if y = 0 then some (decide (x = 0)) else none : Fin 2 → Fin 2 → Option Bool) 1) := by
  refine ⟨by decide, by decide⟩

/-! ## Part 3: the two moves compared -/

/-- **Totalization is bidirectional in its fill, partialization is not.** Totalization separates identical rows
through its fill, a uniform per-element scale sending one rule to different values per row; partialization by a
uniform column mask never separates, its fill the constant absence. So totalization's fill goes either way,
partialization's one way, and opening separates only through a row-discriminating mask. -/
theorem totalization_is_bidirectional_partialization_is_not :
    (totalization idScale (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) 0
        ≠ totalization idScale (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) 1)
    ∧ (∀ (wc : Fin 2 → Bool) (c : Fin 2 → Fin 2 → Option Bool),
        c 0 = c 1 → partialization (fun _ y => wc y) c 0 = partialization (fun _ y => wc y) c 1) := by
  refine ⟨by decide, fun wc c h => ?_⟩
  funext y; simp only [partialization, congrFun h y]

/-- **The ethics tracks falsehood, sharing a root with the asymmetry.** Partialization asserts no falsehood against
any target, so it is safe; totalization fabricates, two scales giving opposite verdicts at the absence, so it can
assert a falsehood. The prohibition targets totalization for this, and the distinction-asymmetry shares the root,
that a verdict carries content the absence does not, but the ethics is about falsehood, not distinction. -/
theorem does_this_explain_the_ethics {X : Type} (w : X → X → Bool) (c : X → X → Option Bool)
    (t : X → X → Bool) (x y : X) :
    (assertsFalse (partialization w c) t x y → assertsFalse c t x y)
    ∧ (∃ s s' : Fin 4 → Nat, totalization s imprecise 0 2 ≠ totalization s' imprecise 0 2) :=
  ⟨partialization_asserts_no_falsehood w c t x y, totalization_fabricates⟩

/-- **The total opening is reached only by opening.** No totalization is the total opening, totalization always
removing every absence; partialization reaches it by opening every pair. Totalization can reach degeneracy, a total
constant map, but never the total opening itself. -/
theorem the_floor_is_reached_by_opening_only :
    (∀ (s : Fin 2 → Nat) (c : Fin 2 → Fin 2 → Option Bool), totalization s c ≠ (fun _ _ => none))
    ∧ (partialization (fun _ _ => true) (satN : Fin 2 → Fin 2 → Option Bool) = fun _ _ => none) := by
  refine ⟨fun s c heq => totalization_totalizes s c 0 0 (congrFun (congrFun heq 0) 0), ?_⟩
  funext x y; simp [partialization]

/-! ## The verdicts

Part 1: opening can separate, but only through the mask, and its fill is monotone. Opening one row's cell
separates two identical rows (`can_opening_separate`), so partialization is not unconditionally monotone; but a
column-uniform mask never separates, the fill being the constant absence (`opening_is_monotone_on_distinction`), so
separation comes from the mask, never the fill.

Part 2: opening preserves where the distinction is not at the opened pair, and destroys where it is. Opening an
uninvolved column keeps a distinction (`can_opening_preserve`); opening the column that carried it merges the rows,
and that distinction is present-carried, surviving totalization (`what_opening_destroys`), so the two moves destroy
dual kinds.

Part 3: the asymmetry is in the fill, and it bears on the ethics through a shared root. Totalization's fill
separates identical rows, partialization's column fill never does
(`totalization_is_bidirectional_partialization_is_not`); partialization asserts no falsehood while totalization
fabricates (`does_this_explain_the_ethics`); and the total opening is reached only by opening
(`the_floor_is_reached_by_opening_only`).

The verdict: partialization is one-way in its fill and bidirectional only through its mask, dual to totalization in
what it destroys, and the asymmetry bears on the ethics through a shared root without reducing to it. The naive
expectation, that opening can only merge, is refuted: opening a single row's cell separates it from an identical
row, so partialization can create a distinction. But the separation comes entirely from the mask treating the two
rows differently, never from the fill, which is the parameterless absence; a column-uniform mask, opening the same
positions in every row, can only merge. This is the precise asymmetry with totalization, whose fill is a
scale-dependent value that separates rows even under a uniform per-element rule, so totalization goes either way
through its fill while partialization's fill goes one way. In what they destroy the two are dual: totalization
removes absences and so destroys absence-carried distinctions, the ones opening leaves alone, while partialization
removes present verdicts and so destroys present-carried distinctions at the opened pair, the ones totalization
preserves. The ethics connects but is not explained away: the prohibition targets totalization because it
fabricates, asserting a falsehood two scales disagree on, while partialization asserts no falsehood and is
permitted, and the distinction-asymmetry shares the root, that a verdict carries content the absence does not, yet
the prohibition is about falsehood, not distinction, so the connection is real but partial. And the total opening,
where all distinction is destroyed, is reached only by opening: no totalization equals it, totalization always
filling every absence, though totalization can reach a degenerate total map by another route. Per the counter-bias,
monotonicity was not assumed, the counterexample found and the fill monotonicity proved separately; the duality was
computed, the present-carried distinction shown to survive totalization and die under opening; and the ethics
connection was stated as a shared root, not an explanation, the prohibition being about falsehood. Reported per
part. Nothing here is resolved. -/

end Chiralogy.Opening
