-- ARCHIVED (register and ground-structure graduation): the fibre as a state-side negative (empty fibre proves never totalized) graduated to Model/GroundForensics.

import Chiralogy

/-! # Experiment: can totalization be quantified from the state?

`nothing_detects_from_the_state` showed a totalized and an innocent classification can be literally equal, that
pair constructed to coincide; but `totalization_not_faithful` says totalization is non-injective, and
non-injective is not constant. Test whether the fibre structure gives a quantity on the state, and whether some
classifications are provably not totalizations. Detection asks "was this totalized", undecidable in the identity
cases; quantification asks how many partial classifications would have produced this one, a function of the state.
The scale is fixed at `fun _ => 0`, so `totalization` fills each absence with `some (decide (s y ≤ s x))`, which
on the diagonal is always `some true`. Concrete small instances. Stays in `Experiments/`; canonical untouched;
nothing resolved. -/

open Chiralogy

namespace Chiralogy.Fibres

/-! ## Part 1: the fibre -/

/-- **The totalization fibre.** For a total classification `t`, the partial classifications whose totalization is
`t`. On `Fin 1` the all-true `t` has one partial preimage (the all-none), the all-false `t` has none, since a
filled absence on the diagonal is `some true`. -/
theorem totalization_fibre :
    ((Finset.univ.filter (fun c : Fin 1 → Fin 1 → Option Bool =>
        totalization (fun _ => 0) c = (fun _ _ => some true) ∧ ∃ x y, c x y = none)).card = 1)
    ∧ ((Finset.univ.filter (fun c : Fin 1 → Fin 1 → Option Bool =>
        totalization (fun _ => 0) c = (fun _ _ => some false) ∧ ∃ x y, c x y = none)).card = 0) :=
  ⟨by decide, by decide⟩

/-- **Fibres differ.** Some fibre has at least two partial preimages, totalization being non-injective
(`totalization_not_faithful`), and another is empty: the fibre size is non-constant across total classifications,
so the quantity distinguishes. -/
theorem fibres_differ :
    (∃ c c' : Fin 2 → Fin 2 → Option Bool, c ≠ c' ∧ totalization (fun _ => 0) c = totalization (fun _ => 0) c')
    ∧ ((Finset.univ.filter (fun c : Fin 1 → Fin 1 → Option Bool =>
        totalization (fun _ => 0) c = (fun _ _ => some false) ∧ ∃ x y, c x y = none)).card = 0) :=
  ⟨totalization_not_faithful, by decide⟩

/-! ## Part 2: is there an empty fibre? -/

/-- **An empty fibre means never totalized.** The all-false classification on `Fin 1` has empty partial fibre: no
partial classification totalizes to it, since a filled absence yields `some true` on the diagonal (`s x ≤ s x`),
never `some false`. So the framework has a state predicate ruling out totalization, a genuine negative, not
detection. -/
theorem empty_fibre_means_never_totalized :
    ¬ ∃ c : Fin 1 → Fin 1 → Option Bool,
        (∃ x y, c x y = none) ∧ totalization (fun _ => 0) c = (fun _ _ => some false) := by
  decide

/-- **The predicate is non-trivial.** The all-false classification has empty fibre (never totalized); the all-true
has an inhabited fibre, the all-none classification totalizing to it. Both sides are populated, and inhabitance is
by fact, not construction: the all-true fibre is inhabited because the fill value agrees with `t`, and the
all-false one is empty because it disagrees, not because either is `t`-minus-a-none by default. -/
theorem is_the_predicate_nontrivial :
    (¬ ∃ c : Fin 1 → Fin 1 → Option Bool,
        (∃ x y, c x y = none) ∧ totalization (fun _ => 0) c = (fun _ _ => some false))
    ∧ (∃ c : Fin 1 → Fin 1 → Option Bool,
        (∃ x y, c x y = none) ∧ totalization (fun _ => 0) c = (fun _ _ => some true)) :=
  ⟨by decide, ⟨fun _ _ => none, ⟨0, 0, rfl⟩, by decide⟩⟩

/-! ## Part 3: what the quantity gives -/

/-- **The fibre size is a state function.** It is computed from the classification alone: equal classifications
have equal fibres, with no history consulted. Unlike provenance, it needs no log. -/
theorem fibre_size_is_a_state_function (t t' : Fin 1 → Fin 1 → Option Bool) (h : t = t') :
    (Finset.univ.filter (fun c : Fin 1 → Fin 1 → Option Bool =>
        totalization (fun _ => 0) c = t ∧ ∃ x y, c x y = none)).card
    = (Finset.univ.filter (fun c : Fin 1 → Fin 1 → Option Bool =>
        totalization (fun _ => 0) c = t' ∧ ∃ x y, c x y = none)).card := by
  rw [h]

/-- **What it does not give.** The quantity does not decide whether a totalization occurred. Only the empty fibre
is decisive, negatively: empty implies not a totalization. An inhabited fibre is compatible with many histories
including none, the all-true classification having a preimage yet being a well-formed classification that need not
have been totalized. -/
theorem what_it_does_not_give :
    (¬ ∃ c : Fin 1 → Fin 1 → Option Bool,
        (∃ x y, c x y = none) ∧ totalization (fun _ => 0) c = (fun _ _ => some false))
    ∧ (∃ c : Fin 1 → Fin 1 → Option Bool,
        (∃ x y, c x y = none) ∧ totalization (fun _ => 0) c = (fun _ _ => some true)) :=
  ⟨by decide, ⟨fun _ _ => none, ⟨0, 0, rfl⟩, by decide⟩⟩

/-- **Relation to marking.** Marking and the fibre are independent. Marking is a per-move log, distinguishing a
fabrication where recorded (`collision_without_concealment`); the fibre is a per-state quantity with no log,
ruling out totalization where empty. At a marked level the fibre adds nothing to the log's positive record; where
there is no log it supplies the one thing available, the negative. -/
theorem relation_to_marking :
    (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool)))
    ∧ (¬ ∃ c : Fin 1 → Fin 1 → Option Bool,
        (∃ x y, c x y = none) ∧ totalization (fun _ => 0) c = (fun _ _ => some false)) :=
  ⟨collision_without_concealment.2, by decide⟩

/-! ## The verdicts

Part 1: the fibre gives a non-constant quantity. For a total classification, its fibre is the partial
classifications that totalize to it (`totalization_fibre`); the sizes differ, some fibre having at least two
preimages by non-injectivity and another being empty (`fibres_differ`). So the quantity is not inert: it varies
across states.

Part 2: there are empty fibres, and the predicate is non-trivial. The all-false classification on `Fin 1` is the
totalization of no partial classification (`empty_fibre_means_never_totalized`), since a filled absence is
`some true` on the diagonal, never `some false`; and the all-true classification has an inhabited fibre, so both
sides are populated (`is_the_predicate_nontrivial`). The emptiness is by fact, not by construction: it holds
because the fill value disagrees with the state, not because the state fails to be its own totalization.

Part 3: the quantity is state-side and only negatively decisive. It is computed from the classification alone,
equal states giving equal fibres, no history (`fibre_size_is_a_state_function`). It does not decide whether a
totalization occurred: only an empty fibre is decisive, and only in the negative, an inhabited one compatible with
no totalization having happened (`what_it_does_not_give`). It is independent of marking
(`relation_to_marking`): marking is a per-move positive log, the fibre a per-state negative with no log, adding
nothing at a marked level and the only available thing where unmarked.

The verdict: totalization can be quantified from the state, and the quantity is genuine but one-sided. The fibre,
the partial classifications that totalize to a given one, has non-constant size and, at some states, is empty; an
empty fibre proves the classification is not a totalization, a negative the earlier detection results could not
supply. But it is not detection: a large fibre is compatible with any history including none, so the quantity
decides only in the negative, ruling out totalization where empty and saying nothing where inhabited. It is a
state function, needing no log, and so independent of marking, which supplies the positive attribution the fibre
cannot; where there is no log, the fibre is the one thing left, and it can only say never, not did. So the
framework does see slightly more than reported, but only the impossibility of totalization, never its occurrence.
Reported per part. Nothing here is resolved. -/

end Chiralogy.Fibres
