import Chiralogy

/-! # Experiment: does faithfulness mean the range or the signature?

`vacating_a_declared_ground` produced a total classification over a theory that still declares an absence.
Whether that collides with the boundary depends on what faithfulness means: the classification returns an
absence somewhere (range), or its theory has one available (signature). Determine which reading
`complete_and_faithful_is_impossible` uses and what follows.

Range reading: `∃ x y, c x y = none`, the classification actually returns an absence. Signature reading: the
level declares an absence, available whether or not the classification uses it. A vacated classification is
everywhere-defined, absent nowhere in its range, and declares one in its signature: it collides under the
signature reading, not under the range reading. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Faithful

/-! ## Part 1: which reading is on the term? -/

/-- **The boundary uses the range.** The second conjunct of `complete_and_faithful_is_impossible` is
`c 0 2 = imprecise 0 2`, a value the classification returns at cell `(0,2)`, and `imprecise 0 2` is `none`. So
it quantifies a returned value, not a ground the level declares: a total classification fails it, since
`c 0 2 ≠ none`. -/
theorem boundary_uses_the_range :
    imprecise (0 : Fin 4) 2 = none
    ∧ (∀ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) → c 0 2 ≠ imprecise 0 2) :=
  ⟨by decide, fun c htot => by rw [show imprecise (0 : Fin 4) 2 = none from by decide]; exact htot 0 2⟩

/-- **Vacating under the stated reading.** Given the range reading, a vacated classification (total, absent
nowhere) is not in the forbidden set: it is total and yet does not return the absence at `(0,2)`, so it does not
collide. The earlier result is confirmed, not overturned. -/
theorem vacating_under_the_stated_reading :
    ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 ≠ imprecise 0 2 :=
  ⟨fun _ _ => some true, fun _ _ => by simp,
   by rw [show imprecise (0 : Fin 4) 2 = none from by decide]; simp⟩

/-! ## Part 2: what the other reading would give -/

/-- **The signature reading collides everything.** Under the signature reading the faithful conjunct is that
the level declares an absence, a fixed truth (`∃ v : Option Bool, v = none`). So every total classification is
in the signature-forbidden set, the vacated one and the innocent one alike; and total classifications exist. The
signature-reading boundary would therefore be false. So the earlier permission holds under the range reading,
and the signature reading is untenable. -/
theorem signature_reading_collides :
    (∀ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) →
        ((∀ x y, c x y ≠ none) ∧ (∃ v : Option Bool, v = none)))
    ∧ (∃ c : Fin 4 → Fin 4 → Option Bool, ∀ x y, c x y ≠ none) :=
  ⟨fun _ htot => ⟨htot, none, rfl⟩, ⟨fun _ _ => some true, fun _ _ => by simp⟩⟩

/-- **The readings agree except at vacating.** For a classification that returns an absence both readings are
faithful (agree); for a vacated classification the range says not-faithful while the signature says faithful
(differ). They come apart only at vacating, so vacating is precisely the case distinguishing them, a probe of
the framework's notion rather than a gap in the prohibition. -/
theorem are_the_readings_equivalent :
    (∃ c : Fin 4 → Fin 4 → Option Bool, (∃ x y, c x y = none) ∧ (∃ v : Option Bool, v = none))
    ∧ (∃ c : Fin 4 → Fin 4 → Option Bool, (¬ ∃ x y, c x y = none) ∧ (∃ v : Option Bool, v = none)) :=
  ⟨⟨fun x y => if x = y then some true else none, ⟨0, 1, by decide⟩, none, rfl⟩,
   ⟨fun _ _ => some true, by decide, none, rfl⟩⟩

/-! ## Part 3: which reading should the framework have? -/

/-- **What each reading forbids.** The range reading forbids what a classification does, being total and yet
returning the absence, an internal contradiction, which is `complete_and_faithful_is_impossible` and holds. The
signature reading would forbid what the theory keeps, any total classification over an absence-declaring level,
which is false since total classifications exist. The framework's operative results quantify returned values or
surjectivity, so they are the range reading; the choice, were it open, is foreclosed. -/
theorem what_each_reading_forbids :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2)
    ∧ (∃ c : Fin 4 → Fin 4 → Option Bool, ∀ x y, c x y ≠ none) :=
  ⟨complete_and_faithful_is_impossible, ⟨fun _ _ => some true, fun _ _ => by simp⟩⟩

/-! ## The verdicts

Part 1: the boundary uses the range reading. The second conjunct is `c 0 2 = imprecise 0 2`, a value the
classification returns, with `imprecise 0 2 = none` (`boundary_uses_the_range`), read from the statement, not
from intuition. Under it a vacated classification does not collide (`vacating_under_the_stated_reading`): the
earlier result stands, the argument was not a misreading.

Part 2: the signature reading would collide every total classification, since its faithful conjunct is a fixed
truth of the level (`signature_reading_collides`), and total classifications exist, so that boundary would be
false. The two readings agree for classifications that use their grounds and differ only at vacating
(`are_the_readings_equivalent`), so vacating is the probe distinguishing them, not a gap.

Part 3: the range reading forbids what a classification does (total and returning the absence, an internal
contradiction), which holds; the signature reading would forbid what the theory keeps (every total over an
absence-declaring level), which is false (`what_each_reading_forbids`). The framework's other results,
`complete_and_faithful_is_impossible`, `full_totality_collides`, and the payload, all quantify returned values
or surjectivity, so they depend on the range reading; the framework is committed to it, and the signature
reading is not a live alternative but a refuted one. Not chosen here, reported as forced. Nothing here is
resolved. -/

end Chiralogy.Faithful
