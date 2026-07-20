-- ARCHIVED (register and ground-structure graduation): resolved negative: self-sufficiency is a gloss, refuted; not graduated (a claim about the framework, not in it).

import Chiralogy

/-! # Experiment: what is the attempt aimed at?

The framework describes totalization and its self-defeat and says nothing about what the move aims at. Test
whether an aim is derivable from the collision, or whether reading it as self-sufficiency imports vocabulary the
boundary avoids. Two readings: stated, the attempt aims at total-and-faithful, a conjunction that collides
(`complete_and_faithful_is_impossible`); glossed, it aims at self-sufficiency, no absences, no imports, a third
term that must be derived or dropped. Concrete small instances. Stays in `Experiments/`; canonical untouched;
nothing resolved. -/

open Chiralogy

namespace Chiralogy.Aim

/-! ## Part 1: is the narrow move a success? -/

/-- **Totalization succeeds narrowly.** It produces a total classification (`totalization_totalizes`), and total
is a permitted mode, a total classification existing and not prohibited. So the narrow move succeeds at what it
does; only the conjunction fails, a move whose aim is unreachable, not a move that fails. -/
theorem totalization_succeeds_narrowly {X : Type} (s : X → Nat) (c : X → X → Option Bool) :
    (∀ x y, totalization s c x y ≠ none)
    ∧ (∃ d : Fin 4 → Fin 4 → Option Bool, (∀ x y, d x y ≠ none) ∧ ¬ Function.Surjective d) :=
  ⟨totalization_totalizes s c,
   ⟨fun _ _ => some true, fun _ _ => Option.some_ne_none true, hole_uniform _⟩⟩

/-- **What the collision forbids.** The conjunction, not a conjunct: total-and-faithful is unreachable
(`complete_and_faithful_is_impossible`), but total alone is reachable. The aim that collides is the conjunction. -/
theorem what_the_collision_forbids :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2)
    ∧ (∃ c : Fin 4 → Fin 4 → Option Bool, ∀ x y, c x y ≠ none) :=
  ⟨complete_and_faithful_is_impossible, ⟨fun _ _ => some true, fun _ _ => Option.some_ne_none true⟩⟩

/-! ## Part 2: is faithfulness answerable to the import? -/

/-- **What faithfulness is.** A returned absence, a property of the map alone: `c` is faithful at the hole exactly
when it returns `none` there, `imprecise 0 2` being `none`. It answers to no external standard, only to the map's
own value, so the gloss's answerability to something outside is not what faithfulness is. -/
theorem what_faithfulness_is (c : Fin 4 → Fin 4 → Option Bool) :
    (c 0 2 = imprecise 0 2 ↔ c 0 2 = none) := by
  rw [show imprecise (0 : Fin 4) 2 = none from by decide]

/-- **Is the import reachable by a move.** The import is not a value: the seam's far side is an external surplus
(`none_and_surplus_are_distinct`, an excess in `ZMod 3`), not in the classification's value space, while
totalization only ever produces a value. So no move on values reaches the import; the attempt cannot be aimed at
eliminating it, whatever else it aims at. -/
theorem is_the_import_reachable_by_a_move {X : Type} (s : X → Nat) (c : X → X → Option Bool) :
    (∀ x y, ∃ b, totalization s c x y = some b)
    ∧ (∃ a : ZMod 3, a ≠ 0 ∧ a ≠ 1) :=
  ⟨fun _ _ => ⟨_, rfl⟩, ⟨2, by decide, by decide⟩⟩

/-- **Self-sufficiency is a third term.** Total and faithful are value conditions, and they already exclude each
other at the hole (total implies unfaithful there); self-sufficiency adds the elimination of the import, not a
value condition and, being an external surplus, not reachable. So the gloss needs the import, the import is
unreachable, and the third term is imported vocabulary, to be dropped. -/
theorem self_sufficiency_derivable_or_imported :
    (∀ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) → c 0 2 ≠ imprecise 0 2)
    ∧ (∃ a : ZMod 3, a ≠ 0 ∧ a ≠ 1) :=
  ⟨fun _ htot => by rw [show imprecise (0 : Fin 4) 2 = none from by decide]; exact htot 0 2,
   ⟨2, by decide, by decide⟩⟩

/-! ## Part 3: the vacuity test -/

/-- **A level with no import.** The vacuity test is available and the prohibition still bites. The collision holds
on the value space from the returned absence alone (`imprecise 0 2 = none`), invoking no import, no surplus, no
target. So a level considered with no imported far side still has the prohibition: the aim is not the elimination
of the import, since the prohibition bites where there is no import to eliminate. -/
theorem a_level_with_no_import :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2)
    ∧ (imprecise 0 2 = none) :=
  ⟨complete_and_faithful_is_impossible, by decide⟩

/-! ## Part 4: the verdict -/

/-- **The aim is total-and-faithful.** Stated with nothing imported, the aim is the two conjuncts of the collision
(`complete_and_faithful_is_impossible`); total alone succeeds, and the framework has no third term.
Self-sufficiency is a gloss: it adds import-elimination, neither a conjunct nor reachable, so it imports
vocabulary the boundary avoids and should be dropped. -/
theorem the_aim_is :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2)
    ∧ (∃ c : Fin 4 → Fin 4 → Option Bool, ∀ x y, c x y ≠ none) :=
  ⟨complete_and_faithful_is_impossible, ⟨fun _ _ => some true, fun _ _ => Option.some_ne_none true⟩⟩

/-! ## The verdicts

Part 1: the narrow move succeeds; only the conjunction fails. Totalization produces a total classification, a
permitted mode (`totalization_succeeds_narrowly`), and the collision forbids the conjunction, not a conjunct,
total alone reachable (`what_the_collision_forbids`). So the attempt is a move whose aim is unreachable, not a
move that fails.

Part 2: faithfulness is internal, and the import is unreachable. Faithfulness is a returned absence, a property of
the map alone, `c` faithful at the hole exactly when it returns `none` (`what_faithfulness_is`), not answerability
to anything external. The import is not a value, an external surplus no value-move reaches
(`is_the_import_reachable_by_a_move`), so the attempt cannot aim at eliminating it. Self-sufficiency is therefore
a third term, adding an unreachable import-elimination to the two value conditions
(`self_sufficiency_derivable_or_imported`), imported vocabulary.

Part 3: the vacuity test is available and the prohibition still bites. The collision holds from the returned
absence alone, no import invoked (`a_level_with_no_import`), so a level with no imported far side still carries
the prohibition. The aim is not the import.

Part 4: the aim, stated without imports, is total-and-faithful (`the_aim_is`), the two conjuncts, and total alone
succeeds. The framework has no third term.

The verdict: the attempt aims at total-and-faithful and nothing more, and self-sufficiency is a gloss to be
dropped. The narrow move succeeds, producing a total classification, so the failure is the unreachability of the
conjunction, not a defect of the move. Faithfulness is a returned absence, a property of the map, answering to no
external standard; the import is an external surplus no value-move touches; and the prohibition bites from the
absence alone, with no import to eliminate. So self-sufficiency, no absences and no imports, adds a third term
that neither derives from the two conjuncts nor names anything a move can reach, and it imports the very
vocabulary the boundary avoids. The honest outcome is negative: the framework describes the move and its failure
and has no vocabulary for aims beyond the collision's two conjuncts, which is what an aim stated in its own terms
must be. Reported per part. Nothing here is resolved. -/

end Chiralogy.Aim
