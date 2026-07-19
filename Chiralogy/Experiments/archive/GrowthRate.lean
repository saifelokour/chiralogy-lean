import Chiralogy

/-! # Experiment: growth rate as a grading (does the telescope magnify?)

Angle 3 found `grade (selfApply) = 2 + 12 = 14` while the ambient cardinalities ran 2, 4, 16: the sizes
compounded and the difference-grade recorded a sum. Categorical entropy (Dimitrov-Haiden-Katzarkov-Kontsevich;
Ikeda) defines the growth rate of an endofunctor's iterates as the mass growth of `F^n`. The general theory
needs a triangulated category with a stability condition to define mass; for finite objects cardinality is
the mass, and the growth of `card (F^n A)` is direct.

Test whether the ratio-grade is an invariant the difference-grade fails to record, and whether the framework
has an intrinsic endofunctor to iterate. Finite instance throughout: `F X = X × X` on `Bool`, cards 2, 4, 16.

Stays in `Experiments/`; canonical untouched; nothing about P vs NP resolved. -/

open Chiralogy

namespace Chiralogy.GrowthRate

/-- The doubling endofunctor on `Type` (reducible, so the product's `Fintype` is found). -/
abbrev F (X : Type) : Type := X × X

/-- **The growth law.** `F` squares the cardinality: `card (F X) = card X ^ 2`. -/
theorem F_squares_cardinality (X : Type) [Fintype X] :
    Fintype.card (F X) = Fintype.card X ^ 2 := by
  simp only [F, Fintype.card_prod, pow_two]

/-- The iterated cardinalities on `Bool`: 2, 4, 16. The sizes compound. -/
theorem card_sequence :
    Fintype.card Bool = 2 ∧ Fintype.card (F Bool) = 4 ∧ Fintype.card (F (F Bool)) = 16 := by
  simp [Fintype.card_prod, Fintype.card_bool]

/-! ## Part 1: the two gradings on the iterated tower -/

/-- **The difference-grade (increment): 2, 12.** Non-constant, as Angle 3 found. -/
theorem increment_sequence :
    Fintype.card (F Bool) - Fintype.card Bool = 2
    ∧ Fintype.card (F (F Bool)) - Fintype.card (F Bool) = 12 := by
  simp [Fintype.card_prod, Fintype.card_bool]

/-- **The rate-grade (ratio): 2, 4.** Also non-constant: not a fixed exponential rate. -/
theorem rate_sequence :
    Fintype.card (F Bool) / Fintype.card Bool = 2
    ∧ Fintype.card (F (F Bool)) / Fintype.card (F Bool) = 4 := by
  simp [Fintype.card_prod, Fintype.card_bool]

/-- **Repackaging.** Each transition is described both additively (current + increment) and multiplicatively
(rate times current) by the same cards. The rate is not information beyond the sizes: given the cards, both
grades are determined, and each transition reconstructs from either. -/
theorem rate_repackages_increment :
    (Fintype.card (F Bool)
        = Fintype.card Bool + (Fintype.card (F Bool) - Fintype.card Bool)
      ∧ Fintype.card (F Bool)
        = Fintype.card (F Bool) / Fintype.card Bool * Fintype.card Bool)
    ∧ (Fintype.card (F (F Bool))
        = Fintype.card (F Bool) + (Fintype.card (F (F Bool)) - Fintype.card (F Bool))
      ∧ Fintype.card (F (F Bool))
        = Fintype.card (F (F Bool)) / Fintype.card (F Bool) * Fintype.card (F Bool)) := by
  simp [Fintype.card_prod, Fintype.card_bool]

/-! ## Part 2: is the growth rate an invariant?

The rate at each stage is the current size (`F` squares, so `card (F X) / card X = card X`), so the rate is a
function of the card sequence, exactly as the increment is. Neither distinguishes more than the sizes. -/

/-- **The rate is the current size.** For any nonempty finite ambient, `card (F X) / card X = card X`: the
rate is read off the cards, the same data the increment reads. -/
theorem rate_equals_size (X : Type) [Fintype X] (h : Fintype.card X ≠ 0) :
    Fintype.card (F X) / Fintype.card X = Fintype.card X := by
  rw [F_squares_cardinality, pow_two, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h)]

/-! ## Part 3: is the endofunctor intrinsic or supplied? -/

/-- The doubling map is definable for any type with no classification: a construction on the bare ambient
(the cartesian product), borrowed from `Type`, not arising from `c`. -/
def double (A : Type) : A → A × A := fun a => (a, a)

/-- **The endofunctor is supplied.** To lift the doubling to the framework's objects, which carry a
classification, a classification on `X × X` is needed; `c` on `X` supplies none, and such classifications are
free (distinct ones exist that `c` cannot select). So the growth rate measures a borrowed construction, as the
transpose could not iterate on the framework's own data. -/
theorem doubled_classification_is_supplied :
    ∃ c₂ c₂' : (Bool × Bool) → (Bool × Bool) → Option Bool, c₂ ≠ c₂' :=
  ⟨fun _ _ => some true, fun _ _ => some false, fun h => by
    have := congrFun (congrFun h (true, true)) (true, true); simp at this⟩

/-! ## The verdict

Part 1: repackaging. The increment (2, 12) and the rate (2, 4) are the additive and multiplicative readings of
one card sequence (2, 4, 16): each transition equals current + increment and rate times current
(`rate_repackages_increment`), so given the sizes both grades are determined, neither new. The rate does
record the compounding the difference-grade sums away, but as the same card data read multiplicatively, which
is the difference-grade of the log-sizes, not a fresh invariant. And from `Primitives`, the framework's
composition law is additive, so this multiplicative reading is not a grade its composition produces.

Part 2: the rate is a function of the sizes (`rate_equals_size`: the rate is the current card), so it
distinguishes exactly what the cards do, no more than the increment. Not constant either (2, 4), so not even a
clean exponential rate.

Part 3: the endofunctor is supplied. The doubling is the cartesian product, definable on any bare type
(`double`), and to act on the framework's classifying objects it needs a classification on `X × X` that `c`
does not supply (`doubled_classification_is_supplied`), exactly as the transpose could not iterate. The growth
rate measures a borrowed construction, the same borrowing as the rest of the cataphatic arm.

The verdict: growth rate is not a grading the framework owns. It is a multiplicative repackaging of the same
sizes the difference-grade records additively, on an endofunctor the framework does not own. The eleventh
wall. Nothing here is about P vs NP; no complexity class, no separation. -/

end Chiralogy.GrowthRate
