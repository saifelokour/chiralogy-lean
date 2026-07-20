import Chiralogy

/-! # Experiment: can anything detect that a totalization occurred?

The prohibition forbids totalizing to completeness. Test whether any framework operation can determine, from a
resulting classification, that a totalization was performed, and whether a move achieves totality-in-effect
without taking a quotient.

Detection means: an operation distinguishes a totalized/untotalized pair with the same resulting values, not
merely some pair. Vacating means: the level declares a ground as a nullary generator and the classification
never lands on it, no quotient taken; a bare non-surjective function does not vacate anything, since the
framework has no notion of what the codomain was meant to contain. Stays in `Experiments/`; canonical untouched;
nothing resolved. -/

open Chiralogy

namespace Chiralogy.Detection

/-! ## Part 1: the guard cannot detect -/

/-- **The guard cannot detect totalization.** The guard's value is a proof of `¬ Surjective c`, erased
(`guard_erases`), so any detector built on it is constant (`erasure_forces_nondependence`): it separates no two
proofs, hence no totalized from untotalized account. -/
theorem guard_cannot_detect_totalization {X B T : Type} (c : X → X → B)
    (F : (¬ Function.Surjective c) → T) (h₁ h₂ : ¬ Function.Surjective c) :
    F h₁ = F h₂ :=
  erasure_forces_nondependence c F h₁ h₂

/-- **Blindness is the price of universality.** The guard bounds every account (`guard_is_universal` on both)
because it inspects none: its verdict is internally constant. Inability to detect is its universality, not a
defect beside it, and it is not concealment, nothing is hidden, the guard does not look. -/
theorem blindness_is_the_price_of_universality {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b)
    (c₁ c₂ : X → X → B) :
    ((¬ Function.Surjective c₁) ∧ (¬ Function.Surjective c₂))
    ∧ (∀ (T : Type) (F : (¬ Function.Surjective c₁) → T) (h₁ h₂ : ¬ Function.Surjective c₁), F h₁ = F h₂) :=
  ⟨⟨guard_is_universal c₁ hg, guard_is_universal c₂ hg⟩,
   fun _ F h₁ h₂ => erasure_forces_nondependence c₁ F h₁ h₂⟩

/-! ## Part 2: does anything else detect? -/

/-- **The protocol cannot detect.** Membership tests can-differ and non-degeneracy. A totalized account (total,
non-degenerate) passes both, and so does an untotalized one (partial, non-degenerate): conformance does not
separate them. -/
theorem protocol_cannot_detect :
    (∃ c : Fin 2 → Fin 2 → Option Bool, NonDegenerate c ∧ ∀ x y, c x y ≠ none)
    ∧ (∃ c : Fin 2 → Fin 2 → Option Bool, NonDegenerate c ∧ ∃ x y, c x y = none) :=
  ⟨⟨fun x y => some (decide (x = y)), ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩, fun _ _ => by simp⟩,
   ⟨fun x y => if x = y then some true else none, ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩,
     ⟨0, 1, by decide⟩⟩⟩

/-- A classification that used the ground `false` (a throw at one cell). -/
def cUsed : Fin 2 → Fin 2 → Bool ⊕ Bool :=
  fun x y => if x = 0 ∧ y = 1 then Sum.inr false else if x = 1 ∧ y = 0 then Sum.inl false else Sum.inl true

/-- A classification with the same resulting values that never had that ground. -/
def cInnocent : Fin 2 → Fin 2 → Bool ⊕ Bool :=
  fun x y => if x = 1 ∧ y = 0 then Sum.inl false else Sum.inl true

/-- **The closure needs the move, not the state.** `cUsed` used the ground `false`; `cInnocent` never did; yet
closing that ground in `cUsed` yields exactly `cInnocent`. The totalized and untotalized classifications have
the same resulting values, so from the resulting classification alone the closure operation cannot be
recovered. -/
theorem closure_needs_the_move_not_the_state :
    (∃ x y, cUsed x y = Sum.inr false)
    ∧ (¬ ∃ x y, cInnocent x y = Sum.inr false)
    ∧ (fun x y => closeE (fun e => decide (e = false)) (cUsed x y)) = cInnocent :=
  ⟨⟨0, 1, by decide⟩, by decide, by decide⟩

/-- **Nothing detects from the state.** Since the closed `cUsed` equals `cInnocent`, every operation on the
resulting classification returns the same value on both: no framework notion taking a classification alone
separates the totalized from the innocent. The prohibition is over moves; nothing in a resulting classification
records which move produced it, and a move whose result is indistinguishable from innocence is still forbidden,
the prohibition being on the act. -/
theorem nothing_detects_from_the_state (T : Type) (F : (Fin 2 → Fin 2 → Bool ⊕ Bool) → T) :
    F (fun x y => closeE (fun e => decide (e = false)) (cUsed x y)) = F cInnocent :=
  congrArg F closure_needs_the_move_not_the_state.2.2

/-! ## Part 3: totality without a quotient

The ground must be declared by the level, `throwExcept` supplying the two grounds of Except as nullary
generators, so a ground exists in the presentation whether or not the classification lands on it. -/

/-- A classification using the ground `false` and never the ground `true`. -/
def vacatedClassify : Fin 2 → Fin 2 → Bool ⊕ Bool :=
  fun x y => if x = y then Sum.inl true else Sum.inr false

/-- **Vacating a declared ground.** The classification lands on the ground `false` and never on `true`, yet
`true` remains a legitimate value of the theory: `throwExcept true` is the declared nullary generator, present
whether or not the classification uses it. -/
theorem vacating_a_declared_ground :
    (∃ x y, vacatedClassify x y = Sum.inr false)
    ∧ (¬ ∃ x y, vacatedClassify x y = Sum.inr true)
    ∧ throwExcept true = Sum.inr true :=
  ⟨⟨0, 1, by decide⟩, by decide, rfl⟩

/-- **Vacating is not a closure.** No quotient is taken: both grounds remain distinct declared throws (the
theory is unchanged, verified), and the vacated classification still exhibits `inr false` as a live throw. A
closure of that ground would instead identify it with a verdict (`closeE`). -/
theorem vacating_is_not_a_closure :
    (throwExcept false ≠ throwExcept true)
    ∧ (∃ x y, vacatedClassify x y = Sum.inr false)
    ∧ (closeE (fun e => decide (e = false)) (Sum.inr false) = Sum.inl true) :=
  ⟨by decide, ⟨0, 1, by decide⟩, by decide⟩

/-- **Is vacating within the prohibition.** The prohibition (`full_totality_collides`) forbids being total and
yet keeping a throw. A vacated-total classification is total without keeping a throw, non-degenerate, and takes
no quotient (both grounds still declared): so it is not forbidden, permitted and quotient-free. The prohibition
is over the closure move; vacating takes no closure, so the prohibition does not reach it, and the distinction
from closing lies in the move alone, consistent with Part 2. -/
theorem is_vacating_within_the_prohibition :
    ∃ c : Fin 2 → Fin 2 → Bool ⊕ Bool,
      (∀ x y, ∃ b, c x y = Sum.inl b)
      ∧ (∃ x x', c x ≠ c x')
      ∧ throwExcept false ≠ throwExcept true :=
  ⟨fun x y => Sum.inl (decide (x = y)), fun x y => ⟨decide (x = y), rfl⟩,
   ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩, by decide⟩

/-! ## The verdicts

Part 1: the guard's blindness follows from erasure. Its value is a proof of non-surjectivity, erased, so any
detector on it is constant (`guard_cannot_detect_totalization`); it bounds every account precisely because it
inspects none (`blindness_is_the_price_of_universality`). Blindness is universality, not concealment, nothing is
hidden.

Part 2: no operation detects totalization from a resulting classification. The protocol accepts a totalized and
an untotalized account alike (`protocol_cannot_detect`); a closed classification equals an innocent one with the
same values (`closure_needs_the_move_not_the_state`), so every operation on the state returns the same on both
(`nothing_detects_from_the_state`). The pair is genuinely totalized and untotalized with matching results, so
the survey is not trivial: the prohibition is over moves, and the state records no move. This is the correct
shape for a prohibition on an act, not a deficiency.

Part 3: vacating a declared ground is expressible and is not a closure. The level declares the ground
(`throwExcept`), so the classification can decline to use it (`vacating_a_declared_ground`) without taking a
quotient, the theory unchanged (`vacating_is_not_a_closure`). A vacated-total classification is total without
keeping a throw, so the prohibition, stated over closures, does not reach it (`is_vacating_within_the_prohibition`):
it is permitted and quotient-free, a totality-in-effect that closing would reach only by a move the state does
not record. Nothing here is resolved. -/

end Chiralogy.Detection
