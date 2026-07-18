import Chiralogy

/-! # Experiment: no transcendent judgement (the negative, derived)

Define the distinction by variance, not by importing philosophy. A judgement (a map from accounts to
verdicts) is **transcendent** if its verdict depends on the case: two accounts receive different verdicts, a
standard applied from outside. It is **immanent** if the verdict cannot vary: the standard is not applied to
the object, it is the object's own structure returned. The discriminating test is whether the verdict map
can be non-constant.

This build shows Chiralogy's judgement is constant and that no case-varying verdict can be formed from the
framework's flows, so transcendent judgement is structurally unavailable and immanence is forced. Everything
is re-derived from canonical (the earlier experiments are not compiled).

Stays in `Experiments/`; canonical layers untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Judgement

/-! ## Part 1: the framework's judgement is constant -/

/-- **The verdict is constant.** Every account receives the same answer, bounded: the verdict holds of every
account with a fixed-point-free codomain (`guard_is_universal`). The answer never varies with the case. -/
theorem judgement_is_constant {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) :
    ∀ build : X → (X → B), ¬ Function.Surjective build :=
  fun build => guard_is_universal build hg

/-- **The verdict ignores the case.** Two structurally different accounts (constant `true` and constant
`false` on `Fin 2`) receive identical verdicts: both bounded. The account's identity does not reach the
verdict. -/
theorem verdict_ignores_the_case :
    ((fun (_ _ : Fin 2) => true) ≠ (fun (_ _ : Fin 2) => false))
    ∧ (¬ Function.Surjective (fun (_ _ : Fin 2) => true))
    ∧ (¬ Function.Surjective (fun (_ _ : Fin 2) => false)) :=
  ⟨by decide,
   no_reflexive_object (g := fun b => !b) (by decide) _,
   no_reflexive_object (g := fun b => !b) (by decide) _⟩

/-! ## Part 2: the negative, no transcendent judgement is available -/

/-- **Erasure.** The guard's output is a `Prop`, proof-irrelevant: any two proofs are equal. -/
theorem guard_erases {X B : Type} (c : X → X → B) (h₁ h₂ : ¬ Function.Surjective c) : h₁ = h₂ := rfl

/-- **No discriminating verdict from the channel.** Any verdict formed from the guard's output is constant
in it (erasure): a case-varying verdict would have to depend on the guard's proof, which it cannot. -/
theorem no_discriminating_verdict {X B V : Type} (c : X → X → B)
    (J : ¬ Function.Surjective c → V) (h₁ h₂ : ¬ Function.Surjective c) : J h₁ = J h₂ :=
  congrArg J (guard_erases c h₁ h₂)

/-- The cataphatic ambient carries no case data to the apophatic verdict (input unused). -/
theorem ambient_informs_nothing_apophatic {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) (c : X → X → B)
    (_ambient₁ _ambient₂ : Type) : ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-- The surplus carries no case data to the apophatic verdict (input unused). -/
theorem surplus_constrains_nothing {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) (c : X → X → B)
    (_surplus : ∃ a : ZMod 3, a ≠ 0 ∧ a ≠ 1) : ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-! **Immanence is forced.** No verdict formed from the framework's flows can vary with the case: the guard's
own verdict is constant (`judgement_is_constant`); every verdict derived from the guard's output is constant
(`no_discriminating_verdict`, from erasure); and the two traced flows carry no case data
(`ambient_informs_nothing_apophatic`, `surplus_constrains_nothing`, inputs unused). So every judgement in
Chiralogy returns the object's own limit. This is over the flows the framework has: the hunt traced the
certification channel and two candidate flows, not every conceivable operation, so the claim is that no flow
among those it has can discriminate, not an exhaustiveness proof. -/

/-! ## Part 3: the four registers -/

/-- **Structure is operation, one term.** The hole (`hole_uniform`, the structure) and the guard
(`guard_is_universal`, the operation) are the same term, `no_reflexive_object` at the fixed-point-free
endomap. Identity, not resemblance. -/
theorem structure_is_operation {X : Type} (c : X → X → Option Bool) :
    hole_uniform c = guard_is_universal c optCycle_fixedpointfree := rfl

/-- **The prohibition needs no target.** The norm (`totalization_is_self_defeating`, the verdict register) is
derived from the object's own impossibility, with no target parameter: an immanent judgement needs no
external standard. `complete_and_faithful_is_impossible` is that impossibility, targetless. -/
theorem prohibition_needs_no_target :
    ¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2 :=
  complete_and_faithful_is_impossible

/-- **The ethical center explained.** It is a distinct center (`ethical_center_is_distinct`) but its move is
apophatic-shaped (a `¬ ∃`, the same limit). Under immanence this is expected: judgement is its own register
(a distinct center) yet returns the same limit (the same move). -/
theorem ethical_center_explained :
    (∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ ¬ Function.Surjective c)
    ∧ ¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2 :=
  ⟨ethical_center_is_distinct, complete_and_faithful_is_impossible⟩

/-! ## The verdict

Part 1: the verdict map is constant (every account bounded; different accounts, identical verdicts). Part 2:
no verdict formed from the framework's flows can discriminate (the guard is constant, maps out of it are
constant by erasure, the traced flows carry no case data), stated honestly as over the flows it has, not
exhaustively. So transcendent judgement is structurally unavailable and immanence is forced: every judgement
returns the object's own limit. Part 3: structure and operation are one term (`rfl`); the norm and the
verdict are derived from the same hole. This explains the targetless prohibition (no external standard) and
the distinct-but-apophatic ethical center (its own register, the same limit). -/

end Chiralogy.Judgement
