import Chiralogy

/-! # Experiment: separation requires a discriminating verdict (P vs NP, reoriented)

A circuit lower bound proceeds by a property `P`: the hard function has `P`, every function in the class `C`
lacks it (Razborov-Rudich). A natural proof asks for constructivity (membership decidable in time polynomial
in the truth table), largeness (a noticeable fraction have `P`), and usefulness (`P` separates). Williams
makes constructivity equivalent to `NEXP ⊄ C`. So a separating property must be computed from the case and
must not be universal.

This build tests whether such a property is formable from the framework's flows. Nothing about P vs NP is
resolved; no separation is claimed either way. The result is honest against its own gate: the framework's own
verdict cannot discriminate, but discrimination itself is expressible, so the strong "separation not
expressible" claim fails and the true finding is a positional split.

Stays in `Experiments/`; canonical layers untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Separation

/-! ## Part 1: a separation is a discriminating verdict -/

/-- A separation in the Razborov-Rudich shape: a verdict the hard object satisfies and another lacks. -/
def Separates {α : Type} (V : α → Prop) : Prop := ∃ a b, V a ∧ ¬ V b

/-- **The model.** Separation is discrimination: some object has the property, another does not. This is a
necessary condition, not the full definition: usefulness against a complexity class is stronger, and the
framework has no notion of complexity class, so this is the weakest faithful shape. If the framework's verdict
fails even this, it cannot separate; meeting it is not sufficient. -/
theorem separation_is_a_discriminating_verdict {α : Type} (V : α → Prop) :
    Separates V ↔ ∃ a b, V a ∧ ¬ V b := Iff.rfl

/-! ## Part 2: the framework's own verdict cannot discriminate -/

/-- **The framework's verdict does not separate.** Its verdict is `c ↦ ¬ Surjective c`; it holds of every
object (`guard_is_universal`), so no object supplies the `Surjective b` the second slot needs. Scope: the
framework's own verdict, not every predicate. -/
theorem framework_verdict_is_nondiscriminating {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) :
    ¬ Separates (fun c : X → X → B => ¬ Function.Surjective c) := by
  rintro ⟨_, b, _, hb⟩
  exact hb (guard_is_universal b hg)

/-- **No separation from the apophatic verdict.** The framework's verdict does not separate, and any verdict
formed from the guard's output is constant (`erasure_forces_nondependence`), so it too fails to separate. Over
the flows the framework has (the certification channel and the traced candidate flows), not a quantification
over all conceivable operations. -/
theorem no_separation_from_the_apophatic_verdict {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) :
    ¬ Separates (fun c : X → X → B => ¬ Function.Surjective c) :=
  framework_verdict_is_nondiscriminating hg

/-! ## Part 3: the two axes, largeness and constructivity -/

/-- **Maximally large.** The verdict holds of every object (`guard_is_universal`): universal, so it excludes
nothing. Largeness at its limit. -/
theorem framework_verdict_is_maximally_large {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) :
    ∀ c : X → X → B, ¬ Function.Surjective c :=
  fun c => no_reflexive_object hg c

/-- **Zero constructive.** The verdict is not computed from the case: the input is erased and every map out
of it is constant (`erasure_forces_nondependence`). Membership carries no case-information. -/
theorem framework_verdict_is_zero_constructive {X B T : Type} (c : X → X → B)
    (F : ¬ Function.Surjective c → T) (h₁ h₂ : ¬ Function.Surjective c) : F h₁ = F h₂ :=
  erasure_forces_nondependence c F h₁ h₂

/-- **The degenerate corner.** The framework's verdict is maximally large and not constructive. This is a
positional mapping onto the natural-proofs axes, nothing more: the framework is not a proof technique and the
barrier does not "apply" to it. A separating property sits at a different position, non-universal and
case-computed. -/
theorem degenerate_corner {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) :
    (∀ c : X → X → B, ¬ Function.Surjective c)
    ∧ (∀ (c : X → X → B) (F : ¬ Function.Surjective c → Bool) (h₁ h₂ : ¬ Function.Surjective c), F h₁ = F h₂) :=
  ⟨fun c => no_reflexive_object hg c, fun c F h₁ h₂ => erasure_forces_nondependence c F h₁ h₂⟩

/-! ## Part 4: the gate, a cataphatic discriminating verdict -/

/-- **The gate fires.** A cataphatic forget operation (`restrict`) composed with evaluation discriminates
objects: the constant-`1` object satisfies `restrict (c 0 0) = true`, the constant-`0` object does not. So a
separating verdict, in the Part 1 sense, is expressible. A bare decidable predicate `c ↦ c 0 0 = 1`
discriminates too: discrimination is not scarce, in this framework or any with distinguishable objects. -/
theorem cataphatic_verdict_discriminates :
    Separates (fun c : Fin 1 → Fin 1 → ZMod 3 => restrict (c 0 0) = true) :=
  ⟨fun _ _ => 1, fun _ _ => 0, by decide, by decide⟩

/-- **Separation is split, not absent.** What fails to discriminate is the framework's own verdict
(apophatic, universal). Discrimination is expressible, but it lives in the cataphatic arm as a borrowed
operation (`cataphatic_verdict_discriminates`), renders an ambient value rather than the structural verdict,
and cannot cross the zero-capacity channel (`erasure_forces_nondependence`, `channel_capacity_is_zero`) to
become it. So the framework cannot render a separation as its own structural verdict, though it can host
separating predicates. Over the framework's flows; nothing here concerns P vs NP. -/
theorem separation_is_split_not_absent {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) :
    Separates (fun c : Fin 1 → Fin 1 → ZMod 3 => restrict (c 0 0) = true)
    ∧ ¬ Separates (fun c : X → X → B => ¬ Function.Surjective c)
    ∧ (∀ (c : X → X → B) (F : ¬ Function.Surjective c → Bool) (h₁ h₂ : ¬ Function.Surjective c), F h₁ = F h₂) :=
  ⟨cataphatic_verdict_discriminates, framework_verdict_is_nondiscriminating hg,
   fun c F h₁ h₂ => erasure_forces_nondependence c F h₁ h₂⟩

/-! ## The verdict

Part 1: the model is discrimination (a necessary condition for RR separation, not the full useful-against-a-
class definition, which the framework cannot state). Part 2: the framework's own verdict does not
discriminate, universal by `guard_is_universal`, scope the flows. Part 3: that verdict sits at the degenerate
corner, maximally large and zero-constructive; the mapping is positional, the barrier does not apply. Part 4:
the gate fires. A cataphatic forget operation discriminates objects, and a bare decidable predicate does too,
so separating predicates are expressible; the strong claim that separation is not expressible is false.

What survives is narrow and honest: the framework's own verdict cannot separate, and its discrimination
(cataphatic, borrowed) is split from its verdict-rendering (apophatic, universal) by a zero-capacity channel,
so no single flow renders a discriminating structural verdict. This is a statement about the framework's own
verdict, not about the expressibility of separations in general, and not about P vs NP, which is untouched. -/

end Chiralogy.Separation
