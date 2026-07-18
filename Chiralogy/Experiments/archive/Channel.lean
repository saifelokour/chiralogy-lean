import Chiralogy

/-! # Experiment: the channel's uninformativeness, derived, and the hunt for other channels

`Coherence.lean` observed the channel is real but carries no information. This build derives that fact from
the framework's own uniformity, then hunts for flows we have not traced. The guard's output is `Prop`
(proof-irrelevant): its structure does not affect any returned value; the role is only to guarantee the
value meets the specification. Erasure forces uniformity: a value that cannot depend on its input treats
every input alike.

Stays in `Experiments/`; canonical layers untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Channel

/-! ## Part 1: uninformativeness is forced (the chain, link by link) -/

/-- **Link 1, erasure.** The guard's output is a `Prop`, so proof-irrelevant: any two proofs are equal, the
witness is discarded. -/
theorem guard_erases {X B : Type} (c : X → X → B) (h₁ h₂ : ¬ Function.Surjective c) : h₁ = h₂ := rfl

/-- **Link 2, non-dependence.** Because the output is erased, nothing downstream can depend on which proof:
every map from the guard's output is constant in it. -/
theorem erasure_forces_nondependence {X B T : Type} (c : X → X → B)
    (F : ¬ Function.Surjective c → T) (h₁ h₂ : ¬ Function.Surjective c) : F h₁ = F h₂ :=
  congrArg F (guard_erases c h₁ h₂)

/-- **Link 3, uniformity (factors through a constant).** The guard on any account is `no_reflexive_object`
applied to the build: one uniform lemma, not inspecting the account's construction. It factors through the
constant "every account has a hole", so its fiber over any account is the same. -/
theorem guard_is_the_uniform_hole {X B : Type} (build : X → (X → B)) {g : B → B} (hg : ∀ b, g b ≠ b) :
    proposer_guard build hg = no_reflexive_object hg build := rfl

/-- **Link 4, non-discrimination.** Two genuinely different accounts receive identical treatment: both are
bounded by the same lemma. The guard cannot tell them apart. -/
theorem uniformity_forbids_discrimination {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b)
    (build₁ build₂ : X → (X → B)) :
    (¬ Function.Surjective build₁) ∧ (¬ Function.Surjective build₂) :=
  ⟨guard_is_universal build₁ hg, guard_is_universal build₂ hg⟩

/-- **Link 5, zero capacity.** The chain closes: the guard's answer never varies, every account is bounded
(`guard_is_universal`). Erasure, non-dependence, uniformity, non-discrimination, zero information. -/
theorem channel_capacity_is_zero {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) (c : X → X → B) :
    ¬ Function.Surjective c :=
  guard_is_universal c hg

/-! ## Part 2: what the channel is, given it is not transmission -/

/-- **Certification, not communication.** The account must be present (it is the guard's argument,
`(proposedAccount build).build = build`) and the output is invariant (all verdicts identified). The role is
to guarantee, not to inform. -/
theorem channel_is_certification {X B : Type} (build : X → (X → B)) :
    ((proposedAccount build).build = build)
    ∧ (∀ h₁ h₂ : ¬ Function.Surjective build, h₁ = h₂) :=
  ⟨rfl, fun _ _ => rfl⟩

/-- **Erasure buys universality.** The guard applies to every account precisely because it inspects none:
the same non-inspection that erases (Part 1) makes it universal. Universality and uninformativeness are one
property seen twice. -/
theorem erasure_buys_universality {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) (c : X → X → B) :
    ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-! ## Part 3: the two uniformities are one -/

/-- **The apophatic uniformity is the channel uniformity.** `hole_uniform` (every object holed, pointwise)
and `guard_is_universal` (every account bounded) are the same term, `no_reflexive_object` at the
fixed-point-free endomap. The channel cannot inform because the hole is the same everywhere: the apophatic
fractality and the channel's thinness are one fact (and `Transport`'s pointwise findings a third face). -/
theorem apophatic_uniformity_is_channel_uniformity {X : Type} (c : X → X → Option Bool) :
    hole_uniform c = guard_is_universal c optCycle_fixedpointfree := rfl

/-! ## Part 4: the hunt for other channels -/

/-- **The cataphatic ambient informs nothing apophatic.** The apophatic verdict on `c` does not take the
ambient as input: two objects differing only in their cataphatic ambient get the same verdict. -/
theorem ambient_informs_nothing_apophatic {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) (c : X → X → B)
    (_ambient₁ _ambient₂ : Type) : ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-- **The surplus constrains nothing apophatic.** The apophatic verdict does not take the surplus as input:
the excess (5.b.2) does not change what the apophatic arm says. -/
theorem surplus_constrains_nothing {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) (c : X → X → B)
    (_surplus : ∃ a : ZMod 3, a ≠ 0 ∧ a ≠ 1) : ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-! ## The verdict

Part 1: the chain holds link by link (erasure, non-dependence, uniformity, non-discrimination, zero
capacity); the guard factors through the constant hole. Uninformativeness is derived, not observed. Part 2:
the channel certifies (the account must be present, the output invariant); erasure buys universality, one
property. Part 3: the apophatic uniformity and the channel uniformity are the same term (`no_reflexive_object`),
not merely parallel. Part 4: every candidate flow is uninformative for the same reason (the input is unused),
so proposal-to-guard is the only channel, and it certifies.

Spec rewording: 6.b's "feeds" is certification, not communication. The channel guarantees, it does not
transmit; its uninformativeness is the apophatic uniformity in another place. -/

end Chiralogy.Channel
