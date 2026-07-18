import Chiralogy

/-! # Experiment: coherence between the arms

Coherence in the Mac Lane sense (do different routes agree), not the fusion sense (answered: no). Three
senses kept apart: within the apophatic model coherence is canonical (`cycle_is_not_the_hole`); across `Obj`
gluing is thin (`Transport`); coherence between the arms is what this tests, and it is unasked.

C1: is "the apophatic none meets the cataphatic surplus" an identity (one obstruction from two ends) or a
gloss (two obstructions co-located)? C2: does the guard's bound on a proposal differ from that account's
pointwise hole (informative) or coincide with it (redundant)? Expect adjacency and redundancy, consistent
with the thin transport result.

Stays in `Experiments/`; canonical layers untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Coherence

/-! ## C1: do the arms agree at the boundary? -/

/-- **C1: adjacency, not identity.** The apophatic none is an absence, a missing value in the codomain
`Option Bool` (`imprecise 0 2 = none`); the cataphatic surplus is an excess, a present unreached point in the
ambient `ZMod 3` (`2 ≠ 0 ∧ 2 ≠ 1`). Different ambients, opposite kinds (absence versus presence). On the proof
terms neither derives from the other and they share no substantive lemma: `complete_and_faithful_is_impossible`
is a direct contradiction on the none (decidability at the pair `0 2`), `embedding_not_iso` a case analysis on
the surplus point. They are co-located at the boundary, not one obstruction from two ends. -/
theorem none_and_surplus_are_distinct :
    (imprecise 0 2 = none) ∧ (∃ a : ZMod 3, a ≠ 0 ∧ a ≠ 1) :=
  ⟨by decide, embedding_buys_in_rich_ambient⟩

/-! ## C2: does the channel carry information? -/

/-- **C2, the structural reason.** The proposed account is the build itself: `(proposedAccount build).build`
reduces to `build`. -/
theorem account_is_the_build {X B : Type} (build : X → (X → B)) :
    (proposedAccount build).build = build := rfl

/-- **C2: redundant.** The guard's bound on a proposal is the pointwise hole applied to it: the two Props
`¬ Surjective (proposedAccount build).build` and `¬ Surjective build` are definitionally equal, and both
`proposer_guard` and `guard_is_universal` at this account are `no_reflexive_object hg build`. The channel is
coherent but carries no information: the guard tells the proposal the hole it had anyway pointwise. -/
theorem channel_carries_no_information {X B : Type} (build : X → (X → B)) :
    (¬ Function.Surjective (proposedAccount build).build) = (¬ Function.Surjective build) := rfl

/-- The two theorems coincide at the account: the channel and the pointwise hole are one term. -/
theorem proposer_guard_is_the_pointwise_hole {X B : Type} (build : X → (X → B)) {g : B → B}
    (hg : ∀ b, g b ≠ b) : proposer_guard build hg = guard_is_universal build hg := rfl

/-! ## The verdict

C1 adjacency: the none (an absence in `Option Bool`) and the surplus (an excess in `ZMod 3`) are distinct
obstructions co-located at the boundary, sharing only the boundary location, not the content. C2 redundant:
the account is the build, so the guard's bound is the pointwise hole, one term.

The arms do not agree at a shared obstruction, and the channel repeats what is pointwise. The framework is
per-object and adjacent all the way: two arms, two boundary obstructions co-located, a channel that carries
no new content. Consistent with `Transport`'s thinness. Spec rewording: 6.a.2's "the none meets the surplus"
is co-location, not a meeting; 6.b's "feeds" is data-flow without information. -/

end Chiralogy.Coherence
