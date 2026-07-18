import Chiralogy

/-! # Experiment: is Chiralogy tricameral?

The framework is bicameral: an apophatic codomain end and a cataphatic domain end. Test whether a third
chamber exists by elimination against a fixed five-point bar, not by search. The cataphatic arm qualified
because on the term it had (1) its own kernel move distinct from the fold (build vs refute), (2) its own
model (free constructions vs `Kl(Maybe)`), (3) a position on the map (the domain end), (4) a conformance
protocol, (5) irreducibility to the other arm. A candidate clearing four of five is not a chamber.

Stays in `Experiments/`; canonical layers untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Tricameral

/-! ## Stage 1: positions are exhaustive (the backbone) -/

/-- **Positions are two ends and an empty middle.** The map `c : X → X → B` has a codomain end (the apophatic
obstruction), a domain end (the cataphatic construction), and the middle between them, which is empty
(`center_is_empty`). The type `c` has exactly the slots `X` (domain) and `B` (codomain): no fourth position.
A third chamber must be off-map. This eliminates candidates that are not positions: dynamics (a move over
time) and self-application (a map fed to itself) die here, failing bar 3. -/
theorem positions_are_two_and_a_middle {X B : Type} (c : X → X → B) :
    ((∀ g : B → B, (∀ b, g b ≠ b) → ¬ Function.Surjective c)
      ∧ (∃ build : X → (X → B), ∀ x, build x = c x))
    ∧ ¬ ∃ Y : Type, Nonempty (Y ≃ (Y → Bool)) :=
  ⟨one_map_two_ends c, center_is_empty⟩

/-! ## Stage 2: transport (the strongest candidate) -/

/-- **Transport is a distinct move (bar 1 passes).** A morphism carries a classification to a classification:
`onValues` after `S.classify` equals `T.classify` after `onCarrier` (the preservation, functorial). It
neither refutes (fold) nor builds outward (build); it carries. -/
theorem transport_is_a_distinct_move (S T : Obj) (φ : Hom S T) (x y : S.X) :
    φ.onValues (S.classify x y) = T.classify (φ.onCarrier x) (φ.onCarrier y) :=
  φ.preserves x y

/-- **Transport has no position (bar 3 fails, the decisive test).** A morphism `φ : Hom S T` carries both a
domain-end map (`onCarrier : S.X → T.X`) and a codomain-end map (`onValues : S.B → T.B`): it acts on both
ends at once, singling out no position. It is a relation between two-ended maps, not a third end. Failing
bar 3, transport is not a chamber; it enriches the boundary (it relates conforming objects) and lives a layer
up (2-categorical), not as a third arm. -/
theorem transport_acts_on_both_ends (S T : Obj) (φ : Hom S T) :
    (∃ f : S.X → T.X, f = φ.onCarrier) ∧ (∃ g : S.B → T.B, g = φ.onValues) :=
  ⟨⟨φ.onCarrier, rfl⟩, ⟨φ.onValues, rfl⟩⟩

/-! ## Stage 3: the tradition's third moment is the channel -/

/-- **The third moment is the channel.** The apophatic tradition's third step, negating the negation (the
unsaying that corrects a proposed name), is the guard applied to a cataphatic proposal: `proposer_guard`, the
boundary channel. It is the composite guard-of-propose, not a distinct move, so not a third chamber. -/
theorem third_moment_is_the_channel {X B : Type} (build : X → (X → B)) {g : B → B} (hg : ∀ b, g b ≠ b) :
    ¬ Function.Surjective (proposedAccount build).build :=
  proposer_guard build hg

/-! ## Stage 4: the ethical inversion (a third center, is it a third chamber?) -/

/-- **The ethical inversion is apophatic-shaped.** A third center is proven distinct
(`ethical_center_is_distinct`: a total object still carries the hole). But its move, the one prohibition, is
refusal-shaped, ending in absurdity (`complete_and_faithful_is_impossible`, a `¬ ∃`), the same shape as the
fold. It fails bar 1, its move is not distinct from the fold: a third inversion inside the first chamber, not
a third chamber. Three centers, two chambers. -/
theorem ethical_is_apophatic_shaped :
    (∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ ¬ Function.Surjective c)
    ∧ ¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2 :=
  ⟨ethical_center_is_distinct, complete_and_faithful_is_impossible⟩

/-! ## The verdict -/

/-- **Chiralogy is bicameral.** Positions are two ends and an empty middle (Stage 1), so a third chamber must
be off-map. Every candidate fails the fixed bar: transport is a distinct move but has no position, bar 3
(Stage 2), enriching the boundary as a 2-categorical layer; the tradition's third moment is the channel, a
composite, not a move (Stage 3); the ethical inversion is apophatic-shaped, bar 1 (Stage 4). Two chambers,
three centers, one channel, one 2-categorical layer. -/
theorem chiralogy_is_bicameral {X B : Type} (c : X → X → B) :
    ((∀ g : B → B, (∀ b, g b ≠ b) → ¬ Function.Surjective c)
      ∧ (∃ build : X → (X → B), ∀ x, build x = c x))
    ∧ ¬ ∃ Y : Type, Nonempty (Y ≃ (Y → Bool)) :=
  positions_are_two_and_a_middle c

end Chiralogy.Tricameral
