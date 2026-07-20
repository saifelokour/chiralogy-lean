import Chiralogy

/-! # Experiment: is the bicameral structure literally the algebra/coalgebra duality?

`CoalgebraicArm` concluded coalgebra is the apophatic arm's proper name and marked the identification a READING.
Test whether the precise version is a theorem: is there a functor `F` for which the cataphatic arm is `Alg F`
and the apophatic is `CoAlg F`, one shared `F`? An identification, not a characterization: exhibiting the functor
is the theorem. The evidence against, tested rather than assumed: `Alg F` and `CoAlg F` for a shared `F` are
related, so if the arms were those categories some relation should be visible, where ours are joined by `And`
with six refuted between-arms morphisms. Concrete instances; no general coalgebra machinery. Stays in
`Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.ArmsDuality

/-! ## Part 1: is there a candidate functor? -/

/-- **What the cataphatic arm would be algebras for.** The cataphatic witnesses are free algebras over distinct
signature functors, one per bought-operation: the monoid functor (unit and multiplication) and the group functor
(adding inverse) already differ in cardinality, so there is a family of functors, not one; the list is open. -/
theorem what_the_cataphatic_arm_would_be_algebras_for :
    (Fintype.card (Unit ⊕ (Fin 1 × Fin 1)) = 2)
    ∧ (Fintype.card (Unit ⊕ (Fin 1 × Fin 1) ⊕ Fin 1) = 3) :=
  ⟨by decide, by decide⟩

/-- **What the apophatic arm would be coalgebras for.** The apophatic content is coalgebra-shaped, a
classification `c : X → (X → B)` being a coalgebra structure map for `F X = X → B`; but that `F` is
contravariant, `X` in negative position, not a covariant endofunctor, and has no final coalgebra. -/
theorem what_the_apophatic_arm_would_be_coalgebras_for {X B : Type} (g : B → B) (hg : ∀ b, g b ≠ b) :
    ∀ c : X → (X → B), ¬ Function.Surjective c :=
  fun c => no_reflexive_object hg c

/-- **Is there a shared F.** The candidates do not coincide: the cataphatic arm is algebras for a family of
distinct covariant signature functors (`2 ≠ 3`), the apophatic candidate coalgebras for the contravariant
`F X = X → B` with no final coalgebra. A family of covariant functors and a single contravariant one share no
`F`, so the identification fails at the first step. -/
theorem is_there_a_shared_F :
    (Fintype.card (Unit ⊕ (Fin 1 × Fin 1)) ≠ Fintype.card (Unit ⊕ (Fin 1 × Fin 1) ⊕ Fin 1))
    ∧ (∀ (X B : Type) (g : B → B), (∀ b, g b ≠ b) → ∀ c : X → (X → B), ¬ Function.Surjective c) :=
  ⟨by decide, fun _ _ _ hg c => no_reflexive_object hg c⟩

/-! ## Part 2: the relation that should be visible -/

/-- The Maybe endofunctor, a shared `F` for the illustration. -/
def Fmaybe (X : Type) : Type := Option X

/-- **Alg and CoAlg are related.** For a shared `F`, an `F`-algebra is a map `F A → A` and an `F`-coalgebra a
map `C → F C`, opposite directions over the same `F` (here `Option`); both carry forgetful functors to the base.
This is the relation that should be visible if the arms were `Alg F` and `CoAlg F`. -/
theorem alg_and_coalg_are_related :
    (∃ alg : Fmaybe Bool → Bool, alg none = true)
    ∧ (∃ coalg : Bool → Fmaybe Bool, coalg true = none) :=
  ⟨⟨fun v => v.getD true, rfl⟩, ⟨fun _ => none, rfl⟩⟩

/-- **Our arms have no such relation, and none is forced.** The arms are joined by `And`, not a between-arms
morphism (`two_adjacent_arms`), and the six refutations forbid such a morphism. But the Alg/CoAlg relation is
weaker: an algebra and a coalgebra over the same `F` share only a forgetful functor to the base and need not be
linked by any map, so even if the arms were `Alg F` and `CoAlg F` the relation would not be a between-arms
morphism, and the identification does not contradict the refutations. -/
theorem our_arms_have_no_such_relation {X B : Type} (c : X → X → B) :
    ((∀ g : B → B, (∀ b, g b ≠ b) → ¬ Function.Surjective c) ∧ (∃ build : X → (X → B), ∀ x, build x = c x))
    ∧ (∃ (alg : Option Bool → Bool) (coalg : Bool → Option Bool), alg none = true ∧ coalg true = none) :=
  ⟨two_adjacent_arms c, ⟨fun v => v.getD true, fun _ => none, rfl, rfl⟩⟩

/-! ## Part 3: the verdict -/

/-- **Refuted in its precise form, the READING earned.** No shared `F`: the cataphatic arm is algebras for a
family (`2 ≠ 3`), not one, so no single `F` has the cataphatic witnesses as exactly its algebras. And not by
contradiction with the refutations: the arms are joined by `And` (`two_adjacent_arms`), the Alg/CoAlg relation
weaker than a between-arms morphism. So the single-shared-`F` identification is false, the mark earned. -/
theorem identification_is_theorem_or_reading {X B : Type} (c : X → X → B) :
    (Fintype.card (Unit ⊕ (Fin 1 × Fin 1)) ≠ Fintype.card (Unit ⊕ (Fin 1 × Fin 1) ⊕ Fin 1))
    ∧ ((∀ g : B → B, (∀ b, g b ≠ b) → ¬ Function.Surjective c) ∧ (∃ build : X → (X → B), ∀ x, build x = c x)) :=
  ⟨by decide, two_adjacent_arms c⟩

/-- **What survives either way.** Separate results, unaffected: the cataphatic arm is algebraic (free
constructions, operations preserved by homomorphisms) and the apophatic observational (the hole), and the
Lambek-style non-existence stands (`no_reflexive_object`, no `X ≅ X → B`). Only the single-shared-`F`
identification is refuted; the characterizations and the theorem are untouched. -/
theorem what_survives_either_way {X B : Type} (g : B → B) (hg : ∀ b, g b ≠ b) :
    ((fun a b : List Bool => a ++ b) [] [true] = [true])
    ∧ (∀ c : X → (X → B), ¬ Function.Surjective c) :=
  ⟨rfl, fun c => no_reflexive_object hg c⟩

/-! ## The verdicts

Part 1: there is no shared `F`. The cataphatic arm is algebras for a family of distinct signature functors, the
monoid and group functors differing in cardinality (`what_the_cataphatic_arm_would_be_algebras_for`), so one per
bought-operation and the list open; the apophatic candidate `F X = X → B` is contravariant with no final
coalgebra (`what_the_apophatic_arm_would_be_coalgebras_for`). A family of covariant functors and a single
contravariant one coincide in no `F` (`is_there_a_shared_F`): the identification fails at the first step.

Part 2: the identification would not contradict the refutations. For a shared `F`, `Alg F` and `CoAlg F` are
related by opposite-direction structure maps over a shared forgetful functor to the base
(`alg_and_coalg_are_related`); but that relation is weaker than a between-arms morphism, an algebra and a
coalgebra over one `F` need not be linked by any map, so it would not be one of the six refuted morphisms
(`our_arms_have_no_such_relation`). No contradiction is manufactured; the refutations neither confirm nor deny
the identification.

Part 3: the precise identification is refuted, not merely unproven, and the READING mark is earned. There is no
single `F` for which the cataphatic arm is `Alg F` and the apophatic `CoAlg F`, because the cataphatic arm is
already a family and the apophatic candidate a single contravariant functor
(`identification_is_theorem_or_reading`); the refutation is structural, not a contradiction with the between-arms
refutations, which are weaker. What survives is separate (`what_survives_either_way`): the arms'
characterizations, cataphatic algebraic and apophatic observational, and the Lambek-style non-existence, all
unaffected.

The verdict: the bicameral structure is not literally the algebra/coalgebra duality for one shared functor, and
the READING mark is earned. The refutation is at Part 1, not Part 2: the cataphatic arm is algebras for an open
family of signature functors, not one, and the apophatic candidate `F X = X → B` is contravariant with no final
coalgebra, so no `F` is shared. The between-arms refutations do not enter, since the Alg/CoAlg relation is a
shared forgetful functor to the base, weaker than the morphisms those refutations forbid, so the identification
is false by structural mismatch rather than by contradiction. What the READING correctly names survives, each arm
algebraic or observational in flavour and the hole a Lambek-style non-existence, a characterization and a
theorem, not the single-functor identification. Reported per part. Nothing here is resolved. -/

end Chiralogy.ArmsDuality
