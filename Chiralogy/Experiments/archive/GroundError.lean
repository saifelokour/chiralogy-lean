import Chiralogy

/-! ARCHIVED (SPENT): the graduatable universal results of this investigation already reached
canonical in prior sessions, so nothing graduated in the graduate-now wave. Mapping:
  is_it_distinct_from_over_under -> Model/Boundary (the all-none map asserts no falsehood, already a conjunct there).
Remaining content is fixed-size witnesses and (where present) fragility/scale coordinates, kept as
the investigation record. Namespaced under Chiralogy.GroundError, it typechecks standalone against canonical. -/

/-! # Experiment: is there a wrong-ground error?

Over- and under-classification are generic: any binary codomain has two error directions, and both need a target
(8.1, IMPORTED). Test whether the ground-structure contributes an error notion of its own, a wrong-ground error,
attributing an absence to ground `a` when the ground was `b`. Missing-data theory names this: MNAR and MAR cannot
be distinguished empirically, the mechanism-attribution generally untestable, whole sensitivity frameworks built
for it. Domain content IMPORTED. A ground-attribution is modelled as the principal closeable closure of a ground,
comparability defined internally through `closeable` with no target. Compute across the registers before judging.
Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.GroundError

/-- Ground `a` forces ground `b` (`b ≤ a`, `a` below `b` in the order) when every closeable set closing `b` also
closes `a`. Internal to the order, no target. -/
abbrev forces {n : ℕ} (prereq : Fin n → Fin n → Bool) (a b : Fin n) : Prop :=
  ∀ S : Fin n → Bool, closeable prereq S → S b = true → S a = true

/-- Two grounds are comparable when one forces the other. -/
abbrev comparable {n : ℕ} (prereq : Fin n → Fin n → Bool) (a b : Fin n) : Prop :=
  forces prereq a b ∨ forces prereq b a

/-- `S` is the principal closure of ground `a`: the least closeable set closing `a`. -/
abbrev isPrincipalClosure {n : ℕ} (prereq : Fin n → Fin n → Bool) (a : Fin n) (S : Fin n → Bool) : Prop :=
  closeable prereq S ∧ S a = true
    ∧ ∀ T : Fin n → Bool, closeable prereq T → T a = true → ∀ r, S r = true → T r = true

/-- Two ground-attributions are nested when one closure is contained in the other. -/
abbrev nested {n : ℕ} (S T : Fin n → Bool) : Prop :=
  (∀ r, S r = true → T r = true) ∨ (∀ r, T r = true → S r = true)

/-- A closure registers an absence when it closes some ground. -/
abbrev hasClosed {n : ℕ} (S : Fin n → Bool) : Prop := ∃ r, S r = true

/-- The principal closures used below. -/
abbrev chainClsr1 : Fin 3 → Bool := fun r => decide (r = 0 ∨ r = 1)
abbrev chainClsr2 : Fin 3 → Bool := fun _ => true
abbrev vClsr1 : Fin 3 → Bool := fun r => decide (r = 0 ∨ r = 1)
abbrev vClsr2 : Fin 3 → Bool := fun r => decide (r = 0 ∨ r = 2)
abbrev mixedClsr0 : Fin 3 → Bool := fun r => decide (r = 0)
abbrev mixedClsr1 : Fin 3 → Bool := fun r => decide (r = 0 ∨ r = 1)
abbrev mixedClsr2 : Fin 3 → Bool := fun r => decide (r = 2)

/-- **The closures are the principal closures.** Each exhibited set is the least closeable set closing its ground,
so the ground-attributions below are the genuine closures, not stipulated. -/
theorem closures_are_principal :
    isPrincipalClosure prereqChain3 1 chainClsr1 ∧ isPrincipalClosure prereqChain3 2 chainClsr2
    ∧ isPrincipalClosure prereqV3 1 vClsr1 ∧ isPrincipalClosure prereqV3 2 vClsr2
    ∧ isPrincipalClosure prereqMixed3 0 mixedClsr0 ∧ isPrincipalClosure prereqMixed3 1 mixedClsr1
    ∧ isPrincipalClosure prereqMixed3 2 mixedClsr2 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Part 1: is it statable -/

/-- **Wrong-ground is statable, internally.** Attributing an absence to ground `1` closes its principal closure,
to ground `2` another; the two closures differ yet both register an absence, so a ground is closed either way. The
attribution is a choice of ground in the order and its closure, and the ground it was against, `2`, is itself a
position in the order, not an external truth-target: the notion is stated with the order alone, unlike over/under
which needs a target. -/
theorem wrong_ground :
    (chainClsr1 ≠ chainClsr2)
    ∧ (hasClosed chainClsr1 ∧ hasClosed chainClsr2)
    ∧ (isPrincipalClosure prereqChain3 1 chainClsr1 ∧ isPrincipalClosure prereqChain3 2 chainClsr2) :=
  ⟨by decide, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, by decide, by decide⟩

/-- **Invisible to over/under.** Both ground-attributions leave the position an absence, and an absence asserts no
falsehood against any target; over/under sees only present verdicts against a target, so it returns the same null
verdict under either ground. The two attributions are over/under-identical, so wrong-ground is not one in
disguise: if it is an error it is at the ground level, below the verdict. -/
theorem is_it_distinct_from_over_under {X : Type} (t : X → X → Bool) (x y : X) :
    ¬ assertsFalse (fun _ _ => none : X → X → Option Bool) t x y := by
  simp [assertsFalse]

/-! ## Part 2: does the order matter -/

/-- **The order sorts the error.** At the chain, comparable grounds give nested closures, a one-sided error; at
the fork, the incomparable grounds give closures neither nested, a two-sided error; at the mixed order both occur,
the bound pair nested and the pair across the free ground crossed. Mistaking a ground for its prerequisite differs
from mistaking two incomparable grounds. -/
theorem error_along_the_order :
    (nested chainClsr1 chainClsr2)
    ∧ (¬ nested vClsr1 vClsr2)
    ∧ (nested mixedClsr0 mixedClsr1)
    ∧ (¬ nested mixedClsr1 mixedClsr2) := by decide

/-- **Closure propagates the error, directionally.** The closure of the consequent strictly contains the closure
of its prerequisite, so attributing to the consequent when the prerequisite was in force over-closes, spuriously
forcing the extra ground, while the reverse under-closes, missing it. Mistaking a prerequisite for its consequent
differs from the reverse: one adds ground `2`, the other drops it. This is an over/under at the ground level,
directional because the down-sets nest. -/
theorem does_closure_propagate_the_error :
    ((∀ r, chainClsr1 r = true → chainClsr2 r = true) ∧ (∃ r, chainClsr2 r = true ∧ chainClsr1 r = false))
    ∧ (chainClsr1 2 = false ∧ chainClsr2 2 = true) := by decide

/-- **A free ground gives the sharpest error.** A free ground has no prerequisites, so its closure is its
singleton, disjoint from any bound component's closure; the wrong-ground error involving it is two-sided and
total, spuriously forcing the free ground while missing the whole bound component, with no propagation. Within a
bound component the closures nest and the error is one-sided; across a free ground they are disjoint and the error
is two-sided. -/
theorem free_grounds_and_error :
    (isFree prereqMixed3 2)
    ∧ (mixedClsr2 2 = true ∧ mixedClsr2 0 = false ∧ mixedClsr2 1 = false)
    ∧ (¬ ∃ r, mixedClsr1 r = true ∧ mixedClsr2 r = true)
    ∧ (¬ nested mixedClsr1 mixedClsr2) := by decide

/-! ## Part 3: across the registers -/

/-- **The error-shapes track the order.** Counting the ordered incomparable pairs, the two-sided errors: physics
none, being a single ground with no pair; the chain none, every pair comparable, all errors one-sided; the fork
one unordered pair (two ordered); the mixed order two; chemistry, a three-chain with a free ground, three; trust,
a fork with a free ground, four. The number and kind of possible wrong-ground errors track the order-shape, chains
contributing only one-sided errors, forks and free grounds contributing two-sided. -/
theorem error_shapes_per_register :
    ((Finset.univ.filter (fun p : Fin 1 × Fin 1 => p.1 ≠ p.2 ∧ ¬ comparable prereqDiscrete p.1 p.2)).card = 0)
    ∧ ((Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 ≠ p.2 ∧ ¬ comparable prereqChain3 p.1 p.2)).card = 0)
    ∧ ((Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 ≠ p.2 ∧ ¬ comparable prereqV3 p.1 p.2)).card = 2)
    ∧ ((Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 ≠ p.2 ∧ ¬ comparable prereqMixed3 p.1 p.2)).card = 4)
    ∧ ((Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 ≠ p.2 ∧ ¬ comparable prereqChemistry p.1 p.2)).card = 6)
    ∧ ((Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 ≠ p.2 ∧ ¬ comparable prereqTrust p.1 p.2)).card = 8) := by
  decide

/-- **The state does not record the ground.** The grounded position is an absence, none under either attribution,
and any marking leaves an absence an absence, so no marking recovers the ground; the two ground-explanations
differ as closures yet the verdict and its marking coincide. Wrong-ground is undetectable from the state, a second
undetectable alongside totalization: the state records the value, not the ground of an absence. -/
theorem is_it_detectable (w : Fin 3 → Fin 3 → Bool) :
    (partialization w (fun _ _ => none) 0 1 = none)
    ∧ (chainClsr1 ≠ chainClsr2) := by
  refine ⟨?_, by decide⟩
  unfold partialization; split <;> rfl

/-! ## Part 4: the verdict -/

/-- **The ground-structure contributes a third error, internal.** At comparable grounds the error is one-sided,
nested closures, an over/under at the ground level, so it collapses into the generic two-ness there; at
incomparable grounds it is two-sided, neither nested, neither over nor under, irreducible. And the shape is fixed
by the order prior to any target: against any target the grounded position asserts no falsehood, yet comparability
already sorts the grounds. So wrong-ground is a genuine third notion, internal, structured by the order, reducing
to over/under only where the grounds are comparable. -/
theorem does_the_ground_structure_contribute_an_error (t : Fin 3 → Fin 3 → Bool) :
    (comparable prereqChain3 1 2 ∧ nested chainClsr1 chainClsr2)
    ∧ (¬ comparable prereqV3 1 2 ∧ ¬ nested vClsr1 vClsr2)
    ∧ (¬ assertsFalse (fun _ _ => none : Fin 3 → Fin 3 → Option Bool) t 1 2) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_⟩
  simp [assertsFalse]

/-! ## The verdicts

Part 1: wrong-ground is statable, and internal. Attributing an absence to one ground closes its principal closure,
to another closes a different one, both registering an absence, the notion stated with the order alone and the
ground it was against a position in the order, not a target (`wrong_ground`, `closures_are_principal`). And it is
invisible to over/under: both attributions leave the position an absence, which asserts no falsehood against any
target, so the verdict-level notion gives the same null verdict either way (`is_it_distinct_from_over_under`). If
it is an error, it lives below the verdict.

Part 2: the order sorts it. Comparable grounds give nested closures, a one-sided error, incomparable grounds
crossed closures, a two-sided error, at chain, fork, and mixed order alike (`error_along_the_order`); closing the
wrong ground along the order propagates through the prerequisites and is directional, mistaking a prerequisite for
its consequent over-closing and the reverse under-closing (`does_closure_propagate_the_error`); and a free ground
gives the sharpest error, its singleton closure disjoint from any bound component, two-sided and total
(`free_grounds_and_error`).

Part 3: the shapes track the order and the error is undetectable. Physics has no wrong-ground error, being one
ground; chains contribute only one-sided errors; forks and free grounds contribute two-sided, the count rising
across the six (`error_shapes_per_register`). But the state does not record the ground: the position is an absence
whatever the attribution, and no marking recovers it (`is_it_detectable`), a second undetectable alongside
totalization.

Part 4: the ground-structure contributes a third error, internal. At comparable grounds it is one-sided, an
over/under at the ground level, collapsing into the generic two-ness; at incomparable grounds it is two-sided,
neither over nor under, irreducible; and the shape is fixed by the order prior to any target
(`does_the_ground_structure_contribute_an_error`).

The verdict: there is a wrong-ground error, and it is the first error notion the framework supplies rather than
borrows. Over/under needs a target and sees only present verdicts, so it is blind to a wrong-ground attribution,
which keeps the verdict an absence; wrong-ground lives at the ground level, below over/under. It is internal: the
correct ground is a position in the order, not an external truth, and the shape of the error is fixed by
comparability alone, no target entering. The order structures it, into a one-sided error at comparable grounds,
which does reduce to an over/under of closures, and a two-sided error at incomparable grounds, which does not,
being over on one ground and under on the other at once, irreducible to the generic two-ness; a free ground gives
the sharpest, its closure disjoint. So it does not collapse into the second in disguise: it collapses only where
the grounds are comparable, and elsewhere it is genuinely third. Physics, one ground, has none, so the notion is
empty exactly where the order is trivial, as it should be. But it is undetectable from the state, like
totalization, the ground of an absence not recorded in the verdict; the framework supplies the error notion yet
cannot read it off a state, matching missing-data theory, where the mechanism is real, consequential, and
generally untestable. The missing-data reading is imported; the ground-level structure is the framework's own.
Reported per part. Nothing here is resolved. -/

end Chiralogy.GroundError
