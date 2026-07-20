-- ARCHIVED (register and ground-structure graduation): trust graduated (the first non-chain bound component, a fork); membership judgement fails the gate (a single boundary-drawing).

import Chiralogy

/-! # Experiment: two group-level registers

Five registers exist; three orders are represented, and the mixed cell has two occupants. Test two group-level
candidates where members classify members: trust and membership judgement. All domain content IMPORTED, all
mappings READINGS; the protocol is not extended. The membership gate is applied first: a register needs a genuine
two-place self-classifying family, distinct elements distinct verdicts; a single judge lifts vacuously and fails.
Presupposition is tested pairwise, not sorted in advance. Stays in `Experiments/`; canonical untouched; nothing
resolved. -/

open Chiralogy

namespace Chiralogy.GroupRegisters

/-- A ground is free when isolated: comparable to no other. -/
abbrev isFree {n : ℕ} (prereq : Fin n → Fin n → Bool) (i : Fin n) : Prop :=
  ∀ j, j ≠ i → prereq i j = false ∧ prereq j i = false

/-- A representative genuine two-place family: distinct elements give distinct verdicts, and it carries the hole.
The domain families are IMPORTED; this witnesses that the two-place non-degeneracy gate is passable. -/
def genuineFam : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none

/-- The three-chain, for comparison with the type register and cognition. -/
def prereqChain3 : Fin 3 → Fin 3 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 1) && decide (b = 2))

/-! ## Candidate 1: trust -/

/-- **Trust: a family.** In multi-agent systems every agent is both trustor and trustee, each carrying a
trust-profile over the others, distinct agents distinct profiles (IMPORTED); the two-place non-degeneracy holds
and the payload fires. -/
theorem trust_family : NonDegenerate genuineFam ∧ ¬ Function.Surjective genuineFam :=
  ⟨⟨0, 1, by decide⟩, hole_uniform genuineFam⟩

/-- The trust order: identity-unknown `0` precedes both never-interacted `1` and interacted-inconclusively `2`
(identity resolution precedes interaction assessment), which are independent; deliberately-withheld `3` is free.
READING, defeasible. -/
def prereqTrust : Fin 4 → Fin 4 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 0) && decide (b = 2))

/-- The fork in isolation, the bound component of trust. -/
def prereqFork : Fin 3 → Fin 3 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 0) && decide (b = 2))

/-- **Trust grounds.** Tested pairwise: identity-unknown precedes both interaction grounds; never-interacted and
interacted-inconclusively presuppose nothing of each other; deliberately-withheld presupposes nothing. So the
bound part branches from identity rather than chaining. -/
theorem trust_grounds :
    (prereqTrust 0 1 = true ∧ prereqTrust 0 2 = true)
    ∧ (prereqTrust 1 2 = false ∧ prereqTrust 2 1 = false)
    ∧ (isFree prereqTrust 3) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide⟩

/-- **Trust components.** A free ground `3` (withheld) beside a bound component `{0,1,2}` that is a fork, not a
chain: the fork has five closeable up-sets where a chain of three has four. The closeable count is ten, five for
the fork times two for the free ground, nine permitted. -/
theorem trust_components :
    (isFree prereqTrust 3 ∧ ¬ isFree prereqTrust 0)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable prereqTrust S)).card = 10)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable prereqTrust S ∧ ¬ ∀ r, S r = true)).card = 9)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqFork S)).card = 5) :=
  ⟨⟨by decide, by decide⟩, by decide, by decide, by decide⟩

/-! ## Candidate 2: membership judgement -/

/-- **Membership: a single judge.** Who counts as one of us is a shared boundary, one verdict every member
carries, so the classification lifts vacuously, `fun _ m => authority m`, and is degenerate. A perspectival
belonging would be a family, but the characteristic membership judgement is a single boundary-drawing, so the
gate stops here. -/
theorem membership_single_judge :
    ∀ authority : Fin 2 → Option Bool, ¬ NonDegenerate (fun _ m => authority m) :=
  fun _ => fun ⟨_, _, h⟩ => h rfl

/-! ## The comparison -/

/-- **The extended register table.** Physics one ground (count two); the type register and cognition a
three-chain (four); immunology mixed at three (six) and chemistry mixed at four (eight); trust a fork bound
component plus a free ground (ten), its fork worth five where a chain of three is four. -/
theorem extended_register_table :
    ((Finset.univ.filter (fun S : Fin 1 → Bool => closeable prereqDiscrete S)).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqChain3 S)).card = 4)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable prereqTrust S)).card = 10)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqFork S)).card = 5) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **What the group registers add.** Trust adds a branching: its bound component is a fork, five closeable
up-sets against a chain's four at the same ground count, a shape not previously presented, all prior bound
components being chains. Membership judgement adds nothing, stopping at the gate. -/
theorem what_group_registers_add :
    ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqFork S)).card = 5)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqChain3 S)).card = 4)
    ∧ (5 ≠ 4) :=
  ⟨by decide, by decide, by decide⟩

/-! ## The verdicts

Trust: a family (`trust_family`); tested pairwise, identity-unknown precedes both interaction grounds while
never-interacted and interacted-inconclusively are independent and deliberately-withheld is free (`trust_grounds`);
so a free ground beside a bound component that is a fork, ten closeable and nine permitted, the fork five where a
chain of three is four (`trust_components`). Membership judgement: a single judge, a shared boundary lifting
vacuously, stopped at the gate (`membership_single_judge`).

The table (`extended_register_table`): physics one ground (two), the type register and cognition a three-chain
(four), immunology and chemistry mixed (six and eight), trust a fork-plus-free (ten). Group registers add a shape
(`what_group_registers_add`): the fork is a branching bound component, distinct from a chain by its count, five
against four.

The verdict: of two group-level candidates, one passes and adds a shape, the other stops at the gate. Trust is a
genuine self-classifying family, agents over agents, and under the reading that identity resolution precedes
interaction assessment it presents a branching, its bound component a fork rather than a chain, the first
non-chain bound component any register has shown, distinguished by having five closeable up-sets where a chain of
the same size has four. Membership judgement is a single boundary-drawing, one verdict shared, so it lifts
vacuously and is no family. So the group level does add a shape, a branching, which answers the standing question:
the domains do not present only chains and simple mixed orders. The reading of trust's order is imported and
defeasible, and nothing is claimed of trust or membership beyond the ground-structure each carries or fails to
carry. Reported per candidate. Nothing here is resolved. -/

end Chiralogy.GroupRegisters
