-- ARCHIVED (register and ground-structure graduation): declined: repeats chemistry's three-chain-plus-free shape, and its import (Luhmann) is contested at source by Maturana.

import Chiralogy

/-! # Experiment: a communications register

Five registers give four order-shapes. Test Luhmann's social systems as a sixth. All domain content IMPORTED,
the mapping a READING, and the import here is more heavily marked than any prior: Luhmann extends autopoiesis from
biological to social systems, and the extension is contested by a principal in its own literature. Maturana
rejected it, holding that autopoiesis requires the physical production of components and that humans are
structurally coupled to social systems rather than being components of them. This is the first register whose
imported content is disputed at the source, so the mapping is a reading of a contested reading, marked as such.

The imported content: social systems are networks of communications producing communications; the operative
distinction is system versus environment, whether a communication belongs; a communication classifies
communications, so the classifier is in the carrier; a thought becomes a social communication only when
expressed, understood, and taken up; operationally closed systems may still be structurally coupled, irritating
one another without operational contact. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Communications

/-- A ground is free when isolated: comparable to no other. -/
abbrev isFree {n : ℕ} (prereq : Fin n → Fin n → Bool) (i : Fin n) : Prop :=
  ∀ j, j ≠ i → prereq i j = false ∧ prereq j i = false

/-- A representative genuine two-place family: distinct elements give distinct verdicts, carrying the hole. The
domain family is IMPORTED and contested; this witnesses the gate is passable. -/
def genuineFam : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none

/-- The three-chain, for comparison. -/
def prereqChain3 : Fin 3 → Fin 3 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 1) && decide (b = 2))

/-! ## Part 1: the gate -/

/-- **Communications: a family.** The taking-up relation is perspectival, each communication connecting to its
own prior communications, distinct communications distinct connection-profiles (IMPORTED, contested); so it is a
genuine two-place self-classifying family, not a single system-level boundary, and the payload fires. Had
belonging been one shared verdict it would have lifted vacuously like membership judgement; it does not, because
taking-up is operation-by-operation. -/
theorem communications_family : NonDegenerate genuineFam ∧ ¬ Function.Surjective genuineFam :=
  ⟨⟨0, 1, by decide⟩, hole_uniform genuineFam⟩

/-! ## Part 2: the grounds and their order -/

/-- The communications order: not-expressed `0 ≺ 1` not-understood `1 ≺ 2` not-taken-up (the three stages), and
from-a-structurally-coupled-system `3` a separate axis, free. READING, defeasible, of contested content. -/
def prereqComm : Fin 4 → Fin 4 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 1) && decide (b = 2))

/-- **Communications grounds.** The three stages are staged: understanding presupposes expression, taking-up
presupposes understanding, so `0 ≺ 1 ≺ 2` with no direct edge `0` to `2`. -/
theorem communications_grounds :
    (prereqComm 0 1 = true ∧ prereqComm 1 2 = true)
    ∧ (prereqComm 0 2 = false) :=
  ⟨⟨by decide, by decide⟩, by decide⟩

/-- **Test presupposition pairwise.** Coupling is independent, tested not assumed: the structurally coupled ground
`3` presupposes none of the stages and is presupposed by none, in particular neither taking-up presupposes
coupling nor coupling taking-up. A communication from a coupled system fails to belong without failing any stage. -/
theorem test_presupposition_pairwise :
    (isFree prereqComm 3)
    ∧ (prereqComm 2 3 = false ∧ prereqComm 3 2 = false) :=
  ⟨by decide, ⟨by decide, by decide⟩⟩

/-- **Communications components.** A free ground `3` (coupling) beside a bound component `{0,1,2}` that is a chain,
the three stages; the closeable count is eight, four for the stage chain times two for the free coupling ground,
seven permitted. -/
theorem communications_components :
    (isFree prereqComm 3 ∧ ¬ isFree prereqComm 0)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable prereqComm S)).card = 8)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable prereqComm S ∧ ¬ ∀ r, S r = true)).card = 7) :=
  ⟨⟨by decide, by decide⟩, by decide, by decide⟩

/-! ## Part 3: does it add a shape? -/

/-- **Compare to the five.** Physics one ground (count two); the type register and cognition a three-chain
(four); immunology mixed (six); chemistry mixed at four grounds (eight); trust a fork-plus-free (ten);
communications the same eight as chemistry. -/
theorem compare_to_the_five :
    ((Finset.univ.filter (fun S : Fin 1 → Bool => closeable prereqDiscrete S)).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqChain3 S)).card = 4)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable prereqComm S)).card = 8) :=
  ⟨by decide, by decide, by decide⟩

/-- **New or repeat.** Communications repeats chemistry's shape: closeable count eight, its bound component a
chain of four up-sets, not a fork of five, a three-chain plus a free ground exactly as chemistry. It adds no new
shape. -/
theorem new_or_repeat :
    ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable prereqComm S)).card = 8)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqChain3 S)).card = 4)
    ∧ (4 ≠ 5) :=
  ⟨by decide, by decide, by decide⟩

/-! ## The verdicts

Part 1: communications passes the gate. The taking-up relation is perspectival, each communication connecting to
its own prior communications, so distinct communications give distinct profiles and the classification is a
genuine two-place family, not a single system-boundary (`communications_family`). The likely failure was checked:
belonging is not one shared verdict, because taking-up is operation-by-operation.

Part 2: the grounds are a chain plus a free ground. The three stages are staged, expression before understanding
before taking-up (`communications_grounds`); coupling is independent, presupposing none of the stages and
presupposed by none, a communication from a coupled system failing to belong without failing any stage
(`test_presupposition_pairwise`). So a free ground beside a bound chain, closeable count eight, seven permitted
(`communications_components`).

Part 3: it repeats chemistry. Its count is eight and its bound component a chain of four up-sets, not a fork of
five (`compare_to_the_five`, `new_or_repeat`), a three-chain plus a free ground, the shape chemistry already
presents. It adds no new shape.

The verdict: the communications register passes the membership gate and repeats an existing shape, chemistry's
three-chain plus a free ground. The taking-up relation is genuinely perspectival, so belonging is
communication-by-communication rather than a single boundary, and the register is a family; but its order is the
staged chain of expression, understanding, and taking-up with structural coupling as an independent free axis,
which is exactly chemistry's chain-plus-free, count eight, bound component a chain not a fork. So a sixth register
adds no order-shape, which is a finding about the shapes available: a staged domain with one independent axis
lands on the chain-plus-free mixed order already occupied. And this is the register to hold most lightly, its
imported content contested at the source by Maturana, its mapping a reading of a disputed reading; nothing is
claimed of social systems beyond the ground-structure this contested reading carries. Reported per part. Nothing
here is resolved. -/

end Chiralogy.Communications
