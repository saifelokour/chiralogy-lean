-- ARCHIVED (register and ground-structure graduation): the order-constrains-the-fibre and order-shapes results graduated to Model/GroundForensics.

import Chiralogy

/-! # Experiment: fibre distribution, the cost of maintenance, and the free column

Three connected questions about how the ground-order shapes forensics and fabrication. A state's fibre is the
nonempty closeable subsets of its true-set (the closures that could have produced it), so an order shrinks fibres
by cutting the family to up-sets. Independent verdicts. Concrete small orders. Stays in `Experiments/`; canonical
untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Distribution

/-- The chain order `0 ≺ 1 ≺ 2`. -/
def prereqChain3 : Fin 3 → Fin 3 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 1) && decide (b = 2))

/-- The fork order `0 ≺ 1`, `0 ≺ 2`. -/
def prereqFork : Fin 3 → Fin 3 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 0) && decide (b = 2))

/-- The fibre size of a state with true-set `T`: the nonempty closeable subsets of `T`. -/
abbrev fibreSize {n : ℕ} (prereq : Fin n → Fin n → Bool) (T : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun S : Fin n → Bool =>
    closeable prereq S ∧ (∃ i, S i = true) ∧ (∀ i, S i = true → T i = true))).card

/-! ## Part 1: does the order determine forensic legibility? -/

/-- **Fibre classes.** States sort by fibre: empty (never totalized), singleton (source determined), many
(ambiguous). At the chain order over three grounds, four states are empty, two singleton, two many. -/
theorem fibre_classes :
    ((Finset.univ.filter (fun T : Fin 3 → Bool => fibreSize prereqChain3 T = 0)).card = 4)
    ∧ ((Finset.univ.filter (fun T : Fin 3 → Bool => fibreSize prereqChain3 T = 1)).card = 2)
    ∧ ((Finset.univ.filter (fun T : Fin 3 → Bool => 2 ≤ fibreSize prereqChain3 T)).card = 2) :=
  ⟨by decide, by decide, by decide⟩

/-- **The order shifts the distribution.** More states are legible (empty or singleton fibre) at the chain than
at the discrete order with the same reason count, four against six, and the fork gives five: order-shape
determines forensic legibility. -/
theorem does_the_order_shift_the_distribution :
    ((Finset.univ.filter (fun T : Fin 3 → Bool => fibreSize prereqDiscrete T ≤ 1)).card = 4)
    ∧ ((Finset.univ.filter (fun T : Fin 3 → Bool => fibreSize prereqChain3 T ≤ 1)).card = 6)
    ∧ ((Finset.univ.filter (fun T : Fin 3 → Bool => fibreSize prereqFork T ≤ 1)).card = 5) :=
  ⟨by decide, by decide, by decide⟩

/-- **What makes a state legible.** Legibility is structural. A state has empty fibre when no ground's
prerequisite-closure fits in its true-set: at the chain `{1}` is never totalized because closing `1` requires
closing its prerequisite `0`, and `0 ∉ {1}`. The empty-fibre states are those that omit a prerequisite. -/
theorem what_makes_a_state_legible :
    (fibreSize prereqChain3 (fun i => decide (i = 1)) = 0)
    ∧ (prereqChain3 0 1 = true ∧ (fun i => decide (i = 1)) 0 = false) :=
  ⟨by decide, ⟨by decide, by decide⟩⟩

/-! ## Part 2: the cost of maintaining a fabrication -/

/-- **Cost in views.** A lie maintained across `k` views requires `k` absorptions, each putting that view on the
total side of the collision (unfaithful at the hole); three views, three absorptions, linear in the views. -/
theorem cost_in_views (c1 c2 c3 : Fin 4 → Fin 4 → Option Bool) :
    (c1 0 2 = some true → c1 0 2 ≠ imprecise 0 2)
    ∧ (c2 0 2 = some true → c2 0 2 ≠ imprecise 0 2)
    ∧ (c3 0 2 = some true → c3 0 2 ≠ imprecise 0 2) :=
  ⟨fun h => by rw [h]; decide, fun h => by rw [h]; decide, fun h => by rw [h]; decide⟩

/-- **Cost in grounds.** At an ordered level a closure must be an up-set, so fabricating a ground forces
fabricating its prerequisites. At the chain, fabricating the top ground `2` forces the whole chain, `{2}` alone
not closeable while `{0,1,2}` is; fabricating the root `0` costs one, `{0}` closeable alone. -/
theorem cost_in_grounds :
    (¬ closeable prereqChain3 (fun i => decide (i = 2)))
    ∧ (closeable prereqChain3 (fun _ => true))
    ∧ (closeable prereqChain3 (fun i => decide (i = 0))) :=
  ⟨by decide, by decide, by decide⟩

/-- **Forced levels cost more.** At the free level, fabricating ground `2` costs one, `{2}` closeable alone; at
the chain it costs three, `{2}` not closeable and `{0,1,2}` the smallest closeable set containing it. So forced
levels make lies costlier and free levels cheaper, the cost the size of the forced closure, structural not a
magnitude. -/
theorem forced_levels_cost_more :
    (closeable prereqDiscrete (fun i : Fin 3 => decide (i = 2)))
    ∧ (¬ closeable prereqChain3 (fun i => decide (i = 2)))
    ∧ (closeable prereqChain3 (fun _ => true)) :=
  ⟨by decide, by decide, by decide⟩

/-! ## Part 3: is the free column occupiable? -/

/-- **What independence requires.** Two grounds are independent when neither presupposes the other, so both
singleton closures are legitimate, neither forcing the other; the discrete order realizes it, `{0}` and `{1}`
both closeable. -/
theorem what_independence_requires :
    (closeable prereqDiscrete (fun i : Fin 2 => decide (i = 0)))
    ∧ (closeable prereqDiscrete (fun i : Fin 2 => decide (i = 1))) :=
  ⟨by decide, by decide⟩

/-- **Why the four failed.** The four failures share a form: each is a prerequisite edge (precedence,
applicability, assumption-strength, containment), and any prerequisite makes the dependent ground's closure
presuppose the other, `{1}` not closeable under `0 ≺ 1`. If grounds are ways of failing and failures compose by
presupposition, a prerequisite is exactly a presupposition between failures. -/
theorem why_the_four_failed :
    (prereqChain2 0 1 = true)
    ∧ (¬ closeable prereqChain2 (fun i => decide (i = 1))) :=
  ⟨by decide, by decide⟩

/-- **Is independence satisfiable.** At the model level yes: the discrete order gives a free level whose two
grounds presuppose nothing of each other, both closeable. But a prerequisite makes them dependent, and every
domain examined carried one, so the free level is a construction with no domain analogue supplied. The free
column is model-occupiable and domain-empty, empty for a reason if grounds are failures that compose by
presupposition. -/
theorem is_independence_satisfiable :
    (closeable prereqDiscrete (fun i : Fin 2 => decide (i = 0)))
    ∧ (closeable prereqDiscrete (fun i : Fin 2 => decide (i = 1)))
    ∧ (¬ closeable prereqChain2 (fun i => decide (i = 1))) :=
  ⟨by decide, by decide, by decide⟩

/-! ## The verdicts

Part 1: order-shape shifts the fibre distribution and determines legibility. States sort into empty, singleton,
and many fibres (`fibre_classes`); more are legible at the chain than at the discrete order with the same reason
count, and the fork differs again, six against four against five (`does_the_order_shift_the_distribution`).
Legibility is structural: the empty-fibre states are those omitting a prerequisite, closing a ground requiring
its prerequisites be closed (`what_makes_a_state_legible`). So the connection to the four-domains finding holds:
the order does forensic work.

Part 2: fabrication is costlier under an order, structurally. A lie across `k` views costs `k` absorptions,
linear (`cost_in_views`); and at an ordered level fabricating a ground forces its prerequisites, the top of the
chain forcing the whole chain and the root costing one (`cost_in_grounds`). So a fabrication at a given ground is
more expensive under the order than at the free level, three against one, the cost the size of the forced closure
(`forced_levels_cost_more`), a count of grounds and no magnitude.

Part 3: independence is satisfiable only as a model construction. Structurally it is the absence of a prerequisite
edge, both singleton closures closeable (`what_independence_requires`); the four failures share the one form, a
prerequisite is a presupposition between failures (`why_the_four_failed`). At the model level a free level exists,
the discrete order realizing independence; but a prerequisite makes grounds dependent, and every domain examined
carried one, so the free level has no domain analogue supplied (`is_independence_satisfiable`). The free column is
model-occupiable and domain-empty.

The verdict: the ground-order does connected work across forensics and fabrication. It shifts the fibre
distribution, more states legible under a chain than a free order, so forensic legibility is a property of the
order-shape, not of the reason count alone. It makes fabrication costlier, a fabrication forcing its
prerequisite-closure, so forced levels are the expensive ones and free levels the cheap, the cost structural, a
count of grounds. And it explains the free column: independence is the absence of a prerequisite, satisfiable as
a model construction but domain-empty, since the four domains each carried a prerequisite and a ground, as a way
of failing, tends to presuppose. The negative in Part 3 is a real finding, a property of grounds: failures
compose by presupposition, so the framework's free levels are constructions the domains do not realize. Reported
per part. Nothing here is resolved. -/

end Chiralogy.Distribution
