-- ARCHIVED (register and ground-structure graduation): the components decomposition (bound/free split factors the family, count, and cost) graduated to Model/Grounds.

import Chiralogy

/-! # Experiment: does a ground-order decompose into bound and free parts?

`Distribution` found free grounds cheap to fabricate at and forensically illegible, the free column domain-empty.
Test whether a ground-order splits canonically into constrained and free parts, and whether the split does
structural work. Every poset is the disjoint union of the connected components of its comparability graph; a free
ground is an isolated point. The bound/free split is the components decomposition with singletons separated,
coarser than the canonical one. Concrete small orders; the existing `closeable`. Stays in `Experiments/`;
canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Components

/-- A ground is free when it is isolated: comparable to no other ground. -/
abbrev isFree {n : ℕ} (prereq : Fin n → Fin n → Bool) (i : Fin n) : Prop :=
  ∀ j, j ≠ i → prereq i j = false ∧ prereq j i = false

/-- A chain `0 ≺ 1` plus an isolated point `2`. -/
def prereqMixed : Fin 3 → Fin 3 → Bool := fun a b => decide (a = 0) && decide (b = 1)

/-- Two disjoint chains `0 ≺ 1`, `2 ≺ 3`. -/
def prereqTwoChain : Fin 4 → Fin 4 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 2) && decide (b = 3))

/-! ## Part 1: is the split well-defined? -/

/-- **Components of a ground-order.** At the mixed order `2` is a free (isolated) ground and `0` is bound; at the
two-chain no ground is free, the two chains being two bound components. -/
theorem components_of_a_ground_order :
    (isFree prereqMixed 2 ∧ ¬ isFree prereqMixed 0)
    ∧ (∀ i : Fin 4, ¬ isFree prereqTwoChain i) :=
  ⟨⟨by decide, by decide⟩, by decide⟩

/-- **The free part is the isolated points.** The free part is the union of singleton components, the bound part
the rest. This is coarser than the components decomposition: at the two-chain the free part is empty though there
are two components, so `0` and `2` are both bound yet in different components. What is lost is the distinction
between separate bound components; nothing within a component. -/
theorem free_part_is_the_isolated_points :
    (∀ i : Fin 4, ¬ isFree prereqTwoChain i)
    ∧ (isFree prereqMixed 2)
    ∧ (¬ isFree prereqTwoChain 0 ∧ ¬ isFree prereqTwoChain 2) :=
  ⟨by decide, by decide, ⟨by decide, by decide⟩⟩

/-- **The split is unique.** The free part is a determinate function of the order: at the mixed order it is
exactly `{2}`, at the two-chain empty, each ground free or bound with no choice. -/
theorem is_the_split_unique :
    (∀ i : Fin 3, isFree prereqMixed i ↔ i = 2)
    ∧ (∀ i : Fin 4, isFree prereqTwoChain i ↔ False) :=
  ⟨by decide, by decide⟩

/-! ## Part 2: does the split do work? -/

/-- **The closeable sets factor.** At the mixed order `closeable S` is exactly the bound part's up-closure
condition, `S 1 → S 0`, with the free ground `2` unconstrained; up-closure is componentwise, so a closeable set is
determined by its restriction to each component, and the free part contributes freely, both values of `S 2`
legitimate. -/
theorem closeable_sets_factor :
    ∀ S : Fin 3 → Bool, closeable prereqMixed S ↔ (S 1 = true → S 0 = true) := by decide

/-- **The permitted count factors.** The mixed order's closeable count is six, the product of its components'
counts, three for the chain `{0,1}` and two for the free point `{2}`; the permitted count is that product minus
one, five, the full closure the single prohibited move. `Grounds` computes it from the whole order; the
factorization over components is new. -/
theorem permitted_count_factors :
    ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqMixed S)).card = 6)
    ∧ ((Finset.univ.filter (fun S : Fin 2 → Bool => closeable prereqChain2 S)).card = 3)
    ∧ ((Finset.univ.filter (fun S : Fin 1 → Bool => closeable prereqDiscrete S)).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqMixed S ∧ ¬ ∀ r, S r = true)).card = 5) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **Fabrication cost by part.** The split partitions fabrications into cheap and expensive. In the free part a
fabrication costs one, the isolated ground `2` closeable alone; in the bound part it costs its closure, ground
`1` not closeable alone but forcing its prerequisite `0`, `{0,1}` the closure. -/
theorem fabrication_cost_by_part :
    (closeable prereqMixed (fun i => decide (i = 2)))
    ∧ (¬ closeable prereqMixed (fun i => decide (i = 1)))
    ∧ (closeable prereqMixed (fun i => decide (i = 0 ∨ i = 1))) :=
  ⟨by decide, by decide, by decide⟩

/-! ## Part 3: the reading -/

/-- **What the free part is.** Where closure is unconstrained, fabrication cheapest, and legibility lowest, in
the framework's terms. Every subset of the free part is closeable (both values of the free ground legitimate), so
its fabrications cost one; the bound part restricts, ground `1` not closeable alone where the free ground `2` is.
The free part is the component of the order that imposes no prerequisite, and that is what it does, not a latitude
or a movement or an agency. -/
theorem what_the_free_part_is :
    (closeable prereqMixed (fun _ => false) ∧ closeable prereqMixed (fun i => decide (i = 2)))
    ∧ (closeable prereqMixed (fun i => decide (i = 2)))
    ∧ (¬ closeable prereqMixed (fun i => decide (i = 1))) :=
  ⟨⟨by decide, by decide⟩, by decide, by decide⟩

/-! ## The verdicts

Part 1: the split is canonical and unique, and coarser than the components decomposition. A ground-order has
connected components, a mixed order a chain plus an isolated point (`components_of_a_ground_order`); the free part
is the union of singleton components (`free_part_is_the_isolated_points`), determinate, the mixed order's free
part exactly `{2}` and the two-chain's empty (`is_the_split_unique`). It is coarser: the two-chain's two
components are lumped as one bound part, losing the distinction between them, nothing within a component.

Part 2: the split does structural work, not bookkeeping. The closeable family factors, a closeable set determined
by its restriction to each component, the free part contributing freely (`closeable_sets_factor`); the permitted
count factors as a product over components minus the top, six as three times two, permitted five
(`permitted_count_factors`); and the fabrication cost splits, one in the free part and the closure-size in the
bound (`fabrication_cost_by_part`). So the split partitions the family, the count, and the cost.

Part 3: the free part is where closure is unconstrained, fabrication cheapest, legibility lowest
(`what_the_free_part_is`). It is the component that imposes no prerequisite, both values of its grounds closeable,
its fabrications costing one. Named as what it does, not what it resembles.

The verdict: a ground-order decomposes canonically into bound and free parts, and the split does structural work.
It is the components decomposition with singletons separated, unique and determinate, coarser than the full
components decomposition and losing only the distinction between separate bound components. And it factors the
structure: the closeable family is componentwise, the permitted count a product over components minus the top,
and the fabrication cost one in the free part and the prerequisite-closure in the bound. So the free part is not
bookkeeping but a component of the order, the part that imposes no prerequisite, where closure is unconstrained,
fabrication cheapest at one, and legibility lowest. It does that and no more; the agent-readings refuted before
do not return here, this being a part of an order named by what it does. Reported per part. Nothing here is
resolved. -/

end Chiralogy.Components
