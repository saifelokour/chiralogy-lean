import Chiralogy

/-! # Experiment: the taxonomy of ethical structures

Archived: superseded by `Model/Grounds.lean`, which derives the same enumeration and its ethical content from
the closure notion and organizes it by refinement and the free-ground axis.

A structure is fixed by a reason count and a prerequisite order; the readable moves are the up-sets, the
permitted ones the up-sets minus the top. Enumerate the small structures, state what a domain must have to
occupy each, and identify which are occupied.

A closure is `c : Fin n → Bool`; an order is a prerequisite relation and its readable closures are those
respecting it (closing a ground presupposes closing its prerequisites). The counts and complement behaviour are
THEOREMS; occupancy by a domain is a READING with a defeasible mapping. Stays in `Experiments/`; canonical
untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Taxonomy

/-! ## Part 1: enumerate the small structures

The coherence predicates give the readable closures of each order. For each: the permitted count (up-sets minus
the top), whether Boolean (all subsets readable) or properly Heyting, and how many readable closures have a
readable complement. -/

/-- n = 2, the two-chain: closing reason 1 presupposes closing reason 0. -/
abbrev coh2Chain (c : Fin 2 → Bool) : Prop := c 1 = true → c 0 = true

/-- n = 3, the three-chain. -/
abbrev coh3Chain (c : Fin 3 → Bool) : Prop := (c 2 = true → c 1 = true) ∧ (c 1 = true → c 0 = true)

/-- n = 3, the V (one ground below two): 0 is prerequisite of both 1 and 2. -/
abbrev coh3V (c : Fin 3 → Bool) : Prop := (c 1 = true → c 0 = true) ∧ (c 2 = true → c 0 = true)

/-- n = 3, the Λ (two grounds below one): 2 presupposes both 0 and 1. -/
abbrev coh3Lambda (c : Fin 3 → Bool) : Prop := (c 2 = true → c 0 = true) ∧ (c 2 = true → c 1 = true)

/-- n = 3, the mixed order (a two-chain 0 ≺ 1 and a free point 2). -/
abbrev coh3Mixed (c : Fin 3 → Bool) : Prop := c 1 = true → c 0 = true

/-- **n = 1: the only order.** One permitted move, one prohibition; Boolean, both readable closures
complemented. Binary. -/
theorem n1_only_order :
    (Finset.univ.filter (fun c : Fin 1 → Bool => ¬ ∀ r, c r = true)).card = 1
    ∧ Fintype.card (Fin 1 → Bool) = 2 :=
  ⟨by decide, by decide⟩

/-- **n = 2.** Discrete (free): three permitted, Boolean, all four complemented. The two-chain (forced): two
permitted, properly Heyting (three readable), only two complemented. -/
theorem structures_n2 :
    ((Finset.univ.filter (fun c : Fin 2 → Bool => ¬ ∀ r, c r = true)).card = 3
        ∧ Fintype.card (Fin 2 → Bool) = 4)
    ∧ ((Finset.univ.filter (fun c : Fin 2 → Bool => coh2Chain c ∧ ¬ ∀ r, c r = true)).card = 2
        ∧ (Finset.univ.filter (fun c : Fin 2 → Bool => coh2Chain c)).card = 3
        ∧ (Finset.univ.filter (fun c : Fin 2 → Bool => coh2Chain c ∧ coh2Chain (fun r => !c r))).card = 2) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

/-- **n = 3.** Five orders up to isomorphism, each as (permitted, complemented): discrete (7, 8 = Boolean),
three-chain (3, 2), V one-below-two (4, 2), Λ two-below-one (4, 2), mixed chain-plus-free-point (5, 4). The
branchings match the chain in complement behaviour; the mixed order, with one free ground, complements more. -/
theorem structures_n3 :
    ((Finset.univ.filter (fun c : Fin 3 → Bool => ¬ ∀ r, c r = true)).card = 7
        ∧ Fintype.card (Fin 3 → Bool) = 8)
    ∧ ((Finset.univ.filter (fun c : Fin 3 → Bool => coh3Chain c ∧ ¬ ∀ r, c r = true)).card = 3
        ∧ (Finset.univ.filter (fun c : Fin 3 → Bool => coh3Chain c ∧ coh3Chain (fun r => !c r))).card = 2)
    ∧ ((Finset.univ.filter (fun c : Fin 3 → Bool => coh3V c ∧ ¬ ∀ r, c r = true)).card = 4
        ∧ (Finset.univ.filter (fun c : Fin 3 → Bool => coh3V c ∧ coh3V (fun r => !c r))).card = 2)
    ∧ ((Finset.univ.filter (fun c : Fin 3 → Bool => coh3Lambda c ∧ ¬ ∀ r, c r = true)).card = 4
        ∧ (Finset.univ.filter (fun c : Fin 3 → Bool => coh3Lambda c ∧ coh3Lambda (fun r => !c r))).card = 2)
    ∧ ((Finset.univ.filter (fun c : Fin 3 → Bool => coh3Mixed c ∧ ¬ ∀ r, c r = true)).card = 5
        ∧ (Finset.univ.filter (fun c : Fin 3 → Bool => coh3Mixed c ∧ coh3Mixed (fun r => !c r))).card = 4) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
   ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **Complement failure by order.** The count of complemented positions is the axis forcing moves along: 8 in
the discrete case (Boolean, every position complemented), 4 in the mixed order (one free ground), 2 in the fully
forced chain. Complementation tracks how free the order is. -/
theorem complement_failure_by_order :
    (Finset.univ.filter (fun c : Fin 3 → Bool => coh3Mixed c ∧ coh3Mixed (fun r => !c r))).card = 4
    ∧ (Finset.univ.filter (fun c : Fin 3 → Bool => coh3Chain c ∧ coh3Chain (fun r => !c r))).card = 2
    ∧ Fintype.card (Fin 3 → Bool) = 8 :=
  ⟨by decide, by decide, by decide⟩

/-! ## Part 2: occupancy conditions (READINGS)

A cell is occupied only if a domain has `n` genuinely distinguishable grounds whose prerequisites match the
order, the readable positions passing the dispute test. All occupancy claims are readings, defeasible. -/

/-- **Occupied cells** (READING, defeasible). Physics occupies n = 1 (one ground, the constitutive none). A type
system occupies the three-chain (well-formedness ≺ inference ≺ termination). These are the known instances;
stated as readings, not asserted. -/
def occupied_cells : Prop :=
  (Finset.univ.filter (fun c : Fin 1 → Bool => ¬ ∀ r, c r = true)).card = 1
    ∧ (Finset.univ.filter (fun c : Fin 3 → Bool => coh3Chain c ∧ ¬ ∀ r, c r = true)).card = 3

/-- **Unoccupied cells** (READING, defeasible). No known domain occupies the n = 2 discrete cell (two
independent grounds, three permitted, Boolean) or the n = 3 branchings (a ground prerequisite to two others, or
two prerequisite to one). To occupy them a domain would need exactly that prerequisite shape with grounds that
pass the dispute test; none is claimed. -/
def unoccupied_cells : Prop :=
  (Finset.univ.filter (fun c : Fin 2 → Bool => ¬ ∀ r, c r = true)).card = 3
    ∧ (Finset.univ.filter (fun c : Fin 3 → Bool => coh3V c ∧ ¬ ∀ r, c r = true)).card = 4
    ∧ (Finset.univ.filter (fun c : Fin 3 → Bool => coh3Lambda c ∧ ¬ ∀ r, c r = true)).card = 4

/-! ## Part 3: is the free case occupied? (READING) -/

/-- **Is the discrete case occupied** (READING, defeasible). The free Boolean structures (n independent grounds,
`2 ^ n - 1` permitted, every position complemented) are realized by the tower's own constructed levels: Except
carries two independent throws with no prerequisite between them. But no domain register clearly occupies them:
every domain that reads is unary (physics) or forced (type systems), and the strongest free-looking candidate,
database null-kinds, shows a plausible lurking prerequisite (applicable-but-absent presupposes applicability),
as type systems did in the survey. So the free case appears realized in the model layer, not by a domain;
domains that read tend to be forced. A finding about where domains sit, not about the framework. Stated, not
asserted. -/
def is_the_discrete_case_occupied : Prop :=
  (Finset.univ.filter (fun c : Fin 2 → Bool => ¬ ∀ r, c r = true)).card = 3
    ∧ Fintype.card (Fin 2 → Bool) = 4

/-! ## The verdict

Part 1: the structures at n ≤ 3. n = 1 has one order, binary. n = 2 has the discrete (three permitted, Boolean,
four complemented) and the two-chain (two permitted, Heyting, two complemented). n = 3 has five orders: discrete
(7, Boolean, 8 complemented), three-chain (3, 2), V (4, 2), Λ (4, 2), mixed (5, 4). The complemented count is
the axis (`complement_failure_by_order`): 8 free, 4 one-free-ground, 2 fully forced. Meet and join preserve
readability throughout; complement does not, and its failure is graded by the order.

Part 2: physics occupies n = 1 and a type system the three-chain (`occupied_cells`); the n = 2 discrete cell and
the n = 3 branchings have no known domain (`unoccupied_cells`). The branchings would need a ground prerequisite
to two others, or two to one, grounds passing the dispute test; none is claimed, and an unoccupied cell is a
result, not a gap to fill.

Part 3: the discrete case is not clearly occupied by any domain (`is_the_discrete_case_occupied`). The free
Boolean structures are realized by the tower's constructed levels (Except's two independent throws), but every
readable domain examined is unary or forced, and the strongest free candidate, database null-kinds, shows a
plausible lurking prerequisite, the same trap type systems sprang. So the free structures appear to live in the
model layer, not in domains; the readable domains are forced. All occupancy claims are READINGS, defeasible.
Nothing here is resolved. -/

end Chiralogy.Taxonomy
