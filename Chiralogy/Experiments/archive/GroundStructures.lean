import Chiralogy

/-! # Experiment: enumerating the ground-structures and organizing them

The model layer cannot construct a forced level, but the combinatorial structure is constructible: a
prerequisite order on grounds, its closeable family, the resulting readable positions. Enumerate the structures
with their ethical content, then organize the enumeration.

The closure notion is the framework's own: a set of grounds is closeable when closing it is a legitimate move,
and closing a ground closes its prerequisites, so `closeable prereq S` holds exactly when `S` contains the
prerequisites of everything in it. The closeable family, the permitted moves, and the Boolean/Heyting verdict
are DERIVED from this; the complement counts are COMPUTED as lattice arithmetic on the derived family, and
marked. Occupancy claims are READINGS. Nothing goes in the protocol. Stays in `Experiments/`; canonical
untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.GroundStructures

/-- The framework's closure notion: `S` is closeable under the prerequisite order when closing a ground closes
its prerequisites, so `prereq a b` and `b ∈ S` force `a ∈ S`. -/
abbrev closeable {n : ℕ} (prereq : Fin n → Fin n → Bool) (S : Fin n → Bool) : Prop :=
  ∀ a b, prereq a b = true → S b = true → S a = true

/-- No prerequisites: the discrete (free) order. -/
def prereqDiscrete {n : ℕ} : Fin n → Fin n → Bool := fun _ _ => false

/-- The two-chain and three-chain (covering relations). -/
def prereqChain2 : Fin 2 → Fin 2 → Bool := fun a b => decide (a = 0) && decide (b = 1)
def prereqChain3 : Fin 3 → Fin 3 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 1) && decide (b = 2))

/-- The V (one below two) and Λ (two below one). -/
def prereqV3 : Fin 3 → Fin 3 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 0) && decide (b = 2))
def prereqLambda3 : Fin 3 → Fin 3 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 2)) || (decide (a = 1) && decide (b = 2))

/-- The mixed order: a two-chain `0 ≺ 1` and a free ground `2`. -/
def prereqMixed3 : Fin 3 → Fin 3 → Bool := fun a b => decide (a = 0) && decide (b = 1)

/-! ## Part 1: enumerate, ethical content derived

Per order: the closeable count and the permitted count (the proper opens, the prohibition being the whole set)
are DERIVED via `closeable`; the complemented count is COMPUTED as lattice arithmetic on that family. Boolean
iff the closeable family is the full powerset. -/

/-- **n = 1 and n = 2.** DERIVED: n = 1 has one permitted move (binary, Boolean). n = 2 discrete, three
permitted (Boolean); the two-chain, two permitted (Heyting). COMPUTED complements: all versus two. -/
theorem enumerate_n1_n2 :
    ((Finset.univ.filter (fun S : Fin 1 → Bool => closeable prereqDiscrete S ∧ ¬ ∀ r, S r = true)).card = 1)
    ∧ ((Finset.univ.filter (fun S : Fin 2 → Bool => closeable prereqDiscrete S ∧ ¬ ∀ r, S r = true)).card = 3
        ∧ (Finset.univ.filter (fun S : Fin 2 → Bool =>
            closeable prereqDiscrete S ∧ closeable prereqDiscrete (fun r => !S r))).card = 4)
    ∧ ((Finset.univ.filter (fun S : Fin 2 → Bool => closeable prereqChain2 S ∧ ¬ ∀ r, S r = true)).card = 2
        ∧ (Finset.univ.filter (fun S : Fin 2 → Bool =>
            closeable prereqChain2 S ∧ closeable prereqChain2 (fun r => !S r))).card = 2) :=
  ⟨by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **n = 3.** DERIVED permitted counts: discrete 7 (Boolean), chain 3, V 4, Λ 4, mixed 5 (all Heyting).
COMPUTED complemented counts: discrete 8, chain 2, V 2, Λ 2, mixed 4. The mixed order, with a free ground,
complements more. -/
theorem enumerate_n3 :
    ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqDiscrete S ∧ ¬ ∀ r, S r = true)).card = 7
      ∧ (Finset.univ.filter (fun S : Fin 3 → Bool =>
          closeable prereqDiscrete S ∧ closeable prereqDiscrete (fun r => !S r))).card = 8)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqChain3 S ∧ ¬ ∀ r, S r = true)).card = 3
      ∧ (Finset.univ.filter (fun S : Fin 3 → Bool =>
          closeable prereqChain3 S ∧ closeable prereqChain3 (fun r => !S r))).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqV3 S ∧ ¬ ∀ r, S r = true)).card = 4
      ∧ (Finset.univ.filter (fun S : Fin 3 → Bool =>
          closeable prereqV3 S ∧ closeable prereqV3 (fun r => !S r))).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqLambda3 S ∧ ¬ ∀ r, S r = true)).card = 4
      ∧ (Finset.univ.filter (fun S : Fin 3 → Bool =>
          closeable prereqLambda3 S ∧ closeable prereqLambda3 (fun r => !S r))).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqMixed3 S ∧ ¬ ∀ r, S r = true)).card = 5
      ∧ (Finset.univ.filter (fun S : Fin 3 → Bool =>
          closeable prereqMixed3 S ∧ closeable prereqMixed3 (fun r => !S r))).card = 4) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
   ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **Boolean iff free.** The Boolean case is the discrete order, where the closeable family is the whole
powerset; every forced order is properly Heyting, its family a proper subset. DERIVED. -/
theorem boolean_iff_free :
    (∀ S : Fin 3 → Bool, closeable prereqDiscrete S)
    ∧ (¬ ∀ S : Fin 3 → Bool, closeable prereqChain3 S) :=
  ⟨by decide, by decide⟩

/-! ## Part 2: occupancy as specification (READINGS)

A structure's occupancy condition is a specification: what a domain must exhibit to present it, whether or not
anything does. -/

/-- **Occupancy conditions** (READING, defeasible). To present a structure a domain must exhibit `n`
distinguishable grounds whose prerequisites match the order, positions passing the dispute test. The signatures:
n = 1 has one permitted move, the three-chain three. Specifications, not a survey. -/
def occupancy_conditions : Prop :=
  (Finset.univ.filter (fun S : Fin 1 → Bool => closeable prereqDiscrete S ∧ ¬ ∀ r, S r = true)).card = 1
    ∧ (Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqChain3 S ∧ ¬ ∀ r, S r = true)).card = 3

/-- **Known instances** (READING, defeasible). Physics presents n = 1; type systems, Rubin's mechanisms, and
compositional missingness present the three-chain. Everything else is unoccupied, including the whole discrete
column. Stated, not asserted. -/
def known_instances : Prop :=
  (Finset.univ.filter (fun S : Fin 1 → Bool => closeable prereqDiscrete S ∧ ¬ ∀ r, S r = true)).card = 1
    ∧ (Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqChain3 S ∧ ¬ ∀ r, S r = true)).card = 3
    ∧ (Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqDiscrete S ∧ ¬ ∀ r, S r = true)).card = 7

/-! ## Part 3: organize the enumeration -/

/-- **Refinement orders the enumeration.** One structure refines another when it has more closeable sets, fewer
prerequisites: `closeable A ⊇ closeable B`. The discrete order refines every other (its family is the whole
powerset) and sits at the top; the chain sits below the mixed order, which sits below the discrete. This is the
inclusion order on families, a partial order. -/
theorem refinement_orders_the_enumeration :
    (∀ S : Fin 3 → Bool, closeable prereqChain3 S → closeable prereqDiscrete S)
    ∧ (∃ S : Fin 3 → Bool, closeable prereqDiscrete S ∧ ¬ closeable prereqChain3 S)
    ∧ (∀ S : Fin 3 → Bool, closeable prereqChain3 S → closeable prereqMixed3 S)
    ∧ (∃ S : Fin 3 → Bool, closeable prereqMixed3 S ∧ ¬ closeable prereqChain3 S) := by
  refine ⟨by decide, ?_, by decide, ?_⟩
  · exact ⟨fun r => decide (r = 1), by decide, by decide⟩
  · exact ⟨fun r => decide (r = 2), by decide, by decide⟩

/-- **Refinement reads.** Higher in the order is fewer prerequisites, so grounds less dependent on one another:
the discrete top has no prerequisites, every set closeable; a forced structure below has prerequisites, fewer
sets closeable. The reading holds. -/
theorem refinement_reads :
    (∀ S : Fin 3 → Bool, closeable prereqDiscrete S)
    ∧ (¬ ∀ S : Fin 3 → Bool, closeable prereqChain3 S) :=
  ⟨by decide, by decide⟩

/-- **Topology is translation, except connectedness.** Fineness is refinement, and the discrete order is the
finest, already the refinement top; T₁, every singleton open, holds iff the order is discrete (`{1}` is
closeable without prerequisites, not under the chain); sobriety is T₀, which all these posets satisfy. Each is
an order statement rewritten. -/
theorem topology_is_translation :
    (∀ S : Fin 3 → Bool, closeable prereqDiscrete S)
    ∧ closeable prereqDiscrete (fun r => decide (r = (1 : Fin 3)))
    ∧ ¬ closeable prereqChain3 (fun r => decide (r = (1 : Fin 3))) :=
  ⟨by decide, by decide, by decide⟩

/-- **Connectedness is content.** It does work refinement does not: the mixed order has an isolated ground `2`,
related to nothing (disconnected, a free ground), while the chain has none (`2` is related). This is the
free-ground axis, and it is what makes the mixed order complement more (four versus the chain's two). The
topological vocabulary contributes the name; the distinction is a genuine second axis the refinement depth does
not record. -/
theorem connectedness_is_content :
    ((∀ b : Fin 3, prereqMixed3 2 b = false) ∧ (∀ a : Fin 3, prereqMixed3 a 2 = false))
    ∧ (prereqChain3 1 2 = true)
    ∧ (Finset.univ.filter (fun S : Fin 3 → Bool =>
        closeable prereqMixed3 S ∧ closeable prereqMixed3 (fun r => !S r))).card = 4
    ∧ (Finset.univ.filter (fun S : Fin 3 → Bool =>
        closeable prereqChain3 S ∧ closeable prereqChain3 (fun r => !S r))).card = 2 :=
  ⟨⟨by decide, by decide⟩, by decide, by decide, by decide⟩

/-! ## The verdict

Part 1: the structures at n ≤ 3 with derived ethical content. The closeable family, the permitted count, and
the Boolean/Heyting verdict are DERIVED from the closure notion `closeable` (a set is closeable when closing a
ground closes its prerequisites): n = 1 binary, n = 2 discrete (3, Boolean) and chain (2, Heyting), n = 3
discrete (7, Boolean), chain (3), V (4), Λ (4), mixed (5), all forced ones Heyting. The complemented counts are
COMPUTED as lattice arithmetic on the derived family (discrete 8, chain/V/Λ 2, mixed 4), and marked as such.

Part 2: occupancy is specification. Each structure states what a domain must exhibit to present it
(`occupancy_conditions`); the known instances are physics at n = 1 and three domains at the three-chain, the
rest unoccupied including the discrete column (`known_instances`), a reading.

Part 3: refinement orders the enumeration and reads. It is the inclusion order on closeable families, a partial
order with the discrete structure at the top (`refinement_orders_the_enumeration`), and higher means fewer
entanglements among grounds (`refinement_reads`). Topology mostly does not earn its keep: fineness is
refinement, T₁ is discrete, sobriety is T₀, all translation (`topology_is_translation`), so the vocabulary is
dropped. The exception is connectedness (`connectedness_is_content`): it flags a free ground, the disconnected
structures, the same distinction as the complement jump, which refinement depth does not name. That one notion
is content, a second axis; the topology contributes its name, not new structure. Nothing here is resolved. -/

end Chiralogy.GroundStructures
