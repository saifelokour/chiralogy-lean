import Chiralogy.Model.Apophatic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card

/-! # Model: ground-structures

The model layer cannot construct a forced level, but the combinatorial structure of a domain's grounds is
constructible: a prerequisite order on grounds, its closeable family, the resulting readable positions. The
closure notion is the framework's own, closing a ground closes its prerequisites; the closeable family, the
permitted counts, and the Boolean/Heyting verdict are derived from it, while the complement counts are lattice
arithmetic on the derived family. The structures are organized by two axes, refinement and the free-ground
distinction. This file names no domain: the occupancy specifications say what a domain would need, not what any
has. -/

namespace Chiralogy

/-- The framework's closure notion: `S` is closeable under the prerequisite order when closing a ground closes
its prerequisites, so `prereq a b` and `S b` force `S a`. -/
abbrev closeable {n : ℕ} (prereq : Fin n → Fin n → Bool) (S : Fin n → Bool) : Prop :=
  ∀ a b, prereq a b = true → S b = true → S a = true

/-- No prerequisites: the discrete (free) order. -/
def prereqDiscrete {n : ℕ} : Fin n → Fin n → Bool := fun _ _ => false

/-- The two-chain and three-chain (covering relations). -/
def prereqChain2 : Fin 2 → Fin 2 → Bool := fun a b => decide (a = 0) && decide (b = 1)
def prereqChain3 : Fin 3 → Fin 3 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 1) && decide (b = 2))

/-- The V (one ground below two) and Λ (two below one). -/
def prereqV3 : Fin 3 → Fin 3 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 0) && decide (b = 2))
def prereqLambda3 : Fin 3 → Fin 3 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 2)) || (decide (a = 1) && decide (b = 2))

/-- The mixed order: a two-chain `0 ≺ 1` and a free ground `2`. -/
def prereqMixed3 : Fin 3 → Fin 3 → Bool := fun a b => decide (a = 0) && decide (b = 1)

/-- **The small structures enumerated.** The permitted counts are derived from `closeable` (the proper opens,
the prohibition being the whole set): n = 1 has one, n = 2 discrete three and the chain two, n = 3 discrete
seven, chain three, V four, Λ four, mixed five. The complement counts are lattice arithmetic on these families,
recorded in `free_ground_axis`. -/
theorem enumerate_small :
    (Finset.univ.filter (fun S : Fin 1 → Bool => closeable prereqDiscrete S ∧ ¬ ∀ r, S r = true)).card = 1
    ∧ (Finset.univ.filter (fun S : Fin 2 → Bool => closeable prereqDiscrete S ∧ ¬ ∀ r, S r = true)).card = 3
    ∧ (Finset.univ.filter (fun S : Fin 2 → Bool => closeable prereqChain2 S ∧ ¬ ∀ r, S r = true)).card = 2
    ∧ (Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqDiscrete S ∧ ¬ ∀ r, S r = true)).card = 7
    ∧ (Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqChain3 S ∧ ¬ ∀ r, S r = true)).card = 3
    ∧ (Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqV3 S ∧ ¬ ∀ r, S r = true)).card = 4
    ∧ (Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqLambda3 S ∧ ¬ ∀ r, S r = true)).card = 4
    ∧ (Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqMixed3 S ∧ ¬ ∀ r, S r = true)).card = 5 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Boolean exactly when the ground-order is discrete.** Every closure is closeable iff there are no
prerequisites; a forced order restricts the family. This is `boolean_because_free` from the other side: that
reads Boolean off the level's freeness (independent constants), this off the ground-order's discreteness, and
they coincide exactly where a level's constants and a domain's grounds agree. -/
theorem boolean_iff_free :
    (∀ S : Fin 3 → Bool, closeable prereqDiscrete S)
    ∧ (¬ ∀ S : Fin 3 → Bool, closeable prereqChain3 S) :=
  ⟨by decide, by decide⟩

/-- **Refinement orders the structures.** One structure refines another when it has more closeable sets, fewer
prerequisites: inclusion of closeable families. The discrete order refines every other and sits at the top; the
chain sits below the mixed order, which sits below the discrete. Inclusion is a partial order, so refinement is
one. -/
theorem refinement_orders_the_structures :
    (∀ S : Fin 3 → Bool, closeable prereqChain3 S → closeable prereqDiscrete S)
    ∧ (∃ S : Fin 3 → Bool, closeable prereqDiscrete S ∧ ¬ closeable prereqChain3 S)
    ∧ (∀ S : Fin 3 → Bool, closeable prereqChain3 S → closeable prereqMixed3 S)
    ∧ (∃ S : Fin 3 → Bool, closeable prereqMixed3 S ∧ ¬ closeable prereqChain3 S) :=
  ⟨by decide, ⟨fun r => decide (r = 1), by decide, by decide⟩, by decide,
   ⟨fun r => decide (r = 2), by decide, by decide⟩⟩

/-- **The free-ground axis.** A structure with a ground standing free complements more than one without: the
mixed order, whose ground `2` is isolated (related to nothing), has four complemented positions to the chain's
two. This is a second axis refinement does not record. The topological vocabulary is dropped, fineness is
refinement, T₁ is discreteness, sobriety is T₀, all order statements rewritten; only the free-ground
distinction does work, and it is order-expressible. -/
theorem free_ground_axis :
    (Finset.univ.filter (fun S : Fin 3 → Bool =>
        closeable prereqMixed3 S ∧ closeable prereqMixed3 (fun r => !S r))).card = 4
    ∧ (Finset.univ.filter (fun S : Fin 3 → Bool =>
        closeable prereqChain3 S ∧ closeable prereqChain3 (fun r => !S r))).card = 2
    ∧ ((∀ b : Fin 3, prereqMixed3 2 b = false) ∧ (∀ a : Fin 3, prereqMixed3 a 2 = false))
    ∧ prereqChain3 1 2 = true :=
  ⟨by decide, by decide, ⟨by decide, by decide⟩, by decide⟩

end Chiralogy
