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

/-! ## The bound and free parts: connected components

The comparability graph's connected components split a ground-order canonically; a free ground is an isolated
point. The bound/free decomposition is the components decomposition with singletons separated, coarser than it
(two disjoint chains are two components lumped as one bound part): the components are the standard part, the
coarsening ours. -/

/-- A ground is free when isolated: comparable to no other. -/
abbrev isFree {n : ℕ} (prereq : Fin n → Fin n → Bool) (i : Fin n) : Prop :=
  ∀ j, j ≠ i → prereq i j = false ∧ prereq j i = false

/-- **The closeable family factors over the components.** At the mixed order a closeable set is exactly the bound
part's up-closure `S 1 → S 0` with the free ground `2` unconstrained, so it is its restriction to each component,
the free part contributing freely. -/
theorem closeable_sets_factor :
    ∀ S : Fin 3 → Bool, closeable prereqMixed3 S ↔ (S 1 = true → S 0 = true) := by decide

/-- **The permitted count factors as a product over components.** The mixed order's closeable count is six, the
chain's three times the free ground's two; the whole-order count of `enumerate_small` is this product. -/
theorem permitted_count_factors :
    ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqMixed3 S)).card = 6)
    ∧ ((Finset.univ.filter (fun S : Fin 2 → Bool => closeable prereqChain2 S)).card = 3)
    ∧ ((Finset.univ.filter (fun S : Fin 1 → Bool => closeable prereqDiscrete S)).card = 2) :=
  ⟨by decide, by decide, by decide⟩

/-- **Fabrication cost splits over the parts.** In the free part a fabrication costs one, the isolated ground `2`
closeable alone; in the bound part it costs its prerequisite-closure, ground `1` not closeable alone but forcing
`0`. -/
theorem fabrication_cost_by_part :
    (closeable prereqMixed3 (fun i => decide (i = 2)))
    ∧ (¬ closeable prereqMixed3 (fun i => decide (i = 1)))
    ∧ (closeable prereqMixed3 (fun i => decide (i = 0 ∨ i = 1))) :=
  ⟨by decide, by decide, by decide⟩

/-! ## The ground-structure generically, over an arbitrary open

The closeable family is the up-sets of the preorder, the Alexandrov opens; the topological vocabulary is dropped
(`free_ground_axis`), so `closeable` is kept and its Alexandrov theory unused. Over an arbitrary open the
permitted family, the prohibition, and the operations hold without a count. -/

/-- The generic closeable predicate, over an arbitrary order. -/
def closeableG {ι : Type} (prereq : ι → ι → Prop) (S : ι → Prop) : Prop :=
  ∀ a b, prereq a b → S b → S a

/-- The Heyting negation as the interior of the complement: the union of closeable sets disjoint from `S`. -/
def negInterior {ι : Type} (prereq : ι → ι → Prop) (S : ι → Prop) : ι → Prop :=
  fun x => ∃ T : ι → Prop, closeableG prereq T ∧ (∀ y, T y → ¬ S y) ∧ T x

/-- **The permitted moves are the proper opens, without a count.** The whole space is closeable (the prohibition
at the top) and the empty closure is a proper open, over any index. -/
theorem permitted_are_the_proper_opens {ι : Type} (prereq : ι → ι → Prop) :
    (closeableG prereq (fun _ => True)) ∧ (closeableG prereq (fun _ => False)) :=
  ⟨fun _ _ _ _ => trivial, fun _ _ _ h => h⟩

/-- **The operations stay inside the family at arbitrary index.** An arbitrary intersection and an arbitrary union
of closeable sets are closeable, over any index type, infinite included: complete distributivity without
finiteness. -/
theorem operations_generically {ι : Type} (prereq : ι → ι → Prop) :
    (∀ (J : Type) (F : J → (ι → Prop)), (∀ j, closeableG prereq (F j)) →
        closeableG prereq (fun x => ∀ j, F j x))
    ∧ (∀ (J : Type) (F : J → (ι → Prop)), (∀ j, closeableG prereq (F j)) →
        closeableG prereq (fun x => ∃ j, F j x)) :=
  ⟨fun _ _F hF a b hab hb j => hF j a b hab (hb j),
   fun _ _F hF a b hab => fun ⟨j, hj⟩ => ⟨j, hF j a b hab hj⟩⟩

/-- **Negation is the interior of the complement, generically.** The negation is closeable and contained in the
complement, a proof from the definition rather than an enumeration. -/
theorem negation_is_interior_of_complement {ι : Type} (prereq : ι → ι → Prop) (S : ι → Prop) :
    (closeableG prereq (negInterior prereq S)) ∧ (∀ x, negInterior prereq S x → ¬ S x) :=
  ⟨fun a b hab => fun ⟨U, hU, hUc, hUb⟩ => ⟨U, hU, hUc, hU a b hab hUb⟩,
   fun _ => fun ⟨_U, _, hUc, hUx⟩ => hUc _ hUx⟩

/-- **The permitted family and operations hold at an infinite ground-set.** At `ℕ` with `<` the prohibition, a
proper open, and intersection all hold, where the count `2^n - 1` is silent: the structural results are content at
infinite index, the count essentially finite. -/
theorem infinite_grounds :
    (closeableG (· < · : ℕ → ℕ → Prop) (fun _ => True))
    ∧ (closeableG (· < · : ℕ → ℕ → Prop) (fun _ => False))
    ∧ (∀ S T : ℕ → Prop, closeableG (· < ·) S → closeableG (· < ·) T →
        closeableG (· < ·) (fun x => S x ∧ T x)) :=
  ⟨fun _ _ _ _ => trivial, fun _ _ _ h => h,
   fun _ _ hS hT a b hab hb => ⟨hS a b hab hb.1, hT a b hab hb.2⟩⟩

/-- **What needed finiteness.** Residuation is recovered generically, the negation closeable with no exhaustive
check; the Boolean complement only when the set complement is itself closeable, a discrete order. The count needs
finiteness. -/
theorem what_needed_finiteness {ι : Type} (prereq : ι → ι → Prop) (S : ι → Prop) :
    (closeableG prereq (negInterior prereq S))
    ∧ ((∀ x, (¬ S x) → negInterior prereq S x) ↔ closeableG prereq (fun x => ¬ S x)) := by
  refine ⟨fun a b hab hb => ?_, ?_⟩
  · obtain ⟨U, hU, hUc, hUb⟩ := hb; exact ⟨U, hU, hUc, hU a b hab hUb⟩
  · constructor
    · intro h a b hab hnsb
      obtain ⟨U, hU, hUc, hUb⟩ := h b hnsb
      exact hUc a (hU a b hab hUb)
    · intro hc x hnsx
      exact ⟨fun y => ¬ S y, hc, fun y hy => hy, hnsx⟩

end Chiralogy
