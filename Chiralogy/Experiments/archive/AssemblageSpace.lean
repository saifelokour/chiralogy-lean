import Chiralogy

/-! # Experiment: is the ground-structure enumeration a taxonomy of assemblage-types?

Coding identifies with order-density (closures ruled out), territorialization with the endpoint-count (maximal
elements), both computed from the prerequisite order. `Grounds` enumerates ground-orders. Test whether that
enumeration is the space of assemblage-parameters, computing all candidates across all instances before judging.
The identification with DeLanda's parameters is IMPORTED and defeasible, a READING; the computations are theorems.
Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.AssemblageSpace

/-- The four-chain and the N poset (`0 ≺ 2`, `1 ≺ 2`, `1 ≺ 3`), for the `n = 4` probe. -/
def prereqChain4 : Fin 4 → Fin 4 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 1) && decide (b = 2))
            || (decide (a = 2) && decide (b = 3))
def prereqN4 : Fin 4 → Fin 4 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 2)) || (decide (a = 1) && decide (b = 2))
            || (decide (a = 1) && decide (b = 3))

/-! ## Part 1: the parameter map -/

/-- **The parameters of each order.** Coding (closures ruled out) and territorialization (maximal-count), for the
`n ≤ 3` enumeration: `Fin 1` discrete `(0,1)`, `Fin 2` discrete `(0,2)`, chain2 `(1,1)`, chain3 `(4,1)`, V `(3,2)`,
Λ `(3,1)`, mixed `(2,2)`, `Fin 3` discrete `(0,3)`. -/
theorem parameters_of_each_order :
    ((Finset.univ.filter (fun S : Fin 1 → Bool => ¬ closeable prereqDiscrete S)).card = 0
     ∧ (Finset.univ.filter (fun i : Fin 1 => ∀ j, prereqDiscrete i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun S : Fin 2 → Bool => ¬ closeable prereqDiscrete S)).card = 0
       ∧ (Finset.univ.filter (fun i : Fin 2 => ∀ j, prereqDiscrete i j = false)).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 2 → Bool => ¬ closeable prereqChain2 S)).card = 1
       ∧ (Finset.univ.filter (fun i : Fin 2 => ∀ j, prereqChain2 i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqChain3 S)).card = 4
       ∧ (Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqChain3 i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqV3 S)).card = 3
       ∧ (Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqV3 i j = false)).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqLambda3 S)).card = 3
       ∧ (Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqLambda3 i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqMixed3 S)).card = 2
       ∧ (Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqMixed3 i j = false)).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqDiscrete S)).card = 0
       ∧ (Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqDiscrete i j = false)).card = 3) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
   ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **The map is injective at `n ≤ 3`.** The pairs sharing one coordinate separate on the other: the fork and the
join code alike (three) but territorialize apart (two against one); the chain and the join territorialize alike
(one) but code apart (four against three). No two of the eight enumerated orders share both coordinates. -/
theorem is_the_map_injective :
    ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqV3 S)).card =
       (Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqLambda3 S)).card
     ∧ (Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqV3 i j = false)).card ≠
       (Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqLambda3 i j = false)).card)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqChain3 i j = false)).card =
       (Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqLambda3 i j = false)).card
     ∧ (Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqChain3 S)).card ≠
       (Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqLambda3 S)).card) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **What the coordinates miss, at `n ≤ 3`, is nothing that collides.** The coordinates ignore the free-part, the
mixed order having a free ground and the fork none, but the two differ in coding (two against three), so the
free-part is not needed to separate them here. The loss appears only at `n = 4`. -/
theorem what_the_coordinates_miss :
    ((Finset.univ.filter (fun i : Fin 3 => isFree prereqMixed3 i)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => isFree prereqV3 i)).card = 0)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqMixed3 S)).card ≠
       (Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqV3 S)).card) :=
  ⟨by decide, by decide, by decide⟩

/-! ## Part 2: the space -/

/-- **Which corners are occupied.** Uncoded and territorialized (physics `(0,1)`); heavily coded and
territorialized (the chain `(4,1)`); uncoded and fully deterritorialized (`Fin 3` discrete `(0,3)`). The coded and
fully deterritorialized corner is empty, structurally so (`is_the_space_a_product`). -/
theorem which_corners_are_occupied :
    ((Finset.univ.filter (fun S : Fin 1 → Bool => ¬ closeable prereqDiscrete S)).card = 0
     ∧ (Finset.univ.filter (fun i : Fin 1 => ∀ j, prereqDiscrete i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqChain3 S)).card = 4
       ∧ (Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqChain3 i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqDiscrete S)).card = 0
       ∧ (Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqDiscrete i j = false)).card = 3) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **The register positions.** Physics `(0,1)`, the type register and cognition `(4,1)`, immunology `(2,2)`,
chemistry `(8,2)`, trust `(6,3)`. -/
theorem register_positions :
    ((Finset.univ.filter (fun S : Fin 1 → Bool => ¬ closeable prereqDiscrete S)).card = 0)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => ¬ closeable prereqChemistry S)).card = 8
       ∧ (Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqChemistry i j = false)).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => ¬ closeable prereqTrust S)).card = 6
       ∧ (Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqTrust i j = false)).card = 3) :=
  ⟨by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **The space is not a product.** If every ground is maximal (fully deterritorialized), every closure is
closeable (uncoded): coded-and-fully-deterritorialized is forbidden, so not every combination occurs. A
structural constraint on assemblage-types, not just an unoccupied cell. -/
theorem is_the_space_a_product {n : ℕ} (prereq : Fin n → Fin n → Bool) :
    (∀ i : Fin n, ∀ j, prereq i j = false) → (∀ S : Fin n → Bool, closeable prereq S) :=
  fun hmax S a b hab _ => by rw [hmax a b] at hab; exact absurd hab (by decide)

/-! ## Part 3: does the identification hold at higher n? -/

/-- **At `n = 4` the map is not injective.** Chemistry (a three-chain plus a free ground) and the N poset
(connected) both map to coding eight, territ two: a collision. And a new corner opens, the four-chain at coding
eleven, more coded than any `n ≤ 3` order. -/
theorem n_equals_four :
    ((Finset.univ.filter (fun S : Fin 4 → Bool => ¬ closeable prereqChemistry S)).card = 8
     ∧ (Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqChemistry i j = false)).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => ¬ closeable prereqN4 S)).card = 8
       ∧ (Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqN4 i j = false)).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => ¬ closeable prereqChain4 S)).card = 11) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide⟩

/-! ## Part 4: the verdict -/

/-- **The coordinates are lossy.** Chemistry and the N poset share both coordinates, coding eight and territ two,
but differ in the free-part, chemistry with one free ground and the N poset none, hence in connectivity. So the
two parameters miss the free-part the orders carry: the ground-structure enumeration is richer than the
assemblage-parameter space, and DeLanda's two parameters see less than the framework's ground-structures. -/
theorem the_coordinates_are_lossy :
    ((Finset.univ.filter (fun S : Fin 4 → Bool => ¬ closeable prereqChemistry S)).card =
       (Finset.univ.filter (fun S : Fin 4 → Bool => ¬ closeable prereqN4 S)).card)
    ∧ ((Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqChemistry i j = false)).card =
       (Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqN4 i j = false)).card)
    ∧ ((Finset.univ.filter (fun i : Fin 4 => isFree prereqChemistry i)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 4 => isFree prereqN4 i)).card = 0) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ## The verdicts

Part 1: the parameter map is injective at `n ≤ 3`. Each order has a coding and a territorialization
(`parameters_of_each_order`), the eight pairs all distinct, the pairs sharing one coordinate separating on the
other (`is_the_map_injective`); the coordinates ignore the free-part, but at `n ≤ 3` that causes no collision
(`what_the_coordinates_miss`).

Part 2: the space is occupied unevenly and is not a product. Physics uncoded-territorialized, the chain
coded-territorialized, the discrete order uncoded-deterritorialized (`which_corners_are_occupied`); the six
registers sit across it (`register_positions`); and coded-and-fully-deterritorialized is forbidden, full
deterritorialization forcing uncoding (`is_the_space_a_product`). A structural constraint, not a product.

Part 3: at `n = 4` the map is not injective (`n_equals_four`). Chemistry and the N poset share both coordinates,
and a new corner opens at the four-chain.

Part 4: the coordinates are lossy (`the_coordinates_are_lossy`). Chemistry and the N poset coincide in coding and
territorialization but differ in the free-part, hence connectivity, so the two parameters miss structure the
orders carry.

The verdict: the ground-order enumeration is not the space of assemblage-parameters; the two coordinates are
lossy. At `n ≤ 3` the map is injective and the enumeration looks like a taxonomy, but by the accident of
smallness: at `n = 4` chemistry, a three-chain plus a free ground, and the N poset, connected, share both
coordinates while differing in their free-part and connectivity, which coding and territorialization do not see.
So DeLanda's two parameters see less than the framework's ground-structures do, and the space is not even a
product, coded-and-fully-deterritorialized being forbidden. The reading at the assemblage-theory end is imported
and defeasible; the honest result is that the identification holds only at small `n` and by coincidence, and the
ground-structure carries more, connectivity and the free-part, than the two parameters record. Reported per part.
Nothing here is resolved. -/

end Chiralogy.AssemblageSpace
