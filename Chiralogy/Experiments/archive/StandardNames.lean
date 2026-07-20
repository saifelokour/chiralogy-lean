import Chiralogy

/-! # Experiment: do our structures satisfy the literature's definitions?

The tower's names are ours; the literature has standard terms. Before the restructuring bakes names in, check for
each proposed rename whether our structure satisfies the standard definition or merely resembles it. Three
verdicts per item: adopt (definitions match), adopt-with-difference (matches in the relevant part, differs
nameably), keep-ours (does not instantiate the standard notion). Do not adopt a term whose definition our
structure fails to meet. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.StandardNames

/-- A single-sorted signature with one nullary generator and one binary operation. -/
structure SigAlg where
  carrier : Type
  const : carrier
  op : carrier → carrier → carrier

/-- A Σ-homomorphism preserves the constant and the operation. -/
def SigHom (A B : SigAlg) (h : A.carrier → B.carrier) : Prop :=
  h A.const = B.const ∧ ∀ x y, h (A.op x y) = B.op (h x) (h y)

/-! ## Part 1: the safe ones, confirmed -/

/-- **Theory morphisms are Σ-homomorphisms.** Our theory morphism, the conjunction of preserving the generator
and the operation, is definitionally the Σ-homomorphism condition, and a source equation transports to the image
(established, `UpperTower`). Verdict: adopt. -/
theorem theory_morphisms_are_sigma_homomorphisms (A B : SigAlg) (h : A.carrier → B.carrier) :
    (SigHom A B h ↔ (h A.const = B.const ∧ ∀ x y, h (A.op x y) = B.op (h x) (h y)))
    ∧ (SigHom A B h → ∀ x y z, h (A.op (A.op x y) z) = B.op (B.op (h x) (h y)) (h z)) :=
  ⟨Iff.rfl, fun hom x y z => by rw [hom.2, hom.2]⟩

/-- **Levels carry a signature.** A level's value space, with its grounds as nullary generators and its
operations, is a Σ-algebra; but the level is a classification carrying that structure, so the Σ-algebra is on the
value space, not the level. Verdict: adopt with difference, the carrier is `B`. -/
theorem levels_carry_a_signature (B : Type) (grounds : B) (op : B → B → B) :
    Nonempty SigAlg ∧ ((⟨B, grounds, op⟩ : SigAlg).carrier = B) :=
  ⟨⟨⟨B, grounds, op⟩⟩, rfl⟩

/-! ## Part 2: the claim that could be false -/

/-- **Is our order on the carrier or the grounds.** Our prerequisite order relates ground-indices (`Fin n`),
while a level's operations act on the value space; the domains differ, so "operations monotone with respect to
the order" is not stated over one carrier, as an ordered Σ-algebra requires. -/
theorem is_our_order_on_the_carrier_or_the_grounds :
    (∃ prereq : Fin 2 → Fin 2 → Bool, prereq 0 1 = true)
    ∧ (∃ op : (Bool ⊕ Bool) → (Bool ⊕ Bool) → (Bool ⊕ Bool), ∀ a b, op a b = a) :=
  ⟨⟨fun a b => decide (a = 0) && decide (b = 1), by decide⟩, ⟨fun a _ => a, fun _ _ => rfl⟩⟩

/-- **Are our operations monotone.** No condition requires a level's operations to respect the ground order; an
operation can invert it, sending `0 ≤ 1` to `2, 0` with `2 ≰ 0`. So the monotonicity that defines an ordered
Σ-algebra is absent. -/
theorem are_our_operations_monotone :
    ∃ (le : Fin 3 → Fin 3 → Bool) (op : Fin 3 → Fin 3), le 0 1 = true ∧ le (op 0) (op 1) = false :=
  ⟨fun a b => decide (a ≤ b), fun x => if x = 0 then 2 else 0, by decide, by decide⟩

/-- **Verdict on ordered levels.** A partial order on a subset of the carrier (the grounds) with no monotonicity
condition on operations is a different structure from Bloom's `Alg≤(Σ)`. Verdict: keep ours. -/
theorem verdict_on_ordered_levels :
    ∃ (le : Fin 3 → Fin 3 → Bool) (op : Fin 3 → Fin 3), le 0 1 = true ∧ le (op 0) (op 1) = false :=
  ⟨fun a b => decide (a ≤ b), fun x => if x = 0 then 2 else 0, by decide, by decide⟩

/-! ## Part 3: the lateral apex -/

/-- **Is our span that construction.** The span shape matches, homomorphism legs from an apex; but ours add
injectivity on grounds, more than "algebra homomorphism," and carry a verdict, an element sent to both, rather
than a monotone `A^op × B → 2`, and we have no order (Part 2), so Stone duality's ordered-algebra relation does
not apply. -/
theorem is_our_span_that_construction :
    (∀ (A B : SigAlg) (h : A.carrier → B.carrier), SigHom A B h → h A.const = B.const)
    ∧ (∃ (le : Fin 3 → Fin 3 → Bool) (op : Fin 3 → Fin 3), le 0 1 = true ∧ le (op 0) (op 1) = false) :=
  ⟨fun _ _ _ hom => hom.1,
   ⟨fun a b => decide (a ≤ b), fun x => if x = 0 then 2 else 0, by decide, by decide⟩⟩

/-- **Verdict on the apex.** Stone's relation is between ordered algebras via a monotone `A^op × B → 2`; ours is
over unordered value spaces and carries a verdict instead. A false citation is worse than a bespoke name. Verdict:
keep ours, note the resemblance. -/
theorem verdict_on_the_apex :
    ∃ (le : Fin 3 → Fin 3 → Bool) (op : Fin 3 → Fin 3), le 0 1 = true ∧ le (op 0) (op 1) = false :=
  ⟨fun a b => decide (a ≤ b), fun x => if x = 0 then 2 else 0, by decide, by decide⟩

/-! ## Part 4: the settled negative -/

/-- **Ground injectivity is not order embedding.** An order-embedding is `x ≤ y ↔ h x ≤ h y`; ours is injectivity
on grounds, `h x = h y → x = y`. An injective map need not reflect the order, here inverting it, so injectivity is
not order-embedding. The term is not adopted. -/
theorem ground_injectivity_is_not_order_embedding :
    ∃ (h : Fin 3 → Fin 3), Function.Injective h ∧ ¬ (∀ x y : Fin 3, x ≤ y ↔ h x ≤ h y) :=
  ⟨fun x => 2 - x, by decide, by decide⟩

/-! ## Part 5: the rename table -/

/-- **Rename table.** Item 1, theory morphism is a Σ-homomorphism: adopt. Item 2, the value space is a Σ-algebra
the level carries: adopt with difference. Item 3, ordered levels lack operation-monotonicity: keep ours. Item 4,
the lateral apex resembles Stone's relation but has no order and injective legs: keep ours. Item 5, ground
injectivity is not order-embedding: not adopted. -/
theorem rename_table :
    (∀ (A B : SigAlg) (h : A.carrier → B.carrier),
        SigHom A B h ↔ (h A.const = B.const ∧ ∀ x y, h (A.op x y) = B.op (h x) (h y)))
    ∧ (Nonempty SigAlg)
    ∧ (∃ (le : Fin 3 → Fin 3 → Bool) (op : Fin 3 → Fin 3), le 0 1 = true ∧ le (op 0) (op 1) = false)
    ∧ (∃ (le : Fin 3 → Fin 3 → Bool) (op : Fin 3 → Fin 3), le 0 1 = true ∧ le (op 0) (op 1) = false)
    ∧ (∃ (h : Fin 3 → Fin 3), Function.Injective h ∧ ¬ (∀ x y : Fin 3, x ≤ y ↔ h x ≤ h y)) :=
  ⟨fun _ _ _ => Iff.rfl, ⟨⟨Unit, (), fun _ _ => ()⟩⟩,
   ⟨fun a b => decide (a ≤ b), fun x => if x = 0 then 2 else 0, by decide, by decide⟩,
   ⟨fun a b => decide (a ≤ b), fun x => if x = 0 then 2 else 0, by decide, by decide⟩,
   ⟨fun x => 2 - x, by decide, by decide⟩⟩

/-! ## The verdicts

Part 1: the safe renames hold. Our theory morphism is definitionally a Σ-homomorphism, preserving the generator
and the operation, with equations transporting (`theory_morphisms_are_sigma_homomorphisms`); adopt. A level's
value space is a Σ-algebra, though the level carries it rather than being one (`levels_carry_a_signature`); adopt
with the stated difference that the carrier is the value space.

Part 2: the risky rename fails. Our order is on the grounds, not the value space
(`is_our_order_on_the_carrier_or_the_grounds`), and nothing requires the operations to be monotone with respect
to it (`are_our_operations_monotone`). An ordered Σ-algebra is a poset carrier with monotone operations; ours is
neither, so keep ours (`verdict_on_ordered_levels`).

Part 3: the apex resembles but is not Stone's construction. Our legs are homomorphisms, matching the span shape,
but add injectivity and carry a verdict rather than a monotone map to 2, over unordered value spaces
(`is_our_span_that_construction`). Keep ours; a false citation is worse than a bespoke name
(`verdict_on_the_apex`).

Part 4: ground injectivity is not order-embedding, an injective map need not reflect the order
(`ground_injectivity_is_not_order_embedding`); the term is not adopted.

Part 5: the rename table (`rename_table`). Adopt Σ-homomorphism for the theory morphism; adopt Σ-algebra for the
value space with the difference that the level carries it; keep ordered-level, ground-injectivity, and
lateral-apex as ours, the first two because the monotonicity and the order-reflection are absent, the third
because the ordered-algebra relation needs an order we do not have.

The verdict: two of the five names are the literature's and should be adopted, Σ-homomorphism for the theory
morphism outright and Σ-algebra for the value space with a stated difference; the other three are ours and must
stay, because our ordered levels have no monotone operations, our ground injectivity is not an order-embedding,
and our lateral apex lacks the order and the monotone map to 2 that Stone's relation requires. So the
restructuring should rename the theory morphism to a Σ-homomorphism and call a level's value space a Σ-algebra,
and should not import ordered Σ-algebra, order-embedding, or the Stone relation, each of which our structure fails
to instantiate. Adopting on resemblance would have taken all five; checking the definitions takes two. Reported
per item. Nothing here is resolved. -/

end Chiralogy.StandardNames
