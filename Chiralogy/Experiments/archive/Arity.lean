import Chiralogy

/-! # Experiment: is intra-object difference the arity-1 case of inter-object difference?

Test whether non-degeneracy (intra) and exceeding (inter) are one relation at two arities, or whether inter is a
strict extension of intra. `NonDegenerate c := ∃ x x', c x ≠ c x'` is on a single carrier; `exceeds c1 c2 imp`, the
assemblage adding content over the empty-cross juxtaposition, is on a product `X1 × X2` with a cross-region. The
types differ, so this cannot be a definitional identity; the honest form is a relation across the arity gap. Set the
second factor trivial, `X2 = Fin 1`, and compute what the assemblage and cross-region become. Stays in
`Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Arity

def satN : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none

/-! ## Part 1: the collapse -/

/-- **The product collapses.** With a trivial second factor no two pairs differ in both components, so the
cross-region is empty and no pair is fully-cross; the assemblage is entirely the determined region and is
independent of the import. -/
theorem product_collapses (c1 : Fin 2 → Fin 2 → Option Bool)
    (imp imp' : (Fin 2 × Fin 1) → (Fin 2 × Fin 1) → Option Bool) :
    (∀ a b : Fin 2 × Fin 1, ¬ (a.1 ≠ b.1 ∧ a.2 ≠ b.2))
    ∧ (assembleClassify c1 (fun _ _ => none) imp = assembleClassify c1 (fun _ _ => none) imp') := by
  refine ⟨?_, ?_⟩
  · rintro a b ⟨_, h2⟩; exact h2 (Subsingleton.elim a.2 b.2)
  · funext a b
    exact construction_takes_two_objects_and_a_cross_map c1 (fun _ _ => none) imp imp'
      (fun a b _ h2 => absurd (Subsingleton.elim a.2 b.2) h2) a b

/-! ## Part 2: the reduction, or its failure -/

/-- **Exceeding goes vacuous, non-degeneracy stays genuine.** At the collapse the assemblage equals its
juxtaposition for every import, so exceeding is vacuously false; yet non-degeneracy of `c1` is a genuine condition,
holding for a non-degenerate `c1`. So exceeding does not reduce to non-degeneracy: one is constantly false, the
other varies with `c1`. -/
theorem does_exceeding_reduce :
    (∀ (c1 : Fin 2 → Fin 2 → Option Bool) (imp : (Fin 2 × Fin 1) → (Fin 2 × Fin 1) → Option Bool),
        assembleClassify c1 (fun _ _ => none) imp = assembleClassify c1 (fun _ _ => none) (fun _ _ => none))
    ∧ (NonDegenerate satN) := by
  refine ⟨?_, ?_⟩
  · intro c1 imp; funext a b
    exact construction_takes_two_objects_and_a_cross_map c1 (fun _ _ => none) imp (fun _ _ => none)
      (fun a b _ h2 => absurd (Subsingleton.elim a.2 b.2) h2) a b
  · unfold NonDegenerate; decide

/-! ## Part 3: the verdict on priority -/

/-- **Inter is a strict extension of intra.** Non-degeneracy holds for `satN`, but the collapsed assemblage never
exceeds, for any import: the intra requirement holds exactly where the inter requirement is vacuous. Only the empty
direction, exceeding implies non-degeneracy, survives at the collapse, and vacuously; the substantive direction,
non-degeneracy implies exceeding, fails. So intra is prior and inter is built on the product structure that arity 1
lacks; non-degeneracy is not exceeding-against-self. -/
theorem which_is_prior :
    (NonDegenerate satN)
    ∧ (∀ imp : (Fin 2 × Fin 1) → (Fin 2 × Fin 1) → Option Bool,
        ¬ (assembleClassify satN (fun _ _ => none) imp
            ≠ assembleClassify satN (fun _ _ => none) (fun _ _ => none))) := by
  refine ⟨by unfold NonDegenerate; decide, ?_⟩
  intro imp heq
  apply heq; funext a b
  exact construction_takes_two_objects_and_a_cross_map satN (fun _ _ => none) imp (fun _ _ => none)
    (fun a b _ h2 => absurd (Subsingleton.elim a.2 b.2) h2) a b

/-! ## The verdicts

Part 1: the product collapses. With a trivial second factor the cross-region is empty, no pair differing in both
components, and the assemblage is the determined region, independent of the import (`product_collapses`).

Part 2: exceeding goes vacuous. The collapsed assemblage equals its juxtaposition for every import, so exceeding is
vacuously false, while non-degeneracy of `c1` is a genuine condition (`does_exceeding_reduce`); exceeding does not
reduce to non-degeneracy.

Part 3: inter is a strict extension. Non-degeneracy holds where exceeding is vacuous (`which_is_prior`), so intra is
prior and inter is built on the product.

The verdict: inter-object difference is a strict extension of intra-object difference, not its arity-2 form, so the
attractive identity is refused by the computation. At a trivial second factor the product collapses to the first
carrier and the cross-region is empty, since no two pairs can differ in both components when one component cannot
vary; the assemblage is then classified entirely by the first factor and is independent of the import. Exceeding,
defined as the assemblage differing from its empty-cross juxtaposition, therefore goes vacuously false: with no
cross-region there is nothing for the import to add, so the assemblage always equals its juxtaposition, for every
import, and never exceeds. Non-degeneracy of the first factor, by contrast, remains a genuine condition, holding for
a non-degenerate classification. So the two do not reduce to each other across the arity gap: exceeding is
constantly false at arity 1 while non-degeneracy varies, and the only implication that survives, exceeding implies
non-degeneracy, holds vacuously because its premise is false and carries no content, while the substantive
direction, non-degeneracy implies exceeding, fails, witnessed by a non-degenerate first factor whose collapsed
assemblage does not exceed. The dependency is one-way and empty, not mutual: the intra requirement can hold where
the inter requirement is undefined for want of a cross-region, so intra is prior and inter is a strict extension
built on the product, which arity 1 lacks. Reading over this, whether they are mutually constitutive is answered
in the negative: non-degeneracy is not exceeding-against-self, and the model's intra and inter difference are two
relations at two levels, the second requiring structure the first does not, not one operation at two arities. Per
the counter-bias, the elegant answer was not forced, the collapse computed and exceeding found vacuous rather than
reducing; no rfl was manufactured across the type gap, the relation stated as the honest asymmetry between the two
claims at the collapsed instance; and the reduction was named one-way and vacuous, not mutual constitution.
Reported per part. Nothing here is resolved. -/

end Chiralogy.Arity
