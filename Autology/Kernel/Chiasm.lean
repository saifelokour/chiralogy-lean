import Autology.Kernel.SelfApplication
import Autology.Protocol.Membership

/-! # Chiasm: the shared-center census

Do the framework's principal inversions cross at one center? Census, by proof term, not by citation.

The self-referential inversion (`self_account_has_hole`, `𝒜`) and the epistemic inversion (membership's
payload) both turn on non-surjectivity `no_reflexive_object` (K1): each is that obstruction applied to an
object's own classification (`two_inversions_share_center`). The ethical inversion
(`complete_and_faithful_is_impossible`, total ∧ faithful cancel) does not: it turns on a constitutive
absence (`imprecise 0 2 = none`), which is independent of non-surjectivity, since a total object carries
the hole with no such absence (`ethical_center_is_distinct`). So the three do not factor through one
center: two cross at the Lawvere hole, the ethical arm at the partial absence. What all three do share is
only that the center is empty (`center_is_empty`): an absence, not a positive object.

○ chiasm_does_not_totalize: this census settles the center question alone. "The framework is chiastic" is a
complete self-account of its own form, forbidden by `no_complete_self_account`; the figure stays a reading
(●). Only the emptiness of the centers and the two-way sharing are ●●; the single common center is refuted. -/

namespace Autology

/-- **Two inversions share the center.** The self-referential (`𝒜`) and epistemic (any `Member`)
inversions both factor through non-surjectivity `no_reflexive_object` (K1): each conjunct is that one
obstruction applied to the object's own classification. -/
theorem two_inversions_share_center :
    (¬ Function.Surjective 𝒜.classify) ∧ (∀ M : Member, ¬ Function.Surjective M.classify) :=
  ⟨no_reflexive_object (g := fun b => !b) (by decide) 𝒜.classify,
   fun M => (fpf_of_canDiffer M.canDiffer).elim fun _ hg => no_reflexive_object hg M.classify⟩

/-- **The ethical center is distinct.** The ethical inversion turns on a constitutive absence
(`imprecise 0 2 = none`), not on non-surjectivity: a total object (`∀ x y, c x y ≠ none`) still carries the
hole. Non-surjectivity does not supply the constitutive absence, so the ethical pivot is a second center. -/
theorem ethical_center_is_distinct :
    ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ ¬ Function.Surjective c :=
  ⟨fun _ _ => some true, fun _ _ => (by decide : (some true : Option Bool) ≠ none), hole_uniform _⟩

/-- **The center is empty.** Wherever an inversion crosses, it crosses at an absence, not a positive
object: no carrier is equivalent to its own classifier space (`empty_center`, K1). -/
theorem center_is_empty : ¬ ∃ X : Type, Nonempty (X ≃ (X → Bool)) := empty_center

end Autology
