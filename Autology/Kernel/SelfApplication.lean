import Autology.Kernel.Autology
import Autology.Kernel.Trichotomy

/-! # Self-application

The framework's own self-classification, represented internally as an object `𝒜 : Obj`, is non-degenerate
and carries the payload (`self_account_has_hole`). ○ Gap (handed back): `𝒜 : Obj` codes self-classifying
systems, which inhabit `Type 1`, into `Type 0`; the coding is not surjective onto them and this theorem is
not proved inside `𝒜`. Representation is not identity (Gödel): `𝒜 = Autology` is neither stated nor
provable, and that distance is `𝒜`'s own hole (`no_reflexive_object` applied to the framework). -/

namespace Autology

/-- Codes for self-classifying systems: a `Type 0` proxy for objects of `Autology` (which live in `Type 1`). -/
abbrev Rep : Type := Nat

/-- The internal self-classification: `selfClassify s t` is `s`'s decidable proxy verdict that system `t`
completely classifies itself (a reflexive proxy: a system vouches only for itself). -/
def selfClassify : Rep → Rep → Bool := fun s t => decide (s = t)

theorem selfClassify_nondegenerate : NonDegenerate selfClassify :=
  ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩

theorem selfClassify_hole : ¬ Function.Surjective selfClassify :=
  hole_transports (g := fun b => !b) (by decide) selfClassify

/-- `𝒜`: a faithful internal representation of Autology's own self-classification as an object. -/
def 𝒜 : Obj := ⟨Rep, Bool, selfClassify⟩

/-- The codomain is a genuine two-point space: `𝒜` is a well-formed object. -/
theorem 𝒜_canDiffer : ∃ a b : 𝒜.B, a ≠ b := ⟨true, false, fun h => Bool.noConfusion h⟩

/-- **Non-degenerate.** The self enters the representation: two systems classify differently. -/
theorem 𝒜_nondegenerate : NonDegenerate 𝒜.classify := selfClassify_nondegenerate

/-- **Self-application (the payload, internally).** The internal representation of Autology's own
self-classification is not surjective onto its rows: it carries the hole. -/
theorem self_account_has_hole : ¬ Function.Surjective 𝒜.classify := selfClassify_hole

end Autology
