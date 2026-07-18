import Chiralogy

/-! # Experiment: what transport does at the boundary

The elimination (`Tricameral.lean`) ruled transport out as a third chamber and concluded it "enriches the
boundary", a verdict with no content. This build gives it content or shows there is none. The decisive test
throughout is whether a morphism `φ` is used in a proof: if the target's property holds without `φ`,
transport contributed nothing.

Stays in `Experiments/`; canonical layers untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Transport

/-! ## Q1: is the center-assignment functorial? (the variance decides) -/

/-- **Q1, the covariant half.** A morphism transports the exponential's codomain, by postcomposition with
`onValues`: `(S.X → S.B) → (S.X → T.B)`. This half is functorial. -/
def exp_codomain_transports (S T : Obj) (φ : Hom S T) : (S.X → S.B) → (S.X → T.B) :=
  fun h => φ.onValues ∘ h

/-- **Q1, the block.** The exponential's domain `S.X` is contravariant, so to transport it covariantly one
would need `T.X → S.X`. A morphism supplies the opposite, `onCarrier : S.X → T.X`. The wrong direction, so
there is no induced map to `(T.X → T.B)`: the center-assignment `S ↦ (S.X → S.B)` is mixed-variance, not a
functor on `Obj`. -/
def onCarrier_is_wrong_direction (S T : Obj) (φ : Hom S T) : S.X → T.X :=
  φ.onCarrier

/-- **Q1 at the center itself: vacuous.** The center is empty (`empty_center_is_coincidence`), so a morphism
induces the unique map between empty types, by `absurd`. The morphism `_φ` is unused: this functoriality is
vacuous, there is nothing to transport. -/
def center_map_is_vacuous (S T : Obj) (_φ : Hom S T)
    (gS : S.B → S.B) (hgS : ∀ b, gS b ≠ b) :
    (S.X ≃ (S.X → S.B)) → (T.X ≃ (T.X → T.B)) :=
  fun e => absurd ⟨e⟩ (empty_center_is_coincidence gS hgS)

/-! ## Q2: is the hole natural or unnatural? -/

/-- **Q2: the hole is pointwise (unnatural).** The target's hole holds without the morphism `_φ`: every
object is independently holed (`no_reflexive_object`). So the family is a pointwise assignment, not a natural
transformation. The diagonal witness would be natural only if `onValues` intertwined the fixed-point-free
endomaps (`onValues ∘ gS = gT ∘ onValues`), a condition `Hom` does not impose, so it is unnatural. -/
theorem hole_is_pointwise (S T : Obj) (_φ : Hom S T) (gT : T.B → T.B) (hgT : ∀ b, gT b ≠ b) :
    ¬ Function.Surjective T.classify :=
  no_reflexive_object hgT T.classify

/-! ## Q3: does center-emptiness transport non-vacuously? -/

/-- **Q3: vacuous.** The target's center is empty without the morphism `_φ`: emptiness holds of every object
independently (`empty_center_is_coincidence`). The proof does not use `_φ`, so transport contributes nothing
at the center; preservation is vacuous. -/
theorem center_transported_vacuously (S T : Obj) (_φ : Hom S T)
    (gT : T.B → T.B) (hgT : ∀ b, gT b ≠ b) :
    ¬ Nonempty (T.X ≃ (T.X → T.B)) :=
  empty_center_is_coincidence gT hgT

/-! ## Q4: is there a global center over the category? (closed by Q1) -/

/-- **Q4: no global center, closed by Q1.** The center-assignment is not a functor (Q1, mixed variance), so
there is no functor `Obj → Type` whose limit could be a category-wide center. Each object's center is empty
(uniformly), but per-object: the emptiness does not glue. -/
theorem no_global_center (S : Obj) (gS : S.B → S.B) (hgS : ∀ b, gS b ≠ b) :
    ¬ Nonempty (S.X ≃ (S.X → S.B)) :=
  empty_center_is_coincidence gS hgS

/-! ## The verdict: thin

Q1 non-functorial (mixed variance blocks the domain; vacuous at the empty center). Q2 unnatural (the hole is
pointwise, the morphism unused). Q3 vacuous (center-emptiness holds per object, the morphism unused). Q4
blocked by Q1 (no functor, no limit, no global center). Transport relates objects and adds no boundary
content: the 2-categorical layer is real but thin. The framework is per-object, and the empty center does not
glue across the category. The elimination's "enriches the boundary" is sharpened: transport is a relation,
not an enrichment. -/

end Chiralogy.Transport
