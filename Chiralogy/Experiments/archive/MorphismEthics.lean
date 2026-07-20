import Chiralogy

/-! # Experiment: do morphisms respect the prohibition?

`Hom S T` is `(onCarrier, onValues, preserves)` with `preserves : onValues (S.classify x y) = T.classify
(onCarrier x) (onCarrier y)`. Nothing in the laws requires `onValues` to carry an absence in `S.B` to an
absence in `T.B`. Test whether a morphism can carry a partial classification to a total one, totalization by a
map, and whether the prohibition reaches it. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy CategoryTheory

namespace Chiralogy.MorphismEthics

/-- A partial classification: an absence off the diagonal. -/
def partialClass : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none

/-- An `onValues` that fabricates a verdict from the absence: `none` to `true`. -/
def totalOnValues : Option Bool → Bool := fun v => v.getD true

/-- The image classification, total by its codomain `Bool`. -/
def totalClass : Fin 2 → Fin 2 → Bool := fun x y => totalOnValues (partialClass x y)

def partialObj : Obj := ⟨Fin 2, Option Bool, partialClass⟩
def totalObj : Obj := ⟨Fin 2, Bool, totalClass⟩

/-- The totalizing morphism: identity on carriers, fabricating on values. -/
def totalizingHom : Hom partialObj totalObj := ⟨id, totalOnValues, fun _ _ => rfl⟩

/-! ## Part 1: can a morphism send an absence to a verdict? -/

/-- **`onValues` is unconstrained.** For any `onValues : S.B → T.B` the sole law, `preserves`, is satisfied by
defining the target as `onValues` after `S.classify`. So no condition requires an absence in `S.B` to map to an
absence in `T.B`. -/
theorem onValues_is_unconstrained {SX SB TB : Type} (c : SX → SX → SB) (f : SB → TB) :
    ∃ φ : Hom ⟨SX, SB, c⟩ ⟨SX, TB, fun x y => f (c x y)⟩, φ.onValues = f :=
  ⟨⟨id, f, fun _ _ => rfl⟩, rfl⟩

/-- **A morphism totalizes.** `partialObj` is partial, `totalObj` is total, and the morphism sends the absence
`none` to the verdict `true` with `preserves` satisfied (verified, not assumed): the laws permit a map that
fabricates a verdict from an absence. -/
theorem morphism_totalizes :
    (∃ x y, partialClass x y = none)
    ∧ totalizingHom.onValues none = true
    ∧ (∀ x y, totalizingHom.onValues (partialObj.classify x y)
        = totalObj.classify (totalizingHom.onCarrier x) (totalizingHom.onCarrier y)) :=
  ⟨⟨0, 1, by decide⟩, rfl, totalizingHom.preserves⟩

/-! ## Part 2: does the prohibition reach it? -/

/-- **The prohibition is on classifications.** `complete_and_faithful_is_impossible` and
`full_totality_collides` each quantify over a single classification; neither mentions a morphism. -/
theorem prohibition_is_on_classifications :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2)
    ∧ (¬ ∃ c : Fin 4 → Fin 4 → Bool ⊕ Bool,
        (∀ x y, ∃ b, c x y = Sum.inl b) ∧ (∃ x y e, c x y = Sum.inr e)) :=
  ⟨complete_and_faithful_is_impossible, full_totality_collides⟩

/-- **The image is innocent.** The morphism's image is total, hence permitted (as vacating established for
total classifications); the source is partial, permitted. Neither endpoint is a prohibited classification, and
no prohibited move was applied to either. -/
theorem image_is_innocent :
    (∀ x y, ∃ b : Bool, totalClass x y = b)
    ∧ (∃ x y, partialClass x y = none) :=
  ⟨fun x y => ⟨totalClass x y, rfl⟩, ⟨0, 1, by decide⟩⟩

/-- **Is this the forbidden move?** The morphism fabricates a verdict where the source returned an absence
(`onValues none = true`), the same act totalization performs on values; yet the image is total and keeps no
absence, so it is not the prohibited total-and-faithful classification. The difference: totalization acts on one
classification, filling its absences in the same codomain, where the total-and-faithful collision lives; a
morphism relates two objects, the image a separate consistent codomain. The laundering is real but produces
nothing prohibited. -/
theorem is_this_the_forbidden_move :
    (totalizingHom.onValues none = true ∧ ∃ x y, partialClass x y = none)
    ∧ (∀ x y, ∃ b : Bool, totalClass x y = b) :=
  ⟨⟨rfl, ⟨0, 1, by decide⟩⟩, fun x y => ⟨totalClass x y, rfl⟩⟩

/-! ## Part 3: what would constrain morphisms -/

/-- A morphism is absence-preserving when its `onValues` carries absences to absences. -/
def AbsPreserving {A C : Obj} (absA : A.B → Prop) (absC : C.B → Prop) (φ : A ⟶ C) : Prop :=
  ∀ v, absA v → absC (φ.onValues v)

/-- **Absence-preserving morphisms are a subcategory.** They contain identities (`onValues = id` preserves any
predicate) and compose (`onValues` composes, preservation transitively), so the framework has a natural
ethical restriction on its own morphisms that it does not currently impose. -/
theorem absence_preserving_morphisms {A C D : Obj}
    (absA : A.B → Prop) (absC : C.B → Prop) (absD : D.B → Prop)
    (φ : A ⟶ C) (ψ : C ⟶ D)
    (hφ : AbsPreserving absA absC φ) (hψ : AbsPreserving absC absD ψ) :
    AbsPreserving absA absA (𝟙 A) ∧ AbsPreserving absA absD (φ ≫ ψ) :=
  ⟨fun _ hv => hv, fun v hv => hψ (φ.onValues v) (hφ v hv)⟩

/-- **What is lost.** Restricting to absence-preserving morphisms excludes exactly the laundering ones: the
totalizing morphism is not absence-preserving, its `none` landing in a codomain with no absence. The cost is
that class alone; the transport result `hole_transports` is morphism-free, quantifying a single classification,
so it survives the restriction unchanged. -/
theorem what_is_lost :
    (¬ AbsPreserving (fun v => v = none) (fun _ => False) totalizingHom)
    ∧ (∀ (X B : Type) (g : B → B), (∀ b, g b ≠ b) → ∀ c : X → X → B, ¬ Function.Surjective c) :=
  ⟨fun h => h none rfl, fun _ _ _ hg c => hole_transports hg c⟩

/-! ## The verdicts

Part 1: a morphism can send an absence to a verdict with `preserves` satisfied. `onValues` is bare, constrained
only by `preserves`, which any `onValues` meets by defining the target (`onValues_is_unconstrained`);
`morphism_totalizes` exhibits a partial source, a total image, and a map fabricating a verdict from the absence,
`preserves` verified. The laws do not constrain absence.

Part 2: the prohibition does not reach it. It quantifies over one classification, not a morphism
(`prohibition_is_on_classifications`); the image is total and the source partial, neither prohibited
(`image_is_innocent`). The map fabricates a verdict from an absence yet is not the forbidden move
(`is_this_the_forbidden_move`): totalization acts on one classification in one codomain, where the
total-and-faithful collision lives, while a morphism relates two objects, its image a separate consistent
codomain. The laundering is real but produces nothing prohibited.

Part 3: the absence-preserving morphisms form a subcategory, containing identities and closed under composition
(`absence_preserving_morphisms`), a restriction the framework does not impose. Restricting excludes exactly the
laundering morphisms (`what_is_lost`), and the transport result is morphism-free, so it survives; the transport
findings do not depend on morphisms being unrestricted. The restriction is reported, not imposed; the canonical
category is unchanged. Nothing here is resolved. -/

end Chiralogy.MorphismEthics
