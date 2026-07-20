import Chiralogy

/-! # Experiment: can absence-preservation be derived?

Absence-preserving morphisms form a subcategory the framework does not impose. Imposing it would be an external
standard, which the boundary is meant to have none of; the one prohibition is derived (an internal collision).
Test whether absence-preservation follows from existing structure, the kernel, the protocol, the model's own
notions, without a new normative premise, or must be stipulated. Do not modify `Hom`. Stays in `Experiments/`;
canonical untouched; nothing resolved. -/

open Chiralogy CategoryTheory

namespace Chiralogy.DerivePreservation

/-- A partial source: a verdict on the diagonal, an absence off it. -/
def pClass : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some (decide (x = 0)) else none

/-- An `onValues` that fabricates a verdict from the absence. -/
def onV : Option Bool → Bool := fun v => v.getD true

/-- The image, total and non-degenerate. -/
def tClass : Fin 2 → Fin 2 → Bool := fun x y => onV (pClass x y)

def pObj : Obj := ⟨Fin 2, Option Bool, pClass⟩
def tObj : Obj := ⟨Fin 2, Bool, tClass⟩

/-- The laundering morphism. -/
def launderHom : Hom pObj tObj := ⟨id, onV, fun _ _ => rfl⟩

/-- A morphism is absence-preserving when `onValues` carries absences to absences. -/
def AbsPreserving {A C : Obj} (absA : A.B → Prop) (absC : C.B → Prop) (φ : A ⟶ C) : Prop :=
  ∀ v, absA v → absC (φ.onValues v)

/-! ## Part 1: candidate derivations -/

/-- **From conformance: fails.** The laundering morphism's target conforms, non-degenerate and with the payload
firing, while the source is partial. Conformance of the target does not require `onValues` to preserve
absences. -/
theorem from_conformance :
    NonDegenerate tClass ∧ ¬ Function.Surjective tClass ∧ (∃ x y, pClass x y = none) :=
  ⟨⟨0, 1, fun h => absurd (congrFun h 1) (by decide)⟩,
   payload_uniform ⟨true, false, by decide⟩ tClass,
   ⟨0, 1, by decide⟩⟩

/-- **From the hole: fails.** Both source and target carry the hole (the payload), yet the laundering morphism
sends the absence to a verdict. Holed objects at both ends do not contradict laundering. -/
theorem from_the_hole :
    (¬ Function.Surjective pClass) ∧ (¬ Function.Surjective tClass) ∧ launderHom.onValues none = true :=
  ⟨payload_uniform ⟨some true, none, by decide⟩ pClass, payload_uniform ⟨true, false, by decide⟩ tClass, rfl⟩

/-- **From preserves: fails, and forces the opposite.** For any morphism into `tObj`, `preserves` ties
`onValues` at the source's absence to the target's value there, which is a verdict (the target is total). So
`preserves` forces `onValues none` to be a verdict, laundering, rather than deriving preservation. -/
theorem from_preserves (φ : Hom pObj tObj) (x y : Fin 2) (hxy : pObj.classify x y = none) :
    φ.onValues none = tObj.classify (φ.onCarrier x) (φ.onCarrier y) := by
  have h := φ.preserves x y; rwa [hxy] at h

/-- **From the grounds: the structural candidate.** The absence `none` is a nullary generator of the Maybe
theory (`failMaybe`), yet the laundering `onValues` sends it to a verdict, not to a generator of the target. So
`onValues` is a map of value types, not of theories, and a valid `Hom` need not respect the generators.
Absence-preservation is exactly `onValues` being a theory morphism, which `Hom` does not require. -/
theorem from_the_grounds :
    (∀ v : Option Bool, v = none ↔ ∃ u : Unit, failMaybe u = v)
    ∧ onV none = true
    ∧ (∃ φ : Hom pObj tObj, φ.onValues none = true) :=
  ⟨reasons_are_nullary_generators.2, rfl, ⟨launderHom, rfl⟩⟩

/-! ## Part 2: the verdict -/

/-- **Preservation is imposed.** The laundering morphism satisfies every existing requirement, a valid `Hom`
whose target conforms and whose both ends carry the hole, yet it is not absence-preserving. So no existing
condition, of conformance, the hole, or `preserves`, entails preservation: under the current `Hom` it must be
stipulated. -/
theorem preservation_is_imposed :
    (NonDegenerate tClass ∧ ¬ Function.Surjective tClass ∧ ¬ Function.Surjective pClass)
    ∧ ¬ AbsPreserving (fun v => v = none) (fun _ => False) launderHom :=
  ⟨⟨⟨0, 1, fun h => absurd (congrFun h 1) (by decide)⟩,
     payload_uniform ⟨true, false, by decide⟩ tClass,
     payload_uniform ⟨some true, none, by decide⟩ pClass⟩,
   fun h => h none rfl⟩

/-- **What premise would be needed.** The minimal premise is that `onValues` be a theory morphism, carrying the
declared generators (the absences) to absences, equivalently that absences form a distinguished subobject
morphisms respect. This is a structural premise, about what a morphism between levels is, not a normative one:
it imports no external standard but corrects `Hom` to the level's own structure. The laundering morphism fails
exactly this. -/
theorem what_premise_would_be_needed :
    (∀ v : Option Bool, v = none ↔ ∃ u : Unit, failMaybe u = v)
    ∧ ¬ AbsPreserving (fun v => v = none) (fun _ => False) launderHom :=
  ⟨reasons_are_nullary_generators.2, fun h => h none rfl⟩

/-! ## Part 3: is Hom under-specified relative to levels? -/

/-- **Hom versus theory morphism.** For a bare classification `onValues` is a type map, unconstrained beyond
`preserves`: any `f` gives a morphism. For a level the absence is a declared generator (`failMaybe`), and a
morphism of theories would carry it to an absence, which the type map need not do (the laundering morphism does
not). So `Hom` is the right notion for bare classifications and under-specified for levels; absence-preservation
is not an added ethical rule but the missing theory-morphism condition, a structural correction. -/
theorem hom_versus_theory_morphism :
    (∀ {SX SB TB : Type} (c : SX → SX → SB) (f : SB → TB),
        ∃ φ : Hom ⟨SX, SB, c⟩ ⟨SX, TB, fun x y => f (c x y)⟩, φ.onValues = f)
    ∧ (∀ v : Option Bool, v = none ↔ ∃ u : Unit, failMaybe u = v)
    ∧ ¬ AbsPreserving (fun v => v = none) (fun _ => False) launderHom :=
  ⟨fun _ f => ⟨⟨id, f, fun _ _ => rfl⟩, rfl⟩, reasons_are_nullary_generators.2, fun h => h none rfl⟩

/-! ## The verdicts

Part 1: no existing condition derives absence-preservation. Conformance fails, the laundering target conforms
(`from_conformance`); the hole fails, both ends are holed and laundering persists (`from_the_hole`); `preserves`
fails and forces the opposite, tying `onValues` at the absence to the target's verdict (`from_preserves`). The
one structural candidate, `from_the_grounds`, does not derive it from an existing condition either: it observes
that the absence is a declared generator the type map `onValues` need not respect.

Part 2: under the current `Hom`, preservation is imposed. The laundering morphism meets every existing
requirement yet is not absence-preserving (`preservation_is_imposed`), so a new premise is required. The minimal
premise is that `onValues` be a theory morphism, carrying generators to absences (`what_premise_would_be_needed`);
it is structural, not normative, importing no external standard.

Part 3: `Hom` is under-specified relative to levels. It is a type map, correct for bare classifications where
`onValues` is unconstrained, but a level declares its absence as a generator, and a theory morphism would
respect it (`hom_versus_theory_morphism`). So absence-preservation is not an imported ethical standard but a
correction of an under-specified morphism, which answers the objection only if level-objects are granted theory
morphisms; taking `Hom` as the intended morphism for bare classifications, it remains imposed. Not chosen here.
Nothing is resolved. -/

end Chiralogy.DerivePreservation
