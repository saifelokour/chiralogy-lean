import Chiralogy

/-! # Experiment: does the framework have two categories?

`Obj` is a bare classification and `Hom` a map of value types; the kernel results (hole, center, payload) live
there and mention no declared grounds. A level carries more: which values are absences. Test whether levels
form their own category, carrying the declaration as data, and how it relates to `Obj`. Do not modify `Obj` or
`Hom`. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy CategoryTheory

namespace Chiralogy.TwoCategories

/-! ## Part 1: is there a level category?

The declaration is carried as data, an absence predicate on `B`, so `LevelObj` is a genuinely different object,
not `Obj` with a side condition. -/

/-- An object carrying a classification together with its declared grounds. -/
structure LevelObj where
  X : Type
  B : Type
  classify : X → X → B
  absent : B → Prop

/-- A morphism carrying declared grounds to declared grounds, with `preserves` still holding. -/
@[ext] structure LevelHom (S T : LevelObj) where
  onCarrier : S.X → T.X
  onValues : S.B → T.B
  preserves : ∀ x y, onValues (S.classify x y) = T.classify (onCarrier x) (onCarrier y)
  respects : ∀ v, S.absent v → T.absent (onValues v)

/-- The identity level-morphism. -/
def LevelHom.id (S : LevelObj) : LevelHom S S := ⟨_root_.id, _root_.id, fun _ _ => rfl, fun _ h => h⟩

/-- Composition of level-morphisms. -/
def LevelHom.comp {S T U : LevelObj} (F : LevelHom S T) (G : LevelHom T U) : LevelHom S U :=
  ⟨G.onCarrier ∘ F.onCarrier, G.onValues ∘ F.onValues,
   fun x y => by simp only [Function.comp_apply]; rw [F.preserves x y, G.preserves (F.onCarrier x) (F.onCarrier y)],
   fun v h => G.respects _ (F.respects v h)⟩

/-- **Levels form a category.** Identities respect any declaration and composition of ground-respecting maps is
ground-respecting; with the underlying `Hom` laws (as in `Obj`) `LevelObj` is a category. Since it carries
`absent` as data, it is a genuine second category, not a subcategory of `Obj`. -/
theorem level_category {S T U : LevelObj} (F : LevelHom S T) (G : LevelHom T U) :
    (∀ v, S.absent v → S.absent ((LevelHom.id S).onValues v))
    ∧ (∀ v, S.absent v → U.absent ((LevelHom.comp F G).onValues v)) :=
  ⟨fun _ h => h, fun v h => G.respects _ (F.respects v h)⟩

/-! ## Part 2: the forgetful functor -/

/-- Forget the declaration: a level to a bare classification. -/
def forget (L : LevelObj) : Obj := ⟨L.X, L.B, L.classify⟩

/-- Forget on morphisms: drop `respects`. -/
def forgetHom {S T : LevelObj} (F : LevelHom S T) : Hom (forget S) (forget T) :=
  ⟨F.onCarrier, F.onValues, F.preserves⟩

/-- **Forgetting the declaration is a functor.** It sends the identity to the identity and a composite to the
composite of the images: `forgetHom (id)` has `onValues = id`, and `forgetHom (F ∘ G)` composes the images'
`onValues` and `onCarrier`, which is exactly `forgetHom F ≫ forgetHom G` in `Obj`. -/
theorem forget_the_declaration {S T U : LevelObj} (F : LevelHom S T) (G : LevelHom T U) :
    ((forgetHom (LevelHom.id S)).onValues = _root_.id)
    ∧ ((forgetHom (LevelHom.comp F G)).onValues = (forgetHom G).onValues ∘ (forgetHom F).onValues)
    ∧ ((forgetHom (LevelHom.comp F G)).onCarrier = (forgetHom G).onCarrier ∘ (forgetHom F).onCarrier) :=
  ⟨rfl, rfl, rfl⟩

/-- A partial classification, declared two ways. -/
def sampleClassify : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none
def levelA : LevelObj := ⟨Fin 2, Option Bool, sampleClassify, fun v => v = none⟩
def levelB : LevelObj := ⟨Fin 2, Option Bool, sampleClassify, fun _ => True⟩

/-- **Forgetting loses the reason count.** Two levels with the same classification but different declarations
forget to the same bare object, so the ground data, and with it the reason count, the closeable family, and the
permitted lattice, is not recoverable from the image. -/
theorem forgetting_loses_the_reason_count :
    forget levelA = forget levelB
    ∧ (¬ levelA.absent (some true))
    ∧ levelB.absent (some true) :=
  ⟨rfl, by simp [levelA], trivial⟩

/-! ## Part 3: adjoints -/

/-- The free declaration: declare nothing a ground. -/
def freeDeclare (o : Obj) : LevelObj := ⟨o.X, o.B, o.classify, fun _ => False⟩

/-- The cofree declaration: declare everything a ground. -/
def cofreeDeclare (o : Obj) : LevelObj := ⟨o.X, o.B, o.classify, fun _ => True⟩

/-- **The free declaration is a left adjoint.** For every `Hom o (forget L)` there is a unique `LevelHom`
`freeDeclare o ⟶ L` with the same underlying data: `respects` is vacuous (nothing is a ground), so the universal
property holds. Declaring nothing is free. -/
theorem free_declaration (o : Obj) (L : LevelObj) (ψ : Hom o (forget L)) :
    ∃! φ : LevelHom (freeDeclare o) L, φ.onCarrier = ψ.onCarrier ∧ φ.onValues = ψ.onValues := by
  refine ⟨⟨ψ.onCarrier, ψ.onValues, ψ.preserves, fun _ h => h.elim⟩, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨oc, ov, p, r⟩ ⟨hc, hv⟩; subst hc; subst hv; rfl

/-- **The cofree declaration is a right adjoint.** For every `Hom (forget L) o` there is a unique `LevelHom`
`L ⟶ cofreeDeclare o` with the same underlying data: `respects` is automatic (everything is a ground). Declaring
everything is cofree. So forgetting has both adjoints, an adjoint triple. -/
theorem cofree_declaration (L : LevelObj) (o : Obj) (ψ : Hom (forget L) o) :
    ∃! φ : LevelHom L (cofreeDeclare o), φ.onCarrier = ψ.onCarrier ∧ φ.onValues = ψ.onValues := by
  refine ⟨⟨ψ.onCarrier, ψ.onValues, ψ.preserves, fun _ _ => trivial⟩, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨oc, ov, p, r⟩ ⟨hc, hv⟩; subst hc; subst hv; rfl

/-- **What the adjoints say.** Both adjoints exist and are the extreme declarations, nothing a ground (free) and
everything a ground (cofree). An actual level declares some values grounds and not others, neither free nor
cofree, so its declaration is genuine data not determined by the classification; the two categories are related
by the adjoint triple, forgetting in the middle. -/
theorem what_the_adjoints_say :
    (∀ o : Obj, (freeDeclare o).absent = fun _ => False)
    ∧ (∀ o : Obj, (cofreeDeclare o).absent = fun _ => True)
    ∧ (¬ levelA.absent (some true))
    ∧ levelA.absent none :=
  ⟨fun _ => rfl, fun _ => rfl, by simp [levelA], rfl⟩

/-! ## Part 4: what this reframes -/

/-- **Which results live where.** The kernel facts quantify a bare classification and belong to `Obj`, here the
hole transporting to any distinction space; the ground facts require a declaration and belong to levels, here
that a level's absences are the range of its nullary generators. -/
theorem which_results_live_where :
    (∀ (X B : Type) (g : B → B), (∀ b, g b ≠ b) → ∀ c : X → X → B, ¬ Function.Surjective c)
    ∧ (∀ v : Option Bool, v = none ↔ ∃ u : Unit, failMaybe u = v) :=
  ⟨fun _ _ _ hg c => hole_transports hg c, reasons_are_nullary_generators.2⟩

/-- **Reason-structure transport is untested against morphisms.** A morphism of levels now exists, so whether
the reason count, closeable family, or permitted lattice transports across a `LevelHom` can be tested; it is not
tested here, an open question. -/
theorem reason_structure_untested_against_morphisms :
    Nonempty (LevelHom levelA levelA) :=
  ⟨LevelHom.id levelA⟩

/-! ## The verdicts

Part 1: levels form a category, and a second one, not a subcategory. `LevelObj` carries the declaration as data
(the `absent` field), so its objects are genuinely richer than `Obj`; identities and composition respect
declarations (`level_category`), so with the underlying `Hom` laws it is a category. The gate is met: the
declaration is data, not a side condition on morphisms between `Obj`s.

Part 2: forgetting the declaration is a functor to `Obj` (`forget_the_declaration`), and it loses the ground
data: two levels differing only in their declaration forget to the same object, so the reason count, closeable
family, and permitted lattice are not recoverable from the image (`forgetting_loses_the_reason_count`).

Part 3: both adjoints exist. The free declaration (nothing a ground) is a left adjoint (`free_declaration`) and
the cofree (everything a ground) a right adjoint (`cofree_declaration`), each because `respects` is vacuous at
its extreme, an adjoint triple around forgetting. What they say (`what_the_adjoints_say`): the extremes are
determined by the classification, but an actual level declares some grounds and not others, neither free nor
cofree, so its declaration is genuine data; the categories are related only by forgetting.

Part 4: the reframing is substantive because Part 1 gives a genuine second category. Kernel facts (hole,
transport, payload) quantify a classification and live in `Obj`; ground facts (reasons, closeable family,
lattice) require a declaration and live in levels (`which_results_live_where`). And a new question opens: whether
reason-structure transports across a level morphism, untestable before because no such morphism existed, now
testable and here left open (`reason_structure_untested_against_morphisms`). Nothing is resolved. -/

end Chiralogy.TwoCategories
