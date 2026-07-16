import Mathlib.CategoryTheory.Category.Basic

/-! # The category `Autology`

An object is a self-classification `(X, B, c)`; a morphism preserves it. This is the ambient category
whose structural absences are the kernel. -/

namespace Autology

open CategoryTheory

/-- An object: a carrier `X`, a distinction space `B`, and a self-classification `c : X → X → B`. -/
structure Obj where
  X : Type
  B : Type
  classify : X → X → B

/-- A morphism preserves self-classification. -/
@[ext]
structure Hom (S T : Obj) where
  onCarrier : S.X → T.X
  onValues : S.B → T.B
  preserves : ∀ x y, onValues (S.classify x y) = T.classify (onCarrier x) (onCarrier y)

/-- `Autology` is a category; identity and composition are inherited from `Set`. -/
instance : Category.{0} Obj where
  Hom S T := Hom S T
  id S := { onCarrier := id, onValues := id, preserves := fun _ _ => rfl }
  comp {_ _ _} F G :=
    { onCarrier := G.onCarrier ∘ F.onCarrier
      onValues := G.onValues ∘ F.onValues
      preserves := fun x y => by
        simp only [Function.comp_apply]
        rw [F.preserves x y, G.preserves (F.onCarrier x) (F.onCarrier y)] }
  id_comp _ := by ext <;> rfl
  comp_id _ := by ext <;> rfl
  assoc _ _ _ := by ext <;> rfl

end Autology
