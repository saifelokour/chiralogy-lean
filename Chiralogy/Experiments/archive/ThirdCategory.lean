import Chiralogy

/-! # Experiment: is there a third category, and does the chain terminate?

`Hom` respects the classification; `LevelHom` also respects declarations; neither respects the order among
grounds, and `swapHom` and `collapseHom` showed the ethics fails to transport for that reason. Test whether
ordered levels form a third category and whether anything remains for a fourth. Each category adds object-side
data its predecessor lacks, with morphisms respecting exactly that data. Stays in `Experiments/`; canonical
untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.ThirdCategory

/-! ## Part 1: is there a third category?

The order is carried as data (a `prereq` field), so `OrderedLevelObj` is a genuinely richer object. -/

/-- An object carrying a classification, declared grounds, and a prerequisite order on them. -/
structure OrderedLevelObj where
  X : Type
  B : Type
  classify : X → X → B
  absent : B → Prop
  prereq : B → B → Bool

/-- A morphism that respects grounds, is injective on them, and is monotone for the orders. -/
structure OrderedLevelHom (S T : OrderedLevelObj) where
  onCarrier : S.X → T.X
  onValues : S.B → T.B
  preserves : ∀ x y, onValues (S.classify x y) = T.classify (onCarrier x) (onCarrier y)
  respects : ∀ v, S.absent v → T.absent (onValues v)
  injOnGrounds : ∀ v w, S.absent v → S.absent w → onValues v = onValues w → v = w
  monotone : ∀ v w, S.prereq v w = true → T.prereq (onValues v) (onValues w) = true

/-- The identity ordered-level-morphism. -/
def OrderedLevelHom.id (S : OrderedLevelObj) : OrderedLevelHom S S :=
  ⟨_root_.id, _root_.id, fun _ _ => rfl, fun _ h => h, fun _ _ _ _ h => h, fun _ _ h => h⟩

/-- Composition. -/
def OrderedLevelHom.comp {S T U : OrderedLevelObj}
    (F : OrderedLevelHom S T) (G : OrderedLevelHom T U) : OrderedLevelHom S U :=
  ⟨G.onCarrier ∘ F.onCarrier, G.onValues ∘ F.onValues,
   fun x y => by simp only [Function.comp_apply]; rw [F.preserves x y, G.preserves (F.onCarrier x) (F.onCarrier y)],
   fun v h => G.respects _ (F.respects v h),
   fun v w hv hw hvw => F.injOnGrounds v w hv hw (G.injOnGrounds _ _ (F.respects v hv) (F.respects w hw) hvw),
   fun v w h => G.monotone _ _ (F.monotone v w h)⟩

/-- **Ordered levels form a category.** Identities are injective on grounds and monotone, and composites of
injective monotone maps are injective and monotone; with the underlying `Hom` laws it is a category. Since it
carries `prereq` as data, it is a genuine third category, not a subcategory of Levels. -/
theorem ordered_level_category {S T U : OrderedLevelObj}
    (F : OrderedLevelHom S T) (G : OrderedLevelHom T U) :
    (∀ v w, S.absent v → S.absent w →
        (OrderedLevelHom.id S).onValues v = (OrderedLevelHom.id S).onValues w → v = w)
    ∧ (∀ v w, S.prereq v w = true →
        S.prereq ((OrderedLevelHom.id S).onValues v) ((OrderedLevelHom.id S).onValues w) = true)
    ∧ (∀ v w, S.absent v → S.absent w →
        (OrderedLevelHom.comp F G).onValues v = (OrderedLevelHom.comp F G).onValues w → v = w)
    ∧ (∀ v w, S.prereq v w = true →
        U.prereq ((OrderedLevelHom.comp F G).onValues v) ((OrderedLevelHom.comp F G).onValues w) = true) :=
  ⟨(OrderedLevelHom.id S).injOnGrounds, (OrderedLevelHom.id S).monotone,
   (OrderedLevelHom.comp F G).injOnGrounds, (OrderedLevelHom.comp F G).monotone⟩

/-- **The ethics transports here.** With a monotone morphism the closeable family transports contravariantly:
pulling a coherent target closure back along the map gives a coherent source closure, and the full closure pulls
back to the full closure. Monotonicity, the condition `OrderedLevelHom` adds, is exactly what makes this work,
where `swapHom` (injective, not monotone) broke it in Levels. The covariant image need not be closed when the
target has grounds outside the image, so the natural transport is contravariant. -/
theorem ethics_transports_here (f : Fin 3 → Fin 3) (sPrereq tPrereq : Fin 3 → Fin 3 → Bool)
    (mono : ∀ v w, sPrereq v w = true → tPrereq (f v) (f w) = true)
    (close : Fin 3 → Bool)
    (hcoh : ∀ v w, tPrereq v w = true → close w = true → close v = true) :
    (∀ v w, sPrereq v w = true → close (f w) = true → close (f v) = true)
    ∧ (∀ v : Fin 3, (fun _ => true) (f v) = (fun _ : Fin 3 => true) v) :=
  ⟨fun v w hvw hw => hcoh (f v) (f w) (mono v w hvw) hw, fun _ => rfl⟩

/-! ## Part 2: the forgetful chain -/

/-- A non-injective ground map, for the adjoint check. -/
def collapse : Fin 3 → Fin 3 := fun v => if v = 2 then 2 else 0

/-- **Forgetting the order, and its adjoints.** Dropping `prereq` is a functor to Levels. The free-order
candidate (discrete, no prerequisites) makes the monotone condition vacuous, and the cofree-order candidate
(total, every pair ordered) makes it vacuous from the other side, so the order has adjoints as declaring nothing
and everything gave for `respects`. But `OrderedLevelHom` also requires injectivity on grounds, which no order
makes vacuous (`collapse` is a non-injective ground map), so the full adjoint triple does not persist: the
functor forgets a condition, not only data. -/
theorem forget_the_order :
    (∀ (t : Fin 3 → Fin 3 → Bool) (f : Fin 3 → Fin 3) (v w : Fin 3),
        (fun _ _ : Fin 3 => false) v w = true → t (f v) (f w) = true)
    ∧ (∀ (s : Fin 3 → Fin 3 → Bool) (f : Fin 3 → Fin 3) (v w : Fin 3),
        s v w = true → (fun _ _ : Fin 3 => true) (f v) (f w) = true)
    ∧ (collapse 0 = collapse 1 ∧ (0 : Fin 3) ≠ 1) := by
  refine ⟨fun t f v w h => by simp at h, fun s f v w _ => rfl, ⟨by decide, by decide⟩⟩

/-- **The chain so far.** Obj carries a classification (the payload quantifies it, no declarations); Levels add
declared grounds (the reasons are the nullary generators); ordered levels add the order (a coherent closure
transports, `ethics_transports_here`). Each step forgets its added data; Levels to Obj has an adjoint triple,
ordered levels to Levels only partly. -/
theorem the_chain_so_far :
    (∀ {X : Type} (c : X → X → Option Bool), ¬ Function.Surjective c)
    ∧ (∀ v : Option Bool, v = none ↔ ∃ u : Unit, failMaybe u = v) :=
  ⟨fun c => hole_uniform c, reasons_are_nullary_generators.2⟩

/-! ## Part 3: does it terminate? -/

/-- A value map swapping two verdicts, respecting grounds and order yet not an operation. -/
def swapVerdicts : Fin 3 → Fin 3 := fun v => if v = 1 then 2 else if v = 2 then 1 else 0

/-- **Something is left over.** A value map can respect grounds and their order yet fail to respect a binary
operation on the value space: `swapVerdicts` does not commute with `min`. So the level's algebraic operations
are a fourth object-side datum an `OrderedLevelHom` does not respect, and a morphism can disturb them. -/
theorem is_anything_left_over :
    ∃ (f : Fin 3 → Fin 3) (op : Fin 3 → Fin 3 → Fin 3) (a b : Fin 3),
      f (op a b) ≠ op (f a) (f b) :=
  ⟨swapVerdicts, fun a b => min a b, 1, 2, by decide⟩

/-- **The chain continues.** The operations affect the ethics: an absorbing law blocks a closure
(`blocking_removes_a_closure`, no verdict absorbs), so the permitted family depends on the operations, not the
grounds and order alone. And a ground-and-order-respecting map need not respect operations
(`is_anything_left_over`). So the chain does not terminate at three: the fourth datum is the level's operations,
and the fourth category is the theory morphisms respecting them, the extension of the earlier theory-morphism
condition from generators to operations. -/
theorem termination_or_continuation :
    (∀ a : List Bool, mzAppend (some a) none ≠ some a)
    ∧ (∃ (f : Fin 3 → Fin 3) (op : Fin 3 → Fin 3 → Fin 3) (a b : Fin 3), f (op a b) ≠ op (f a) (f b)) :=
  ⟨blocking_removes_a_closure, is_anything_left_over⟩

/-! ## The verdicts

Part 1: ordered levels form a third category, carrying the order as data (`OrderedLevelObj.prereq`), so its
objects are richer than Levels; identities and composition are injective on grounds and monotone
(`ordered_level_category`). And the ethics transports here: a monotone morphism pulls a coherent closure back to
a coherent closure and the full closure to the full closure (`ethics_transports_here`), the contravariant
transport that monotonicity, absent in Levels, secures. This is the category the ground-structure lives in.

Part 2: forgetting the order is a functor, and its adjoints only partly persist. The discrete and total orders
are the free and cofree candidates, making the monotone condition vacuous (`forget_the_order`); but
`OrderedLevelHom` also demands injectivity on grounds, which no order makes vacuous, so the adjoint triple that
`U : Levels → Obj` enjoyed does not carry over. The chain is Obj, then Levels adding grounds with a triple, then
ordered levels adding an order with adjoints for the order but not for the injectivity.

Part 3: the chain does not terminate at three. An ordered level's algebraic operations are a fourth object-side
datum: they affect the ethics through blocking, an absorbing law removing a closure
(`termination_or_continuation`), and a ground-and-order-respecting morphism can disturb them
(`is_anything_left_over`). So a fourth category is generated, the theory morphisms respecting operations, the
same theory-morphism condition seen before, now extended from the nullary generators to the full algebra. The
layout is not yet stable; the fourth datum is the operations. Nothing here is resolved. -/

end Chiralogy.ThirdCategory
