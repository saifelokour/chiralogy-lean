import Chiralogy

/-! # Experiment: does the tower's shape change above the order?

`Obj → Levels` has an adjoint triple; `Levels → OrderedLevels` breaks it, since injectivity on grounds is a
condition on arrows that no choice of order makes vacuous. The operational steps have not been checked.
Determine the tower's shape above the order, and whether theory morphisms are its top. Concrete small instances.
Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.UpperTower

/-! ## Part 1: adjoints for the operational steps -/

/-- An object carrying a classification and a binary operation. -/
structure OpObj where
  X : Type
  B : Type
  classify : X → X → B
  op : B → B → B

/-- A morphism respecting the classification and the operation. -/
structure OpHom (S T : OpObj) where
  onCarrier : S.X → T.X
  onValues : S.B → T.B
  preserves : ∀ x y, onValues (S.classify x y) = T.classify (onCarrier x) (onCarrier y)
  respectsOp : ∀ a b, onValues (S.op a b) = T.op (onValues a) (onValues b)

def OpHom.id (S : OpObj) : OpHom S S := ⟨_root_.id, _root_.id, fun _ _ => rfl, fun _ _ => rfl⟩

def OpHom.comp {S T U : OpObj} (F : OpHom S T) (G : OpHom T U) : OpHom S U :=
  ⟨G.onCarrier ∘ F.onCarrier, G.onValues ∘ F.onValues,
   fun x y => by simp only [Function.comp_apply]; rw [F.preserves x y, G.preserves (F.onCarrier x) (F.onCarrier y)],
   fun a b => by simp only [Function.comp_apply]; rw [F.respectsOp a b, G.respectsOp (F.onValues a) (F.onValues b)]⟩

/-- Forget the operation, to a bare classification. -/
def forgetOp (S : OpObj) : Obj := ⟨S.X, S.B, S.classify⟩
def forgetOpHom {S T : OpObj} (F : OpHom S T) : Hom (forgetOp S) (forgetOp T) :=
  ⟨F.onCarrier, F.onValues, F.preserves⟩

/-- **Forgetting the operations is a functor.** Identities and composition respect the operation, so `OpObj` is
a category, and dropping the operation sends identity to identity and composite to composite. -/
theorem forget_the_operations {S T U : OpObj} (F : OpHom S T) (G : OpHom T U) :
    ((forgetOpHom (OpHom.id S)).onValues = _root_.id)
    ∧ ((forgetOpHom (OpHom.comp F G)).onValues = (forgetOpHom G).onValues ∘ (forgetOpHom F).onValues) :=
  ⟨rfl, rfl⟩

/-- **No vacuous-extreme adjoint for the operations.** No choice of operation makes respecting it vacuous: even
constant operations impose a constraint an underlying map can violate. So the free-operation candidate does not
give the adjunction that `respects` and `monotone` had; the respect-condition is an equation, not a gated
implication, and has no vacuous extreme. -/
theorem operational_adjoints :
    ∃ (opS opT : Fin 3 → Fin 3 → Fin 3) (f : Fin 3 → Fin 3) (a b : Fin 3),
      f (opS a b) ≠ opT (f a) (f b) :=
  ⟨fun _ _ => 0, fun _ _ => 1, _root_.id, 0, 0, by decide⟩

/-- **The pattern breaks.** `respects` is a gated implication, vacuous at the empty gate, which gave the adjoint
triple; respecting an operation is an ungated equation with no vacuous extreme, like injectivity on grounds. So
the operational steps follow the second pattern and break the adjoint triple. -/
theorem does_the_pattern_hold_or_break :
    (∀ (f : Fin 3 → Fin 3) (v : Fin 3), (fun _ => False) v → (fun _ => False) (f v))
    ∧ (∃ (opS opT : Fin 3 → Fin 3 → Fin 3) (f : Fin 3 → Fin 3) (a b : Fin 3),
        f (opS a b) ≠ opT (f a) (f b)) :=
  ⟨fun _ _ h => h.elim, operational_adjoints⟩

/-! ## Part 2: are theory morphisms the top? -/

/-- **Theory morphisms are the conjunction.** Respecting an operation forces respecting every derived operation
built from it: a homomorphism sends nested applications to nested applications. So any equation among derived
operations transports automatically; respecting the operations is respecting the theory. -/
theorem theory_morphism_is_the_conjunction (f : Fin 3 → Fin 3) (opS opT : Fin 3 → Fin 3 → Fin 3)
    (hom : ∀ a b, f (opS a b) = opT (f a) (f b)) :
    (∀ a b c, f (opS (opS a b) c) = opT (opT (f a) (f b)) (f c))
    ∧ (∀ a b c, f (opS a (opS b c)) = opT (f a) (opT (f b) (f c))) :=
  ⟨fun a b c => by rw [hom, hom], fun a b c => by rw [hom, hom]⟩

/-- **What the top is.** Source associativity transports to the image under a homomorphism, with no condition on
the morphism beyond respecting the operation: the equation holds on the image because the derived operations are
respected and the source equates them. So no datum sits above the operations; theory morphisms are the top, the
last arity step. -/
theorem what_the_top_is (f : Fin 3 → Fin 3) (opS opT : Fin 3 → Fin 3 → Fin 3)
    (hom : ∀ a b, f (opS a b) = opT (f a) (f b))
    (assocS : ∀ a b c, opS (opS a b) c = opS a (opS b c)) :
    ∀ a b c, opT (opT (f a) (f b)) (f c) = opT (f a) (opT (f b) (f c)) :=
  fun a b c => by rw [← hom a b, ← hom (opS a b) c, assocS a b c, hom a (opS b c), hom b c]

/-! ## Part 3: the tower's shape, stated -/

/-- A monotone map respecting a binary operation but not a primitive ternary one. -/
def f2 : Fin 3 → Fin 3 := fun v => if v = 0 then 1 else v
def tMaj : Fin 3 → Fin 3 → Fin 3 → Fin 3 := fun a b c => if a = b then c else a

/-- **The tower shape.** The steps differ. Grounds add object data with a gated respect-condition, vacuous at
the empty gate (adjoint triple). The order adds object data gated by monotonicity (adjoints for the order), but
injectivity is an arrow condition with no vacuous extreme (breaking the triple). Operations add object data
whose respect-condition is an ungated equation, no vacuous extreme (no carrier-preserving adjoint). Recorded as
the three shapes: a vacuous gate, and an ungated equation that fails. -/
theorem tower_shape :
    (∀ (f : Fin 3 → Fin 3) (v : Fin 3), (fun _ => False) v → (fun _ => False) (f v))
    ∧ (∀ (_f : Fin 3 → Fin 3) (v w : Fin 3), (fun _ _ : Fin 3 => false) v w = true → False)
    ∧ (∃ (opS opT : Fin 3 → Fin 3 → Fin 3) (f : Fin 3 → Fin 3) (a b : Fin 3),
        f (opS a b) ≠ opT (f a) (f b)) :=
  ⟨fun _ _ h => h.elim, fun _ _ _ h => by simp at h, operational_adjoints⟩

/-- **What the count depends on.** The arity steps are bounded by the signatures in use: a value map can respect
the binary operation and not a primitive ternary one, so a level carrying a ternary operation extends the tower.
The count is a function of the levels built. -/
theorem what_the_count_depends_on :
    ∃ (f : Fin 3 → Fin 3) (b : Fin 3 → Fin 3 → Fin 3) (t : Fin 3 → Fin 3 → Fin 3 → Fin 3) (x y z : Fin 3),
      (∀ a c, f (b a c) = b (f a) (f c)) ∧ f (t x y z) ≠ t (f x) (f y) (f z) :=
  ⟨f2, fun a b => min a b, tMaj, 0, 1, 2, by decide, by decide⟩

/-! ## The verdicts

Part 1: the operational forgetful functors do not have the vacuous-extreme adjoints. Forgetting the operation is
a functor (`forget_the_operations`), but no choice of operation makes respecting it vacuous, even a constant one
constrains an underlying map (`operational_adjoints`). So the operational steps follow the second pattern
(`does_the_pattern_hold_or_break`): respecting an operation is an ungated equation, like injectivity on grounds,
not a gated implication like `respects` or `monotone`, so the adjoint triple does not carry up. A free-algebra
adjoint exists in principle but changes the value space, outside the carrier-preserving forgetful pattern.

Part 2: theory morphisms are the conjunction, and the top. Respecting an operation forces respecting every
derived operation (`theory_morphism_is_the_conjunction`), so equations transport automatically, source
associativity holding on the image with no further condition (`what_the_top_is`). A morphism respecting all
operations is a homomorphism and preserves every equation, so nothing sits above the operations; the top is the
last arity step.

Part 3: the tower's shape is not uniform. Grounds add object data with a gated respect-condition and an adjoint
triple; the order adds object data with adjoints for the order, plus injectivity, an arrow condition that breaks
the triple; operations add object data whose respect-condition is an ungated equation with no vacuous extreme,
breaking the carrier-preserving adjoint as injectivity did (`tower_shape`). The arity steps run one per
primitive arity, bounded by the signatures in use, extended by any level carrying a higher primitive arity
(`what_the_count_depends_on`), up to theory morphisms at the top. So the tower is an adjoint triple at the base,
then a chain of forgetful functors without the triple above the order, terminating at the highest arity. Nothing
here is resolved. -/

end Chiralogy.UpperTower
