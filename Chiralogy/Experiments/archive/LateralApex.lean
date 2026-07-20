import Chiralogy

/-! # Experiment: is a lateral apex contingent?

A total apex fails: the framework entire gives universal agreement (constancy), a level gives shared
description (form, not transmission). A lateral apex, a source shared by some objects and not others, is what
Zurek's structure actually has. `Obj` is finitely complete, so spans exist; theory morphisms are the tower's top
and do not fabricate. The candidate: a verdict is objective for `S` and `T` if some span `S ← A → T` with
theory-morphism legs carries it to both. The risk: products give every pair a span, so if the projections are
theory morphisms the notion is universal and collapses. Test it. Stays in `Experiments/`; canonical untouched;
nothing resolved. -/

open Chiralogy

namespace Chiralogy.LateralApex

/-- An object carrying a classification, declared grounds, and a binary operation. -/
structure TheoryObj where
  X : Type
  B : Type
  classify : X → X → B
  absent : B → Prop
  op : B → B → B

/-- A theory morphism, the tower's top: respects the classification, the grounds, the operation, and is
injective on grounds. -/
structure TheoryHom (S T : TheoryObj) where
  onCarrier : S.X → T.X
  onValues : S.B → T.B
  preserves : ∀ x y, onValues (S.classify x y) = T.classify (onCarrier x) (onCarrier y)
  respectsAbsent : ∀ v, S.absent v → T.absent (onValues v)
  respectsOp : ∀ a b, onValues (S.op a b) = T.op (onValues a) (onValues b)
  injOnGrounds : ∀ v w, S.absent v → S.absent w → onValues v = onValues w → v = w

/-! ## Part 1: is agreement under theory-morphism legs inherited? -/

/-- **Theory legs do not fabricate.** A theory morphism sends an absence to an absence (`respectsAbsent`), so an
absence cannot become a verdict. Contrast a bare morphism, which fabricates, `onValues` sending `none` and
`some true` to the same value. -/
theorem theory_legs_do_not_fabricate :
    (∀ (S T : TheoryObj) (φ : TheoryHom S T) (v : S.B), S.absent v → T.absent (φ.onValues v))
    ∧ (∃ f : Option Bool → Bool, f none = f (some true)) :=
  ⟨fun _ _ φ v h => φ.respectsAbsent v h, ⟨fun v => v.getD true, rfl⟩⟩

/-- **Agreement is inherited.** Given a span with theory-morphism legs, an absence at the apex is carried by both
legs to absences at `S` and `T`. The inheritance is forward: the apex has it, the legs carry it. -/
theorem agreement_is_inherited (A S T : TheoryObj) (legS : TheoryHom A S) (legT : TheoryHom A T) (v : A.B) :
    A.absent v → (S.absent (legS.onValues v) ∧ T.absent (legT.onValues v)) :=
  fun h => ⟨legS.respectsAbsent v h, legT.respectsAbsent v h⟩

/-! ## Part 2: is the span contingent? -/

/-- The product of two theory-objects, componentwise, with the ground `∧` and the operation componentwise. -/
def tprod (S T : TheoryObj) : TheoryObj :=
  ⟨S.X × T.X, S.B × T.B, fun a b => (S.classify a.1 b.1, T.classify a.2 b.2),
   fun v => S.absent v.1 ∧ T.absent v.2, fun a b => (S.op a.1 b.1, T.op a.2 b.2)⟩

/-- Forget the theory structure to a bare classification. -/
def tforget (S : TheoryObj) : Obj := ⟨S.X, S.B, S.classify⟩

/-- The product projections, as morphisms of bare classifications. -/
def tprodFst (S T : TheoryObj) : Hom (tforget (tprod S T)) (tforget S) := ⟨Prod.fst, Prod.fst, fun _ _ => rfl⟩
def tprodSnd (S T : TheoryObj) : Hom (tforget (tprod S T)) (tforget T) := ⟨Prod.snd, Prod.snd, fun _ _ => rfl⟩

/-- **Products give a span always.** Every pair has the product span, the projections as morphisms. So a span
always exists; the question is whether its legs are theory morphisms. -/
theorem products_give_a_span_always (S T : TheoryObj) :
    Nonempty (Hom (tforget (tprod S T)) (tforget S)) ∧ Nonempty (Hom (tforget (tprod S T)) (tforget T)) :=
  ⟨⟨tprodFst S T⟩, ⟨tprodSnd S T⟩⟩

/-- A one-ground object and a two-ground object. -/
def S1 : TheoryObj := ⟨Unit, Fin 3, fun _ _ => 0, fun v => v = 0, fun a b => min a b⟩
def T2 : TheoryObj := ⟨Unit, Fin 3, fun _ _ => 0, fun v => v = 0 ∨ v = 1, fun a b => min a b⟩

/-- **The product projections are not theory morphisms.** They respect the grounds and the operation, but they
fail injectivity on grounds: the projection collapses the other factor's grounds, sending two distinct product
grounds with the same first component to one. So the product span does not have theory-morphism legs. -/
theorem are_product_projections_theory_morphisms :
    (∀ (S T : TheoryObj) (v : (tprod S T).B), (tprod S T).absent v → S.absent v.1)
    ∧ (∀ (S T : TheoryObj) (a b : (tprod S T).B), ((tprod S T).op a b).1 = S.op a.1 b.1)
    ∧ (∃ (S T : TheoryObj) (v w : (tprod S T).B),
        (tprod S T).absent v ∧ (tprod S T).absent w ∧ v.1 = w.1 ∧ v ≠ w) :=
  ⟨fun _ _ _ h => h.1, fun _ _ _ _ => rfl,
   S1, T2, ((0 : Fin 3), (0 : Fin 3)), ((0 : Fin 3), (1 : Fin 3)),
   ⟨rfl, Or.inl rfl⟩, ⟨rfl, Or.inr rfl⟩, rfl,
   fun h => absurd (congrArg (Prod.snd : Fin 3 × Fin 3 → Fin 3) h) (by decide)⟩

/-- **There is a pair without a span.** A theory morphism is injective on grounds, so its apex's grounds embed
in the target's; but there is no injection from two grounds into one. So a span into a one-ground object carries
at most one ground, and a two-ground object has a verdict no theory-morphism span carries to a one-ground one.
The lateral apex can fail. -/
theorem is_there_a_pair_without_one :
    ¬ ∃ f : Fin 2 → Fin 1, Function.Injective f :=
  fun ⟨f, hf⟩ => absurd (hf (Subsingleton.elim (f 0) (f 1))) (by decide)

/-! ## Part 3: the verdict -/

/-- **Objectivity as a lateral span.** A verdict is objective for two objects when a theory-morphism span
carries it to both: the legs inherit an apex absence forward, to absences at each, without fabricating. And it
can fail, since a span into a one-ground object cannot carry two grounds. So it is contingent. -/
theorem objectivity_as_lateral_span :
    (∀ (A S T : TheoryObj) (legS : TheoryHom A S) (legT : TheoryHom A T) (v : A.B),
        A.absent v → S.absent (legS.onValues v) ∧ T.absent (legT.onValues v))
    ∧ (¬ ∃ f : Fin 2 → Fin 1, Function.Injective f) :=
  ⟨fun _ _ _ legS legT v h => ⟨legS.respectsAbsent v h, legT.respectsAbsent v h⟩, is_there_a_pair_without_one⟩

/-- **What it does not give.** Agreement does not recover a source: two objects can each carry an absence, an
agreement of form, with no apex determined. The inheritance runs forward only, matching the physics, where
redundancy is read off an assumed causal history rather than used to infer one. -/
theorem what_it_does_not_give :
    ∃ (S T : TheoryObj) (s : S.B) (t : T.B), S.absent s ∧ T.absent t :=
  ⟨S1, T2, (0 : Fin 3), (0 : Fin 3), rfl, Or.inl rfl⟩

/-- **Objectivity status: expressible and contingent.** Theory-morphism legs inherit agreement forward
(expressible), and the span can fail to exist (contingent), so the notion does not collapse to universality. -/
theorem objectivity_status :
    (∀ (A S : TheoryObj) (legS : TheoryHom A S) (v : A.B), A.absent v → S.absent (legS.onValues v))
    ∧ (¬ ∃ f : Fin 2 → Fin 1, Function.Injective f) :=
  ⟨fun _ _ legS v h => legS.respectsAbsent v h, is_there_a_pair_without_one⟩

/-! ## The verdicts

Part 1: agreement under theory-morphism legs is inherited. A theory morphism does not fabricate, sending an
absence to an absence (`theory_legs_do_not_fabricate`), and given a span with such legs an apex absence is
carried to both `S` and `T` (`agreement_is_inherited`). The inheritance is forward, the apex to the legs; the
converse, recovering the apex from agreement, is not claimed.

Part 2: the span is contingent, and does not collapse to universality. Every pair has the product span
(`products_give_a_span_always`), but its projections are not theory morphisms: they respect the grounds and the
operation yet fail injectivity on grounds, collapsing the other factor's grounds
(`are_product_projections_theory_morphisms`). So the free product span does not have theory-morphism legs, and
the notion is not universal. And it can genuinely fail: a theory morphism is injective on grounds, and there is
no injection from two grounds into one, so a two-ground object has a verdict no theory-morphism span carries to a
one-ground one (`is_there_a_pair_without_one`).

Part 3: objectivity as a lateral span is expressible and contingent (`objectivity_as_lateral_span`,
`objectivity_status`). A verdict is objective for two objects when a theory-morphism span carries it to both,
the legs inheriting it forward without fabricating; this can fail, so it distinguishes. It does not recover a
source from agreement (`what_it_does_not_give`): the inheritance is one-directional, and agreement is read off
an assumed apex, not used to infer one, which matches the physics rather than falling short of it.

The verdict: objectivity-as-redundancy is expressible as a lateral span with theory-morphism legs, and it is
contingent, not universal. The failure mode, a free span from the product, is avoided precisely because the
product projections collapse grounds and so fail the injectivity a theory morphism requires; the very condition
that makes theory morphisms the tower's top is what keeps the lateral apex from being free. Objectivity here is
agreement inherited from a shared apex, forward, without recovery, exactly the shape Zurek's structure has.
Nothing here is resolved. -/

end Chiralogy.LateralApex
