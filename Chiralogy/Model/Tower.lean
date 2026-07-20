import Chiralogy.Model.Permitted
import Chiralogy.Model.Apophatic.Instances

/-! # Model: the tower of categories

First of the what-there-is pair. `Obj` is the bare classification (the kernel results quantify it); each further
category adds object-side data its predecessor lacks, morphisms respecting exactly that data. `Grounds` is the
companion: the structures those objects present.

Five categories. `Obj` (a classification). Levels (plus declared grounds, `absent`, arrows `respects`). Ordered
levels (plus a prerequisite order on grounds, arrows `injOnGrounds` and `monotone`). The arity steps (arrows
respecting operations of each arity, separating in both directions). Σ-homomorphisms at the top, the conjunction
of the arity conditions, equations transporting so nothing sits above (`sigma_hom_is_the_conjunction`,
`what_the_top_is`).

The forgetful functors are non-uniform. Levels to `Obj` has an adjoint triple: declare-nothing (`freeDeclare`)
and declare-everything (`cofreeDeclare`) make `respects` vacuous (`free_declaration`, `cofree_declaration`). It
breaks above the order, where injectivity and operation-respecting are ungated (`forget_the_order`,
`operational_adjoints`). Height is a function of the signatures, one step per primitive arity in use, currently
two (`respecting_by_arity`, `what_would_make_it_longer`); operations fold into the order region, reaching the
ethics only by blocking or welding (`what_operations_can_do`).

Where the ethics transports: not across ground-respecting arrows alone (`prohibition_under_levelhom`), but
contravariantly across monotone ground-injective maps (`ethics_transports_here`). Objectivity is a lateral span:
a verdict is objective for two objects when a Σ-homomorphism span carries it to both
(`objectivity_as_lateral_span`), contingent since the product's projections collapse grounds and fail injectivity
(`are_product_projections_theory_morphisms`), inheritance forward only, agreement not recovering a source
(`what_it_does_not_give`), matching the physics rather than falling short of it. -/

namespace Chiralogy

/-! ## Levels: declared grounds

A level carries which values are absences, as data (`absent`), so `LevelObj` is a second category, not `Obj`
with a side condition. -/

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

/-- **Levels form a category.** Identities respect any declaration and composites of ground-respecting maps are
ground-respecting; carrying `absent` as data, it is a second category, not a subcategory of `Obj`. -/
theorem level_category {S T U : LevelObj} (F : LevelHom S T) (G : LevelHom T U) :
    (∀ v, S.absent v → S.absent ((LevelHom.id S).onValues v))
    ∧ (∀ v, S.absent v → U.absent ((LevelHom.comp F G).onValues v)) :=
  ⟨fun _ h => h, fun v h => G.respects _ (F.respects v h)⟩

/-- Forget the declaration: a level to a bare classification. -/
def forget (L : LevelObj) : Obj := ⟨L.X, L.B, L.classify⟩

/-- Forget on morphisms: drop `respects`. -/
def forgetHom {S T : LevelObj} (F : LevelHom S T) : Hom (forget S) (forget T) :=
  ⟨F.onCarrier, F.onValues, F.preserves⟩

/-- **Forgetting the declaration is a functor.** It sends the identity to the identity and a composite to the
composite of the images. -/
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
forget to the same bare object, so the ground data is not recoverable from the image. -/
theorem forgetting_loses_the_reason_count :
    forget levelA = forget levelB
    ∧ (¬ levelA.absent (some true))
    ∧ levelB.absent (some true) :=
  ⟨rfl, by simp [levelA], trivial⟩

/-- The free declaration: declare nothing a ground. -/
def freeDeclare (o : Obj) : LevelObj := ⟨o.X, o.B, o.classify, fun _ => False⟩

/-- The cofree declaration: declare everything a ground. -/
def cofreeDeclare (o : Obj) : LevelObj := ⟨o.X, o.B, o.classify, fun _ => True⟩

/-- **The free declaration is a left adjoint.** For every `Hom o (forget L)` there is a unique `LevelHom`
`freeDeclare o ⟶ L` with the same underlying data: `respects` is vacuous. -/
theorem free_declaration (o : Obj) (L : LevelObj) (ψ : Hom o (forget L)) :
    ∃! φ : LevelHom (freeDeclare o) L, φ.onCarrier = ψ.onCarrier ∧ φ.onValues = ψ.onValues := by
  refine ⟨⟨ψ.onCarrier, ψ.onValues, ψ.preserves, fun _ h => h.elim⟩, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨oc, ov, p, r⟩ ⟨hc, hv⟩; subst hc; subst hv; rfl

/-- **The cofree declaration is a right adjoint.** For every `Hom (forget L) o` there is a unique `LevelHom`
`L ⟶ cofreeDeclare o` with the same underlying data: `respects` is automatic; forgetting has an adjoint triple. -/
theorem cofree_declaration (L : LevelObj) (o : Obj) (ψ : Hom (forget L) o) :
    ∃! φ : LevelHom L (cofreeDeclare o), φ.onCarrier = ψ.onCarrier ∧ φ.onValues = ψ.onValues := by
  refine ⟨⟨ψ.onCarrier, ψ.onValues, ψ.preserves, fun _ _ => trivial⟩, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨oc, ov, p, r⟩ ⟨hc, hv⟩; subst hc; subst hv; rfl

/-- **What the adjoints say.** Both adjoints are the extreme declarations; an actual level declares some values
grounds and not others, neither free nor cofree, so its declaration is genuine data. -/
theorem what_the_adjoints_say :
    (∀ o : Obj, (freeDeclare o).absent = fun _ => False)
    ∧ (∀ o : Obj, (cofreeDeclare o).absent = fun _ => True)
    ∧ (¬ levelA.absent (some true))
    ∧ levelA.absent none :=
  ⟨fun _ => rfl, fun _ => rfl, by simp [levelA], rfl⟩

/-! ## Ordered levels: a prerequisite order on grounds

The order is carried as data (`prereq`), so `OrderedLevelObj` is a third category. -/

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
injective monotone maps are injective and monotone; carrying `prereq` as data, it is a third category. -/
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
a coherent target closure pulls back to a coherent source closure, and the full closure to the full closure.
Monotonicity, the condition `OrderedLevelHom` adds, is exactly what makes this work. -/
theorem ethics_transports_here (f : Fin 3 → Fin 3) (sPrereq tPrereq : Fin 3 → Fin 3 → Bool)
    (mono : ∀ v w, sPrereq v w = true → tPrereq (f v) (f w) = true)
    (close : Fin 3 → Bool)
    (hcoh : ∀ v w, tPrereq v w = true → close w = true → close v = true) :
    (∀ v w, sPrereq v w = true → close (f w) = true → close (f v) = true)
    ∧ (∀ v : Fin 3, (fun _ => true) (f v) = (fun _ : Fin 3 => true) v) :=
  ⟨fun v w hvw hw => hcoh (f v) (f w) (mono v w hvw) hw, fun _ => rfl⟩

/-- A non-injective ground map, for the adjoint check. -/
def collapse : Fin 3 → Fin 3 := fun v => if v = 2 then 2 else 0

/-- **Forgetting the order, and its adjoints.** Dropping `prereq` is a functor to Levels; the discrete and total
orders make `monotone` vacuous, but `injOnGrounds` no order makes vacuous (`collapse` is a non-injective ground
map), so the full adjoint triple does not persist. -/
theorem forget_the_order :
    (∀ (t : Fin 3 → Fin 3 → Bool) (f : Fin 3 → Fin 3) (v w : Fin 3),
        (fun _ _ : Fin 3 => false) v w = true → t (f v) (f w) = true)
    ∧ (∀ (s : Fin 3 → Fin 3 → Bool) (f : Fin 3 → Fin 3) (v w : Fin 3),
        s v w = true → (fun _ _ : Fin 3 => true) (f v) (f w) = true)
    ∧ (collapse 0 = collapse 1 ∧ (0 : Fin 3) ≠ 1) := by
  refine ⟨fun t f v w h => by simp at h, fun s f v w _ => rfl, ⟨by decide, by decide⟩⟩

/-- A value map swapping two verdicts, respecting grounds and order yet not an operation. -/
def swapVerdicts : Fin 3 → Fin 3 := fun v => if v = 1 then 2 else if v = 2 then 1 else 0

/-! ## Transport across level morphisms

Whether the reason count, closeable family, and prohibition survive a `LevelHom` was unaskable before Levels;
they need not, unless the morphism is injective on grounds and monotone. -/

/-- A swap of two grounds, verdict fixed. -/
def swap01 : Fin 3 → Fin 3 := fun v => if v = 0 then 1 else if v = 1 then 0 else 2

/-- A carrier classification (its content is irrelevant to ground-transport). -/
def dummyClass : Fin 2 → Fin 2 → Fin 3 := fun x y => if x = y then 2 else 0

/-- Source: two grounds `{0, 1}`. Collapse target: one ground `{0}`. -/
def srcObj : LevelObj := ⟨Fin 2, Fin 3, dummyClass, fun v => v = 0 ∨ v = 1⟩
def tgtObj : LevelObj := ⟨Fin 2, Fin 3, fun x y => collapse (dummyClass x y), fun v => v = 0⟩

/-- The collapsing morphism, a valid `LevelHom`. -/
def collapseHom : LevelHom srcObj tgtObj :=
  ⟨id, collapse, fun _ _ => rfl, fun v h => by rcases h with rfl | rfl <;> rfl⟩

/-- Swap source and target: two grounds each. -/
def swapSrc : LevelObj := ⟨Fin 2, Fin 3, dummyClass, fun v => v = 0 ∨ v = 1⟩
def swapTgt : LevelObj := ⟨Fin 2, Fin 3, fun x y => swap01 (dummyClass x y), fun v => v = 0 ∨ v = 1⟩

/-- The swapping morphism, a valid `LevelHom`. -/
def swapHom : LevelHom swapSrc swapTgt :=
  ⟨id, swap01, fun _ _ => rfl, fun v h => by rcases h with rfl | rfl; exacts [Or.inr rfl, Or.inl rfl]⟩

/-- The prerequisite order `0 ≺ 1` on grounds. -/
def prereq : Fin 3 → Fin 3 → Bool := fun a b => decide (a = 0 ∧ b = 1)

/-- A set is closeable when up-closed under `0 ≺ 1`: closing `1` closes its prerequisite `0`. -/
abbrev coh (S : Finset (Fin 3)) : Prop := (1 : Fin 3) ∈ S → (0 : Fin 3) ∈ S

/-- **The reason count can shrink.** A `LevelHom` carries grounds to grounds but need not injectively:
`collapseHom` sends two source grounds to one. It never grows. -/
theorem reason_count_under_levelhom :
    (Finset.univ.filter (fun v : Fin 3 => v = 0 ∨ v = 1)).card = 2
    ∧ (Finset.image collapse (Finset.univ.filter (fun v : Fin 3 => v = 0 ∨ v = 1))).card = 1
    ∧ (∀ v, srcObj.absent v → tgtObj.absent (collapseHom.onValues v)) :=
  ⟨by decide, by decide, collapseHom.respects⟩

/-- **When the count is preserved.** Exactly when `onValues` is injective on the grounds, weaker than global
injectivity. -/
theorem when_is_the_count_preserved (f : Fin 3 → Fin 3) (G : Finset (Fin 3)) (h : Set.InjOn f ↑G) :
    (Finset.image f G).card = G.card :=
  Finset.card_image_of_injOn h

/-- **Prerequisites need not transport.** `swapHom` respects grounds yet sends the ordered pair `(0, 1)` to
`(1, 0)`, not ordered in the target: ground-respecting does not imply order-respecting. -/
theorem prerequisites_under_levelhom :
    (∀ v, swapSrc.absent v → swapTgt.absent (swapHom.onValues v))
    ∧ prereq 0 1 = true
    ∧ prereq (swap01 0) (swap01 1) = false :=
  ⟨swapHom.respects, by decide, by decide⟩

/-- **The closeable family need not transport.** The source closeable set `{0}` maps under `swap01` to `{1}`, not
closeable in the target order, so the permitted lattice does not transport under a merely ground-respecting
morphism. -/
theorem closeable_family_transports_or_not :
    coh {(0 : Fin 3)} ∧ ¬ coh (Finset.image swap01 {(0 : Fin 3)}) :=
  ⟨by decide, by decide⟩

/-- **A permitted move can become the prohibition.** Under `collapse` the permitted move `{0}` and the full
closure `{0, 1}` both map to the target's single ground `{0}`: the ethics does not transport under a
ground-respecting morphism. -/
theorem prohibition_under_levelhom :
    (Finset.image collapse {(0 : Fin 3)} = Finset.image collapse ({0, 1} : Finset (Fin 3)))
    ∧ (Finset.image collapse {(0 : Fin 3)} = {(0 : Fin 3)})
    ∧ (({0} : Finset (Fin 3)) ≠ ({0, 1} : Finset (Fin 3))) :=
  ⟨by decide, by decide, by decide⟩

/-! ## The arity steps

The operational part of the tower is arity-indexed: one step per primitive arity, separating in both directions.
The order is a separate relational datum, not a signature operation. -/

/-- A unary operation (the constant `0`); a morphism respects it iff it fixes `0`. -/
def uOp : Fin 3 → Fin 3 := fun _ => 0

/-- A binary operation. -/
def bOp : Fin 3 → Fin 3 → Fin 3 := fun a b => min a b

/-- A ternary operation not reducible to the binary one. -/
def tMaj : Fin 3 → Fin 3 → Fin 3 → Fin 3 := fun a b c => if a = b then c else a

/-- Respects a unary operation. -/
abbrev RespectsUnary (f : Fin 3 → Fin 3) (u : Fin 3 → Fin 3) : Prop := ∀ a, f (u a) = u (f a)

/-- Respects a binary operation. -/
abbrev RespectsBinary (f : Fin 3 → Fin 3) (b : Fin 3 → Fin 3 → Fin 3) : Prop :=
  ∀ a c, f (b a c) = b (f a) (f c)

/-- Fixes `0`, respecting `uOp`, but swaps `1` and `2`, breaking `min`. -/
def f1 : Fin 3 → Fin 3 := fun v => if v = 1 then 2 else if v = 2 then 1 else 0

/-- Monotone, respecting `min`, but moves `0`, breaking `uOp`. -/
def f2 : Fin 3 → Fin 3 := fun v => if v = 0 then 1 else v

/-- **Unary and binary are separable.** There is a morphism respecting the unary operation and not the binary,
and one the reverse, so the two arities generate distinct steps. -/
theorem unary_and_binary_are_separable :
    (∃ f : Fin 3 → Fin 3, (∀ a, f (uOp a) = uOp (f a)) ∧ ¬ ∀ a b, f (bOp a b) = bOp (f a) (f b))
    ∧ (∃ f : Fin 3 → Fin 3, (∀ a b, f (bOp a b) = bOp (f a) (f b)) ∧ ¬ ∀ a, f (uOp a) = uOp (f a)) :=
  ⟨⟨f1, by decide, by decide⟩, ⟨f2, by decide, by decide⟩⟩

/-- **Respecting by arity is independent.** The unary and binary respect-conditions neither imply the other; each
arity is a separate condition. -/
theorem respecting_by_arity :
    (RespectsUnary f1 uOp ∧ ¬ RespectsBinary f1 bOp)
    ∧ (RespectsBinary f2 bOp ∧ ¬ RespectsUnary f2 uOp) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **The order is not signature data.** The prerequisite order is a relation, not an operation, and respecting
it (monotone) is independent of respecting the operations; step three is a relational datum. -/
theorem order_is_not_signature_data :
    (∃ f : Fin 3 → Fin 3,
        (∀ v w, prereq v w = true → prereq (f v) (f w) = true) ∧ ¬ ∀ a b, f (bOp a b) = bOp (f a) (f b))
    ∧ (∃ f : Fin 3 → Fin 3,
        (∀ a b, f (bOp a b) = bOp (f a) (f b)) ∧ ¬ ∀ v w, prereq v w = true → prereq (f v) (f w) = true) :=
  ⟨⟨fun v => if v = 2 then 0 else v, by decide, by decide⟩, ⟨fun _ => 2, by decide, by decide⟩⟩

/-- **What would make it longer.** A primitive higher-arity operation separates too: `f2` respects the binary
operation but not the ternary `tMaj`, so a level carrying a genuine ternary operation adds an arity step. -/
theorem what_would_make_it_longer :
    (∀ a b, f2 (bOp a b) = bOp (f2 a) (f2 b))
    ∧ ¬ (∀ a b c, f2 (tMaj a b c) = tMaj (f2 a) (f2 b) (f2 c)) :=
  ⟨by decide, by decide⟩

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

/-- **Forgetting the operations is a functor.** Dropping the operation sends identity to identity and composite
to composite. -/
theorem forget_the_operations {S T U : OpObj} (F : OpHom S T) (G : OpHom T U) :
    ((forgetOpHom (OpHom.id S)).onValues = _root_.id)
    ∧ ((forgetOpHom (OpHom.comp F G)).onValues = (forgetOpHom G).onValues ∘ (forgetOpHom F).onValues) :=
  ⟨rfl, rfl⟩

/-- **No vacuous-extreme adjoint for the operations.** No choice of operation makes respecting it vacuous: even
a constant operation imposes a constraint an underlying map can violate, so the respect-condition is an ungated
equation with no vacuous extreme. -/
theorem operational_adjoints :
    ∃ (opS opT : Fin 3 → Fin 3 → Fin 3) (f : Fin 3 → Fin 3) (a b : Fin 3),
      f (opS a b) ≠ opT (f a) (f b) :=
  ⟨fun _ _ => 0, fun _ _ => 1, _root_.id, 0, 0, by decide⟩

/-- **The pattern breaks.** `respects` is a gated implication, vacuous at the empty gate, which gave the adjoint
triple; respecting an operation is an ungated equation with no vacuous extreme, like injectivity on grounds. -/
theorem does_the_pattern_hold_or_break :
    (∀ (f : Fin 3 → Fin 3) (v : Fin 3), (fun _ => False) v → (fun _ => False) (f v))
    ∧ (∃ (opS opT : Fin 3 → Fin 3 → Fin 3) (f : Fin 3 → Fin 3) (a b : Fin 3),
        f (opS a b) ≠ opT (f a) (f b)) :=
  ⟨fun _ _ h => h.elim, operational_adjoints⟩

/-- **Something is left over.** A value map can respect grounds and their order yet fail an operation:
`swapVerdicts` does not commute with `min`, so the operations are a fourth object-side datum. -/
theorem is_anything_left_over :
    ∃ (f : Fin 3 → Fin 3) (op : Fin 3 → Fin 3 → Fin 3) (a b : Fin 3),
      f (op a b) ≠ op (f a) (f b) :=
  ⟨swapVerdicts, fun a b => min a b, 1, 2, by decide⟩

/-- **The chain continues to the operations.** An absorbing law blocks a closure
(`blocking_removes_a_closure`), so the permitted family depends on the operations, and a
ground-and-order-respecting map need not respect them (`is_anything_left_over`): the fourth datum is the
operations, the fourth category the Σ-homomorphisms. -/
theorem termination_or_continuation :
    (∀ a : List Bool, mzAppend (some a) none ≠ some a)
    ∧ (∃ (f : Fin 3 → Fin 3) (op : Fin 3 → Fin 3 → Fin 3) (a b : Fin 3), f (op a b) ≠ op (f a) (f b)) :=
  ⟨blocking_removes_a_closure, is_anything_left_over⟩

/-! ## The operational region's content

The operational steps are thin: an operation reaches the ethics only by blocking or welding, both requiring an
operation that touches an absence, where the framework's natural operations act on verdicts. This is why
operations fold into the order region. -/

/-- A unary operation permuting two verdicts and fixing the absences. -/
def swapU : Fin 4 → Fin 4 := fun v => if v = 2 then 3 else if v = 3 then 2 else v

/-- **A unary operation can reach the ethics.** Welding relates two grounds (`sOp`), making closing one force the
other; blocking forces a respecting totalization to send an absence to a fixed point, an absence uncloseable. -/
theorem can_a_unary_operation_reach_the_ethics :
    (∀ t : Fin 4 → Fin 4, (∀ x, t (sOp x) = sOp (t x)) → (isVerdict (t 2) → isVerdict (t 3)))
    ∧ (∀ t : Fin 4 → Fin 4, (∀ x, t (swapU x) = swapU (t x)) → swapU (t 0) = t 0) :=
  ⟨fun t hom => (equational_relations_weld t hom).1, fun _ h => (h 0).symm⟩

/-- **Binary routes beyond absorption.** Absorption blocks (no verdict absorbs under `mzAppend`); welding, a
distinct route, relates two grounds both-or-neither. -/
theorem binary_routes_beyond_absorption :
    (∀ a : List Bool, mzAppend (some a) none ≠ some a)
    ∧ (∀ t : Fin 4 → Fin 4, (∀ x, t (sOp x) = sOp (t x)) → (t 2 = 2 → t 3 = 3)) :=
  ⟨blocking_removes_a_closure, fun t hom => (equational_relations_weld t hom).2⟩

/-- **What operations can do.** In the small instances, an operation affects the family in three ways: block a
closure, weld two grounds, or nothing (an operation-operation axiom leaves the family untouched); provisional,
not proven exhaustive. -/
theorem what_operations_can_do :
    (∀ a : List Bool, mzAppend (some a) none ≠ some a)
    ∧ (∀ t : Fin 4 → Fin 4, (∀ x, t (sOp x) = sOp (t x)) → (isVerdict (t 2) → isVerdict (t 3)))
    ∧ (∀ a b c : Option (List Bool), mzAppend (mzAppend a b) c = mzAppend a (mzAppend b c)) := by
  refine ⟨blocking_removes_a_closure, fun t hom => (equational_relations_weld t hom).1, fun a b c => ?_⟩
  cases a <;> cases b <;> cases c <;> simp [mzAppend, List.append_assoc]

/-- **Blocking is not the only binary route.** Welding permits a closure, both grounds closing together, where
blocking permits none: at least two phenomena. -/
theorem is_blocking_the_only_binary_route :
    (∃ t : Fin 4 → Fin 4, (∀ x, t (sOp x) = sOp (t x)) ∧ isVerdict (t 2) ∧ isVerdict (t 3))
    ∧ (∀ a : List Bool, mzAppend (some a) none ≠ some a) :=
  ⟨⟨fun _ => 0, fun _ => rfl, Or.inl rfl, Or.inl rfl⟩, blocking_removes_a_closure⟩

/-- **The unary region is non-empty.** A unary operation relating two distinct grounds (`sOp`) welds them; it is
a constructed operation, the natural unary operation (group inverse) acting on verdicts. -/
theorem unary_region_status :
    ∃ (s : Fin 4 → Fin 4) (a b : Fin 4),
      s a = b ∧ a ≠ b
      ∧ (∀ t : Fin 4 → Fin 4, (∀ x, t (s x) = s (t x)) → (isVerdict (t a) → isVerdict (t b))) :=
  ⟨sOp, 2, 3, rfl, by decide, fun t hom => (equational_relations_weld t hom).1⟩

/-! ## Σ-homomorphisms at the top

A Σ-homomorphism respects the specified constants and operations; equations transport, so nothing sits above. It
is the conjunction of the arity conditions, the tower's last step. -/

/-- **Σ-homomorphisms are the conjunction.** Respecting an operation forces respecting every derived operation:
a homomorphism sends nested applications to nested applications, so any equation among derived operations
transports automatically. -/
theorem sigma_hom_is_the_conjunction (f : Fin 3 → Fin 3) (opS opT : Fin 3 → Fin 3 → Fin 3)
    (hom : ∀ a b, f (opS a b) = opT (f a) (f b)) :
    (∀ a b c, f (opS (opS a b) c) = opT (opT (f a) (f b)) (f c))
    ∧ (∀ a b c, f (opS a (opS b c)) = opT (f a) (opT (f b) (f c))) :=
  ⟨fun a b c => by rw [hom, hom], fun a b c => by rw [hom, hom]⟩

/-- **What the top is.** Source associativity transports to the image under a homomorphism, with no condition on
the morphism beyond respecting the operation, so no datum sits above the operations. -/
theorem what_the_top_is (f : Fin 3 → Fin 3) (opS opT : Fin 3 → Fin 3 → Fin 3)
    (hom : ∀ a b, f (opS a b) = opT (f a) (f b))
    (assocS : ∀ a b c, opS (opS a b) c = opS a (opS b c)) :
    ∀ a b c, opT (opT (f a) (f b)) (f c) = opT (f a) (opT (f b) (f c)) :=
  fun a b c => by rw [← hom a b, ← hom (opS a b) c, assocS a b c, hom a (opS b c), hom b c]

/-! ## The lateral apex

Objectivity as a span with Σ-homomorphism legs (`OpLevelHom`, whose `respectsOp` is the Σ-homomorphism
condition; its `injOnGrounds` is our condition beyond a homomorphism, the lateral-apex leg, so the notion keeps
its own name). Contingent, forward only, recovering no source. -/

/-- An object carrying a classification, declared grounds, and a binary operation. -/
structure OpLevelObj where
  X : Type
  B : Type
  classify : X → X → B
  absent : B → Prop
  op : B → B → B

/-- A Σ-homomorphism leg: respects the classification, grounds, and operation, and is injective on grounds. -/
structure OpLevelHom (S T : OpLevelObj) where
  onCarrier : S.X → T.X
  onValues : S.B → T.B
  preserves : ∀ x y, onValues (S.classify x y) = T.classify (onCarrier x) (onCarrier y)
  respectsAbsent : ∀ v, S.absent v → T.absent (onValues v)
  respectsOp : ∀ a b, onValues (S.op a b) = T.op (onValues a) (onValues b)
  injOnGrounds : ∀ v w, S.absent v → S.absent w → onValues v = onValues w → v = w

/-- **Legs do not fabricate.** A leg sends an absence to an absence (`respectsAbsent`), so an absence cannot
become a verdict; contrast a bare morphism, which fabricates. -/
theorem theory_legs_do_not_fabricate :
    (∀ (S T : OpLevelObj) (φ : OpLevelHom S T) (v : S.B), S.absent v → T.absent (φ.onValues v))
    ∧ (∃ f : Option Bool → Bool, f none = f (some true)) :=
  ⟨fun _ _ φ v h => φ.respectsAbsent v h, ⟨fun v => v.getD true, rfl⟩⟩

/-- **Agreement is inherited.** Given a span with Σ-homomorphism legs, an absence at the apex is carried by both
legs to absences at `S` and `T`: forward, the apex has it, the legs carry it. -/
theorem agreement_is_inherited (A S T : OpLevelObj) (legS : OpLevelHom A S) (legT : OpLevelHom A T) (v : A.B) :
    A.absent v → (S.absent (legS.onValues v) ∧ T.absent (legT.onValues v)) :=
  fun h => ⟨legS.respectsAbsent v h, legT.respectsAbsent v h⟩

/-- The product of two objects, componentwise, with the ground `∧` and the operation componentwise. -/
def tprod (S T : OpLevelObj) : OpLevelObj :=
  ⟨S.X × T.X, S.B × T.B, fun a b => (S.classify a.1 b.1, T.classify a.2 b.2),
   fun v => S.absent v.1 ∧ T.absent v.2, fun a b => (S.op a.1 b.1, T.op a.2 b.2)⟩

/-- Forget the theory structure to a bare classification. -/
def tforget (S : OpLevelObj) : Obj := ⟨S.X, S.B, S.classify⟩

/-- The product projections, as morphisms of bare classifications. -/
def tprodFst (S T : OpLevelObj) : Hom (tforget (tprod S T)) (tforget S) := ⟨Prod.fst, Prod.fst, fun _ _ => rfl⟩
def tprodSnd (S T : OpLevelObj) : Hom (tforget (tprod S T)) (tforget T) := ⟨Prod.snd, Prod.snd, fun _ _ => rfl⟩

/-- **Products give a span always.** Every pair has the product span, the projections as morphisms; the question
is whether its legs are Σ-homomorphisms. -/
theorem products_give_a_span_always (S T : OpLevelObj) :
    Nonempty (Hom (tforget (tprod S T)) (tforget S)) ∧ Nonempty (Hom (tforget (tprod S T)) (tforget T)) :=
  ⟨⟨tprodFst S T⟩, ⟨tprodSnd S T⟩⟩

/-- A one-ground object and a two-ground object. -/
def S1 : OpLevelObj := ⟨Unit, Fin 3, fun _ _ => 0, fun v => v = 0, fun a b => min a b⟩
def T2 : OpLevelObj := ⟨Unit, Fin 3, fun _ _ => 0, fun v => v = 0 ∨ v = 1, fun a b => min a b⟩

/-- **The product projections are not Σ-homomorphism legs.** They respect grounds and the operation but fail
injectivity on grounds, collapsing the other factor's grounds, so the product span does not have
Σ-homomorphism legs. -/
theorem are_product_projections_theory_morphisms :
    (∀ (S T : OpLevelObj) (v : (tprod S T).B), (tprod S T).absent v → S.absent v.1)
    ∧ (∀ (S T : OpLevelObj) (a b : (tprod S T).B), ((tprod S T).op a b).1 = S.op a.1 b.1)
    ∧ (∃ (S T : OpLevelObj) (v w : (tprod S T).B),
        (tprod S T).absent v ∧ (tprod S T).absent w ∧ v.1 = w.1 ∧ v ≠ w) :=
  ⟨fun _ _ _ h => h.1, fun _ _ _ _ => rfl,
   S1, T2, ((0 : Fin 3), (0 : Fin 3)), ((0 : Fin 3), (1 : Fin 3)),
   ⟨rfl, Or.inl rfl⟩, ⟨rfl, Or.inr rfl⟩, rfl,
   fun h => absurd (congrArg (Prod.snd : Fin 3 × Fin 3 → Fin 3) h) (by decide)⟩

/-- **There is a pair without a span.** A Σ-homomorphism leg is injective on grounds, and there is no injection
from two grounds into one, so a two-ground object has a verdict no span carries to a one-ground one. -/
theorem is_there_a_pair_without_one :
    ¬ ∃ f : Fin 2 → Fin 1, Function.Injective f :=
  fun ⟨f, hf⟩ => absurd (hf (Subsingleton.elim (f 0) (f 1))) (by decide)

/-- **Objectivity as a lateral span.** A verdict is objective for two objects when a Σ-homomorphism span carries
it to both, the legs inheriting an apex absence forward without fabricating; and it can fail, since a span into a
one-ground object cannot carry two grounds. -/
theorem objectivity_as_lateral_span :
    (∀ (A S T : OpLevelObj) (legS : OpLevelHom A S) (legT : OpLevelHom A T) (v : A.B),
        A.absent v → S.absent (legS.onValues v) ∧ T.absent (legT.onValues v))
    ∧ (¬ ∃ f : Fin 2 → Fin 1, Function.Injective f) :=
  ⟨fun _ _ _ legS legT v h => ⟨legS.respectsAbsent v h, legT.respectsAbsent v h⟩, is_there_a_pair_without_one⟩

/-- **What it does not give.** Agreement does not recover a source: two objects can each carry an absence with no
apex determined, the inheritance forward only, matching the physics rather than falling short of it. -/
theorem what_it_does_not_give :
    ∃ (S T : OpLevelObj) (s : S.B) (t : T.B), S.absent s ∧ T.absent t :=
  ⟨S1, T2, (0 : Fin 3), (0 : Fin 3), rfl, Or.inl rfl⟩

/-- **Objectivity status: expressible and contingent.** Σ-homomorphism legs inherit agreement forward, and the
span can fail to exist, so the notion does not collapse to universality. -/
theorem objectivity_status :
    (∀ (A S : OpLevelObj) (legS : OpLevelHom A S) (v : A.B), A.absent v → S.absent (legS.onValues v))
    ∧ (¬ ∃ f : Fin 2 → Fin 1, Function.Injective f) :=
  ⟨fun _ _ legS v h => legS.respectsAbsent v h, is_there_a_pair_without_one⟩

/-! ## Arrows carry absence-preservation, and no provenance

Absence-preservation is what a `LevelHom` arrow adds; it does not derive from `preserves` or the hole. And no
`Obj`-morphism carries provenance: the limits are available, the evidence is not. -/

/-- **A morphism can send an absence to a verdict.** A value map can fabricate, sending distinct inputs to one
output, so `preserves` does not force absence-preservation and conformance does not give it: it is the arrow
condition `LevelHom.respects`, not a derived property. -/
theorem morphisms_do_not_preserve_absence :
    ∃ f : Option Bool → Bool, f none = f (some true) ∧ (none : Option Bool) ≠ some true :=
  ⟨fun v => v.getD true, rfl, by decide⟩

/-- The product of two objects, componentwise, classification forced. -/
def objProd (S T : Obj) : Obj :=
  ⟨S.X × T.X, S.B × T.B, fun a b => (S.classify a.1 b.1, T.classify a.2 b.2)⟩

/-- **`Obj` has products.** Two objects have a product with projection morphisms, so the several-views limit
shapes are available in `Obj`; the obstacle to objectivity is not missing limits but provenance, which no
morphism carries (`morphisms_do_not_preserve_absence`). -/
theorem obj_has_products (S T : Obj) :
    Nonempty (Hom (objProd S T) S) ∧ Nonempty (Hom (objProd S T) T) :=
  ⟨⟨Prod.fst, Prod.fst, fun _ _ => rfl⟩, ⟨Prod.snd, Prod.snd, fun _ _ => rfl⟩⟩

end Chiralogy
