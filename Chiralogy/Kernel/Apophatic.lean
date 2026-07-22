import Mathlib.Logic.Function.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

/-! # Kernel: the apophatic end (the hole at the codomain)

The category of self-classifying objects and its structural absences. `Obj`/`Hom` and the category; the two
absences (`no_reflexive_object` the diagonal, `no_universe_classifier` hence `no_right_adjoint` the size
argument, `obstructions_independent`); the hole, uniform and scale-free (`hole_uniform`, `hole_transports`,
`empty_center`); the three modes (`three_modes`, `NonDegenerate`, the lift and reflector); the dynamics
(`lift`, `no_recovery`, `order_canonical`, `no_generation`); the codomain involution (`swap_involution`); the
scope (`hole_scope_uniform`); the framework's own hole (`𝒜`, `self_account_has_hole`); and the variance
obstruction on centers (`onCarrier_is_wrong_direction`).

The no-final-coalgebra reading is a theorem (`no_final_coalgebra_for_the_classifier`): the hole is a Lambek-style
non-existence, no `X ≅ X → B`, so that functor has no final coalgebra as powerset has none by Cantor, the
selection principle for the available dynamics. -/

namespace Chiralogy

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

/-- `Chiralogy` is a category; identity and composition are inherited from `Set`. -/
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


open CategoryTheory

universe u w v₁ v₂ w₁ w₂

/-- **The variance obstruction on centers.** A morphism supplies `onCarrier : S.X → T.X`, but the center's
exponential `S.X → S.B` is contravariant in the carrier, so a covariant action on centers would need
`T.X → S.X`. A morphism does not provide one: its `onCarrier` need not be left-invertible. The
center-assignment `S ↦ (S.X → S.B)` is therefore not a functor on the category. -/
theorem onCarrier_is_wrong_direction :
    ∃ (S T : Obj) (φ : Hom S T), ¬ ∃ ψ : T.X → S.X, ∀ x, ψ (φ.onCarrier x) = x := by
  refine ⟨⟨Fin 2, Unit, fun _ _ => ()⟩, ⟨Fin 1, Unit, fun _ _ => ()⟩,
    ⟨fun _ => 0, id, fun _ _ => rfl⟩, ?_⟩
  rintro ⟨ψ, hψ⟩
  have h0 : ψ 0 = 0 := hψ 0
  have h1 : ψ 0 = 1 := hψ 1
  exact absurd (h0.symm.trans h1) (by decide)

/-! ## First absence: no reflexive object -/

/-- A point-surjection forces a fixed point (the diagonal argument). -/
theorem fixedPoint_of_surjection {X : Type u} {B : Type w}
    (f : X → X → B) (hf : Function.Surjective f) (g : B → B) : ∃ b, g b = b :=
  Function.exists_fixed_point_of_surjective f hf g

/-- **No reflexive object.** If `B` carries a fixed-point-free endomap, no `f : X → X → B` is surjective:
nothing retracts onto its own classifier space. -/
theorem no_reflexive_object {X : Type u} {B : Type w} {g : B → B}
    (hg : ∀ b, g b ≠ b) (f : X → X → B) : ¬ Function.Surjective f := by
  intro hs
  obtain ⟨b, hb⟩ := fixedPoint_of_surjection f hs g
  exact hg b hb

/-! ## Second absence: no universe classifier, hence no right adjoint

The paradox term is Hurkens' simplification of Girard's, taking as hypotheses the impredicative
`Π`-data a `Type : Type` universe would supply and yielding `False`. -/

/-- The paradox: no universe has `Type u : Type u`. -/
theorem paradox (pi : (Type u → Type u) → Type u)
    (lam : ∀ {A : Type u → Type u}, (∀ x, A x) → pi A) (app : ∀ {A}, pi A → ∀ x, A x)
    (beta : ∀ {A : Type u → Type u} (f : ∀ x, A x) (x), app (lam f) x = f x) : False :=
  let F (X) := (Set (Set X) → X) → Set (Set X)
  let U := pi F
  let G (T : Set (Set U)) (X) : F X := fun f => {p | {x : U | f (app x X f) ∈ p} ∈ T}
  let τ (T : Set (Set U)) : U := lam (G T)
  let σ (S : U) : Set (Set U) := app S U τ
  have στ : ∀ {s S}, s ∈ σ (τ S) ↔ {x | τ (σ x) ∈ s} ∈ S := fun {s S} =>
    iff_of_eq (congr_arg (fun f : F U => s ∈ f τ) (beta (G S) U) :)
  let ω : Set (Set U) := {p | ∀ x, p ∈ σ x → x ∈ p}
  let δ (S : Set (Set U)) := ∀ p, p ∈ S → τ S ∈ p
  have : δ ω := fun _p d => d (τ ω) <| στ.2 fun x h => d (τ (σ x)) (στ.2 h)
  this {y | ¬δ (σ y)} (fun _x e f => f _ e fun _p h => f _ (στ.1 h)) fun _p h => this _ (στ.1 h)

/-- A universe classifier: the impredicative dependent product a `Type : Type` universe would provide. -/
structure UniverseClassifier where
  Pi : (Type u → Type u) → Type u
  lam : ∀ {A : Type u → Type u}, (∀ x, A x) → Pi A
  app : ∀ {A : Type u → Type u}, Pi A → ∀ x, A x
  beta : ∀ {A : Type u → Type u} (f : ∀ x, A x) (x), app (lam f) x = f x

/-- **No universe classifier.** -/
theorem no_universe_classifier : IsEmpty UniverseClassifier.{u} :=
  ⟨fun U => paradox U.Pi U.lam U.app U.beta⟩

private theorem eqRec_fun {A : Type u → Type u} (f : ∀ x, A x) {a b : Type u} (h : a = b) :
    h ▸ f a = f b := by subst h; rfl

/-- A `u`-small copy of `Type u` supplies the impredicative `Π`-data: impredicativity from smallness. -/
def universeClassifier_ofEquiv {U : Type u} (e : U ≃ Type u) : UniverseClassifier.{u} where
  Pi A := ∀ x : U, A (e x)
  lam f := fun x => f (e x)
  app g := fun X => (e.apply_symm_apply X) ▸ g (e.symm X)
  beta f X := eqRec_fun f (e.apply_symm_apply X)

/-- **No small universe**: `Type u` is not `u`-small: a small universe would be a universe classifier. -/
theorem no_small_universe : ¬ ∃ U : Type u, Nonempty (U ≃ Type u) := by
  rintro ⟨U, ⟨e⟩⟩
  exact no_universe_classifier.false (universeClassifier_ofEquiv e)

/-- `M : 𝓔'` classifies `Type u` worth of object-types: its global sections along the level shift out
of the object-terminal biject with `Type u`. -/
def IsUniverseClassifier {𝓔 : Type w₁} [Category.{v₁} 𝓔] {𝓔' : Type w₂} [Category.{v₂} 𝓔']
    (one : 𝓔) (up : 𝓔 ⥤ 𝓔') (M : 𝓔') : Prop :=
  Nonempty ((up.obj one ⟶ M) ≃ Type u)

/-- **No right adjoint.** A level-shift functor with a right adjoint and a universe classifier would
transport the classifier down to a small copy of `Type u`, contradicting `no_small_universe`. The small
universe is derived, not assumed; the contradiction routes through the paradox. -/
theorem no_right_adjoint
    {𝓔 : Type w₁} [Category.{v₁} 𝓔] {𝓔' : Type w₂} [Category.{v₂} 𝓔']
    (forget : 𝓔 ⥤ Type u) (one : 𝓔) (pt : ∀ Z : 𝓔, (one ⟶ Z) ≃ forget.obj Z)
    (up : 𝓔 ⥤ 𝓔') [h : up.IsLeftAdjoint]
    (M : 𝓔') (hM : IsUniverseClassifier.{u} one up M) : False := by
  obtain ⟨down, ⟨adj⟩⟩ := h.exists_rightAdjoint
  obtain ⟨eM⟩ := hM
  have e : forget.obj (down.obj M) ≃ Type u :=
    (pt (down.obj M)).symm.trans ((adj.homEquiv one M).symm.trans eM)
  exact no_small_universe ⟨_, ⟨e⟩⟩

/-- **Independence.** The two obstructions are governed by different data, so neither reduces to the other.
The reflexive-object obstruction is codomain-relative: it holds on a nontrivial codomain (`Bool`, carrying
a fixed-point-free endomap) yet fails on a trivial one (`Unit`, where an object surjects onto its
transpose). The size obstruction holds regardless, at the universe level. So no object factors through
both: one is a property of the codomain, the other of the universe. -/
theorem obstructions_independent :
    (∃ c : Fin 2 → Fin 2 → Bool, ¬ Function.Surjective c) ∧
    (∃ (X : Type) (c : X → X → Unit), Function.Surjective c) ∧
    (¬ ∃ U : Type, Nonempty (U ≃ Type)) :=
  ⟨⟨fun _ _ => true, no_reflexive_object (g := fun b => !b) (by decide) _⟩,
   ⟨Fin 1, fun _ _ => (), fun g => ⟨0, funext fun _ => Subsingleton.elim _ _⟩⟩,
   no_small_universe⟩


/-- A fixed-point-free endomap of `Option Bool` (a 3-cycle): witnessing the hole on partial objects. -/
def optCycle : Option Bool → Option Bool
  | none => some true
  | some true => some false
  | some false => none

theorem optCycle_fixedpointfree : ∀ o, optCycle o ≠ o := by
  intro o; cases o with
  | none => decide
  | some b => cases b <;> decide

/-- **The hole, uniform.** Every object with distinction space `Option Bool`, total or partial, in any
mode, is subject to the hole: its classification is not surjective. Nothing changes this; the hole is
Cantor-uniform. -/
theorem hole_uniform {X : Type} (c : X → X → Option Bool) : ¬ Function.Surjective c :=
  no_reflexive_object optCycle_fixedpointfree c

/-- The hole transports: any distinction space carrying a fixed-point-free endomap inherits it. -/
theorem hole_transports {X : Type} {B : Type} {g : B → B} (hg : ∀ b, g b ≠ b)
    (c : X → X → B) : ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-- **The empty center.** No carrier is equivalent to its own classifier space `X → Bool`: the reflexive
site has empty fixed locus. A corollary of the hole. -/
theorem empty_center : ¬ ∃ X : Type u, Nonempty (X ≃ (X → Bool)) := by
  rintro ⟨X, ⟨e⟩⟩
  obtain ⟨b, hb⟩ := fixedPoint_of_surjection (⇑e) e.surjective (fun b => !b)
  exact absurd hb (by cases b <;> decide)

/-! ### No total internal self-description

`empty_center` read as self-description. A description of a carrier `D` is an element of its classifier space
`D → Bool`; a self-classification `desc : D → D → Bool` is, curried, a `D`-indexed family of descriptions, each
`d` giving the row `desc d : D → Bool`, its view of the whole. A TOTAL internal self-description is such a `desc`
surjective onto `D → Bool`: every description realized as some element's view, or equivalently a reflexive
`D ≃ (D → Bool)`. The diagonal (`no_reflexive_object`, `fixedPoint_of_surjection`) forbids it. So the framework
cannot totally self-describe internally, for the same reason its objects cannot totally self-classify: one cause,
the empty center. It can still self-apply (application is an internal predicate, `Member`, in
`Protocol/Membership`); it cannot totally self-describe. The bound is within-language: a statement about what
`D → Bool` can contain, not a claim about every possible formalization. -/

/-- **No total internal self-description.** For any descriptive carrier `D`, no self-classification
`desc : D → D → Bool` is surjective onto the description space `D → Bool`: no `D`-indexed family of Boolean
descriptions realizes every description. This is `no_reflexive_object` (the diagonal) read as self-description:
`Bool` carries the fixed-point-free `not`. -/
theorem no_total_internal_self_description {D : Type u} (desc : D → D → Bool) :
    ¬ Function.Surjective desc :=
  no_reflexive_object (g := fun b => !b) (by decide) desc

/-- **The equivalence form.** No carrier is equivalent to its own description space `D → Bool`: the reflexive
equivalence a total self-description would need does not exist. The content of `empty_center`, here as
self-description, derived from the surjection form (an equivalence would give a surjective self-description). -/
theorem no_self_description_equiv {D : Type u} : ¬ Nonempty (D ≃ (D → Bool)) := by
  rintro ⟨e⟩
  exact no_total_internal_self_description (fun a => e a) e.surjective

/-- Non-degeneracy: the self enters the map: two carrier elements induce different classification rows. -/
def NonDegenerate {X B : Type} (c : X → X → B) : Prop := ∃ x x', c x ≠ c x'

/-- **The three modes are exhaustive.** No self-model (`¬ NonDegenerate`), total self-model, or partial
self-model. -/
theorem three_modes {X : Type} (c : X → X → Option Bool) :
    (¬ NonDegenerate c) ∨
      (NonDegenerate c ∧ ∀ x y, c x y ≠ none) ∨
      (NonDegenerate c ∧ ∃ x y, c x y = none) := by
  by_cases h : NonDegenerate c
  · by_cases ht : ∀ x y, c x y ≠ none
    · exact Or.inr (Or.inl ⟨h, ht⟩)
    · refine Or.inr (Or.inr ⟨h, ?_⟩)
      by_contra hc
      exact ht (fun x y hxy => hc ⟨x, y, hxy⟩)
  · exact Or.inl h

/-- A single external judge, the first argument idle, is degenerate. This is the boundary of `Deg`. -/
theorem external_judge_is_degenerate {X : Type} (j : X → Option Bool) :
    ¬ NonDegenerate (fun (_ : X) => j) := by
  rintro ⟨_, _, h⟩; exact h rfl

/-! ## Degeneracy for morphisms -/

/-- The structureless point: a terminal object, its carrier and distinction space singletons. -/
def pointObj : Obj := ⟨Unit, Unit, fun _ _ => ()⟩

/-- The constant morphism collapsing any object onto the structureless point. -/
def toPoint (S : Obj) : Hom S pointObj := ⟨fun _ => (), fun _ => (), fun _ _ => rfl⟩

/-- **Degenerate morphisms are permitted.** Every object has a morphism to the structureless point, a degenerate
collapse erasing all structure, its target a subsingleton. Where a degenerate object is excluded, the total opening
failing non-degeneracy, a degenerate morphism is admitted: a trivial relation between objects says something
admissible where a trivial object says nothing. -/
theorem degenerate_morphism_permitted (S : Obj) :
    Nonempty (Hom S pointObj) ∧ Subsingleton pointObj.B :=
  ⟨⟨toPoint S⟩, inferInstanceAs (Subsingleton Unit)⟩

/-- **The saturated morphism end is inhabited.** Between distinct objects there is a morphism injective on both
carrier and distinction space, an embedding of a smaller register into a larger: the injective end, where the tower
does its work, is reached, opposite the degenerate collapse. -/
theorem saturated_morphism_available :
    ∃ (S T : Obj) (φ : Hom S T), Function.Injective φ.onCarrier ∧ Function.Injective φ.onValues :=
  ⟨⟨Fin 2, Fin 2, fun x _ => x⟩, ⟨Fin 3, Fin 3, fun x _ => x⟩,
   ⟨Fin.castSucc, Fin.castSucc, fun _ _ => rfl⟩,
   Fin.castSucc_injective 2, Fin.castSucc_injective 2⟩

/-! ## The lift is not a reflection -/

/-- The lift onto `Deg` collapses to a degenerate shadow at a basepoint. Different basepoints give
different shadows; so the lift is parametric, not a canonical reflector. -/
theorem lift_is_basepoint_parametric :
    ∃ c : Fin 2 → Fin 2 → Bool,
      (fun (_ : Fin 2) y => c 0 y) ≠ (fun (_ : Fin 2) y => c 1 y) :=
  ⟨fun i j => decide (i = j), fun h => absurd (congrFun (congrFun h 0) 0) (by decide)⟩

/-! ## `Deg` is reflective, via the codomain quotient -/

/-- The reflector's distinction space: `B` quotiented so the rows collapse. -/
def reflValues {X B : Type} (c : X → X → B) : Type :=
  Quot (fun b b' => ∃ x x' y, b = c x y ∧ b' = c x' y)

/-- The reflected classification. -/
def reflClassify {X B : Type} (c : X → X → B) : X → X → reflValues c :=
  fun x y => Quot.mk _ (c x y)

/-- The reflector's target is degenerate. -/
theorem reflClassify_degenerate {X B : Type} (c : X → X → B) :
    ¬ NonDegenerate (reflClassify c) := by
  rintro ⟨x, x', h⟩
  exact h (funext fun y => Quot.sound ⟨x, x', y, rfl, rfl⟩)

/-- **`Deg` is reflective.** A morphism to a degenerate object forces its value map to equalize the rows;
every such map factors uniquely through the quotient. This is the reflection: the reflector is the
codomain quotient, not the basepoint shadow. -/
theorem reflector_universal {X B B' : Type} (c : X → X → B) (g : B → B')
    (hg : ∀ x x' y, g (c x y) = g (c x' y)) :
    ∃! gbar : reflValues c → B', ∀ b, gbar (Quot.mk _ b) = g b := by
  refine ⟨Quot.lift g ?_, fun _ => rfl, ?_⟩
  · rintro b b' ⟨x, x', y, rfl, rfl⟩; exact hg x x' y
  · intro h hh
    funext q
    induction q using Quot.ind
    exact hh _


/-! ## The one canonical channel: the idempotent lift -/

/-- The lift: collapse to the degenerate shadow at a basepoint. -/
def lift {X B : Type} (x₀ : X) (c : X → X → B) : X → X → B := fun _ y => c x₀ y

/-- **The one canonical channel.** The lift is idempotent: collapsing twice equals collapsing once.
Intrinsic to the classification, independent of the distinction space and of any target. -/
theorem lift_idempotent {X B : Type} (x₀ : X) (c : X → X → B) :
    lift x₀ (lift x₀ c) = lift x₀ c := rfl

/-- The lift is not injective: two maps agreeing on the basepoint row have the same lift. -/
theorem lift_not_injective :
    ∃ c c' : Fin 2 → Fin 2 → Bool, c ≠ c' ∧ lift 0 c = lift 0 c' :=
  ⟨(fun _ _ => false), (fun i j => decide (i = 1 ∧ j = 0)), by decide, by decide⟩

/-- **The arrow.** No operation recovers the original from its lift: the canonical collapse is
irreversible. -/
theorem no_recovery :
    ¬ ∃ recover : (Fin 2 → Fin 2 → Bool) → (Fin 2 → Fin 2 → Bool),
        ∀ c, recover (lift 0 c) = c := by
  rintro ⟨recover, h⟩
  obtain ⟨c, c', hne, heq⟩ := lift_not_injective
  apply hne
  rw [← h c, heq, h c']

/-! ## The imported flow: the agreement preorder -/

/-- The agreement preorder toward a target: `x ⊑_t x'` iff `x'` classifies as `t` at least wherever `x`
does. Motion toward `t` is ascent. -/
def agreementLE {X B : Type} (c : X → X → B) (t : B) (x x' : X) : Prop :=
  ∀ y, c x y = t → c x' y = t

theorem agreementLE_refl {X B : Type} (c : X → X → B) (t : B) (x : X) : agreementLE c t x x :=
  fun _ h => h

theorem agreementLE_trans {X B : Type} (c : X → X → B) (t : B) {x x' x'' : X}
    (h1 : agreementLE c t x x') (h2 : agreementLE c t x' x'') : agreementLE c t x x'' :=
  fun y hy => h2 y (h1 y hy)

/-- The coalgebra for `F X = B → Set X`: the nondeterministic all-successors transition structure,
determined by the classification alone. -/
def targetCoalgebra {X B : Type} (c : X → X → B) : X → (B → Set X) :=
  fun x t => {x' | agreementLE c t x x'}

/-- **The order-part is canonical.** A preorder read off the classification and the target: no measure. -/
theorem order_canonical {X B : Type} (c : X → X → B) (t : B) :
    (∀ x, agreementLE c t x x) ∧
      (∀ x x' x'', agreementLE c t x x' → agreementLE c t x' x'' → agreementLE c t x x'') :=
  ⟨agreementLE_refl c t, fun _ _ _ => agreementLE_trans c t⟩

/-- The rate is imported: the identity is always a valid step, yet a strict successor exists: how far to
move is not determined by the target. -/
def rateWitness : Fin 2 → Fin 2 → Bool := fun i _ => decide (i = 1)

theorem rate_imported :
    agreementLE rateWitness true 0 0 ∧ agreementLE rateWitness true 0 1 ∧
      ¬ agreementLE rateWitness true 1 0 := by
  refine ⟨agreementLE_refl rateWitness true 0, ?_, ?_⟩
  · intro y hy; simp [rateWitness] at hy
  · intro h; have := h 0 (by decide); simp [rateWitness] at this

/-- **Fixed points are target-agreers.** A state classifying everything as `t` is above every state: the
equilibrium the flow ascends to. The moves are the flow structure: totalization is the flow to one
equilibrium. -/
theorem fixed_points_are_target_agreers {X B : Type} (c : X → X → B) (t : B) (xstar : X)
    (h : ∀ y, c xstar y = t) : ∀ x, agreementLE c t x xstar :=
  fun _ y _ => h y

/-- **The flow is kernel-level.** Incomparable equilibria appear on a total object: the dynamics is a fact
about the classification and a target, not the extension. -/
theorem dynamics_nontrivial_on_total :
    ∃ (c : Fin 2 → Fin 2 → Bool) (t : Bool) (x x' : Fin 2),
      ¬ agreementLE c t x x' ∧ ¬ agreementLE c t x' x := by
  refine ⟨fun i j => decide (i = j), true, 0, 1, ?_, ?_⟩
  · intro h; have := h 0 (by decide); simp at this
  · intro h; have := h 1 (by decide); simp at this

/-- **No generation, no history.** The successors are a subset of the existing carrier: the flow moves
among existing elements, and is a function of the current state. Only order-motion toward a target. -/
theorem no_generation {X B : Type} (c : X → X → B) (x : X) (t : B) :
    targetCoalgebra c x t ⊆ (Set.univ : Set X) :=
  fun _ _ => trivial


/-- Argument swap: exchange judge and judged. -/
def swap {X B : Type} (c : X → X → B) : X → X → B := fun x y => c y x

theorem swap_involution {X B : Type} (c : X → X → B) : swap (swap c) = c := rfl

/-- Swap acts non-trivially: on a non-symmetric classification it changes the map. -/
theorem swap_nontrivial : ∃ c : Fin 2 → Fin 2 → Bool, swap c ≠ c :=
  ⟨fun i j => decide (i = 0 ∧ j = 1), fun h => absurd (congrFun (congrFun h 1) 0) (by decide)⟩

/-- Swap carries the first-argument absence to the second: swapping a first-argument-idle map makes it
second-argument-idle. -/
theorem swap_relates_absences {X B : Type} (x₀ : X) (c : X → X → B) :
    swap (fun _ y => c x₀ y) = fun x _ => c x₀ x := rfl

/-- Codomain-negation is not a canonical involution: a fixed-point-free endomap need not be an involution
(a 3-cycle is not). -/
theorem codomain_negation_not_canonical :
    ∃ (B : Type) (g : B → B), (∀ b, g b ≠ b) ∧ g ∘ g ≠ id :=
  ⟨Option Bool, optCycle, optCycle_fixedpointfree,
    fun h => absurd (congrFun h none) (by decide)⟩


/-- A mixed object: a no-self-model block `{0,1}`, a total block `{2,3}`, a partial block `{4,5}`, coupled
by cross-block verdicts on one carrier. -/
def mixed : Fin 6 → Fin 6 → Option Bool := fun x y =>
  if x.val / 2 ≠ y.val / 2 then some (decide (x.val < y.val))
  else if y.val < 2 then some (decide (y.val = 0))
  else if y.val < 4 then some (decide (x = y))
  else if x = y then some true else none

/-- **The hole is uniform**: present on the mixed object as on every object. -/
theorem hole_scope_uniform : ¬ Function.Surjective mixed := hole_uniform mixed

/-- **Self-entry is regional.** The first argument is idle on the no-self-model block; the total and
partial blocks are non-degenerate. Self-entry is confined to those regions. -/
theorem self_entry_regional :
    (∀ x x' y : Fin 6, x.val < 2 → x'.val < 2 → y.val < 2 → mixed x y = mixed x' y) ∧
      (∃ x x' y : Fin 6, 2 ≤ x.val ∧ x.val < 4 ∧ 2 ≤ x'.val ∧ x'.val < 4 ∧ 2 ≤ y.val ∧ y.val < 4 ∧
        mixed x y ≠ mixed x' y) ∧
      (∃ x x' y : Fin 6, 4 ≤ x.val ∧ 4 ≤ x'.val ∧ 4 ≤ y.val ∧ mixed x y ≠ mixed x' y) := by
  refine ⟨by decide, ⟨2, 3, 2, by decide⟩, ⟨4, 5, 5, by decide⟩⟩

/-- **The target-flow is global.** It crosses mode boundaries: a no-self-model state is `⊑_t`-below a
total-self-model state. Not confined like self-entry. -/
theorem flow_global :
    ∃ (t : Option Bool) (x x' : Fin 6),
      x.val / 2 ≠ x'.val / 2 ∧ agreementLE mixed t x x' := by
  refine ⟨none, 0, 2, by decide, ?_⟩
  unfold agreementLE
  decide


/-- Codes for self-classifying systems: a `Type 0` proxy for objects of `Chiralogy` (which live in `Type 1`). -/
abbrev Rep : Type := Nat

/-- The internal self-classification: `selfClassify s t` is `s`'s decidable proxy verdict that system `t`
completely classifies itself (a reflexive proxy: a system vouches only for itself). -/
def selfClassify : Rep → Rep → Bool := fun s t => decide (s = t)

theorem selfClassify_nondegenerate : NonDegenerate selfClassify :=
  ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩

theorem selfClassify_hole : ¬ Function.Surjective selfClassify :=
  hole_transports (g := fun b => !b) (by decide) selfClassify

/-- `𝒜`: a faithful internal representation of Chiralogy's own self-classification as an object. -/
def 𝒜 : Obj := ⟨Rep, Bool, selfClassify⟩

/-- The codomain is a genuine two-point space: `𝒜` is a well-formed object. -/
theorem 𝒜_canDiffer : ∃ a b : 𝒜.B, a ≠ b := ⟨true, false, fun h => Bool.noConfusion h⟩

/-- **Non-degenerate.** The self enters the representation: two systems classify differently. -/
theorem 𝒜_nondegenerate : NonDegenerate 𝒜.classify := selfClassify_nondegenerate

/-- **Self-application (the payload, internally).** The internal representation of Chiralogy's own
self-classification is not surjective onto its rows: it carries the hole. -/
theorem self_account_has_hole : ¬ Function.Surjective 𝒜.classify := selfClassify_hole

/-- **No final coalgebra for the classifier.** A final coalgebra of `F X = X → B` is a fixed point `C ≅ F C`
(Lambek); `empty_center` forbids `C ≅ (C → Bool)`, as Cantor forbids it for powerset. A theorem, not a reading:
the selection principle for the available dynamics, this behaviour functor carries none. -/
theorem no_final_coalgebra_for_the_classifier : ¬ ∃ C : Type, Nonempty (C ≃ (C → Bool)) :=
  empty_center

end Chiralogy
