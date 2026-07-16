import Mathlib.Logic.Function.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs

/-! # The two structural absences

No object is reflexive (the diagonal obstruction), and there is no universe classifier; hence no right
adjoint to the level shift (the size obstruction). They are distinct: the first is about a self-map's
surjectivity, the second about a functor. -/

namespace Autology

open CategoryTheory

universe u w v₁ v₂ w₁ w₂

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

end Autology
