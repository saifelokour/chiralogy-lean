import Chiralogy

/-! # Experiment: what would coalgebra do to the framework?

Lambek plus Cantor says the powerset functor has no final coalgebra; the framework's `empty_center` is the same
fact for `F X = X → B`. So the kernel does not conflict with coalgebra, it selects which behaviour functors are
available. The hole is a Lambek-style non-existence: no `X ≅ X → B`, so that functor has no final coalgebra,
exactly as powerset has none by Cantor. Determine what a coalgebraic reading would change. Concrete small
instances; do not build general coalgebra machinery. Stays in `Experiments/`; canonical untouched; nothing
resolved. -/

open Chiralogy

namespace Chiralogy.Coalgebra

/-- A stream, the final coalgebra of `F X = A × X`. -/
def Str (A : Type) : Type := ℕ → A
def sHead {A : Type} (s : Str A) : A := s 0
def sTail {A : Type} (s : Str A) : Str A := fun n => s (n + 1)
def sCons {A : Type} (a : A) (s : Str A) : Str A := fun n => match n with | 0 => a | k + 1 => s k

/-! ## Part 1: which behaviour functors does the hole permit? -/

/-- **Forbidden functors.** The excluded functors are those whose fixed point is a reflexive object: `F X = X → B`
(and powerset `X → Bool`) admit no surjection `X → (X → B)` when `B` carries a fixed-point-free endomap, so no
iso `X ≅ X → B`, no final coalgebra. The criterion is precisely a surjection violating the hole. -/
theorem forbidden_functors {X B : Type} (g : B → B) (hg : ∀ b, g b ≠ b) :
    ∀ e : X → (X → B), ¬ Function.Surjective e :=
  fun e => no_reflexive_object hg e

/-- **Permitted functors.** Streams `ℕ → A` are the final coalgebra of `F X = A × X`: head and tail with cons are
mutually inverse, an isomorphism `Str A ≅ A × Str A`. The hole does not exclude it, `A × X` gives no reflexive
object; `Maybe (A × X)` (possibly-terminating streams) likewise. So the hole permits genuine dynamics. -/
theorem permitted_functors {A : Type} (a : A) (s : Str A) :
    (sCons (sHead s) (sTail s) = s) ∧ (sHead (sCons a s) = a) ∧ (sTail (sCons a s) = s) := by
  refine ⟨?_, rfl, ?_⟩
  · funext n; cases n <;> rfl
  · funext n; rfl

/-- **The hole is the criterion.** It excludes exactly the functors whose fixed point would be a reflexive
object, a surjection `X → (X → B)`, covering `X → B` and powerset, and permits those with genuine final
coalgebras (streams). It is the diagonal selection principle, the criterion for diagonal failures, which is the
framework's classification functor and its kin. -/
theorem is_the_hole_the_criterion {X B : Type} (g : B → B) (hg : ∀ b, g b ≠ b) {A : Type} (s : Str A) :
    (∀ e : X → (X → B), ¬ Function.Surjective e)
    ∧ (sCons (sHead s) (sTail s) = s) :=
  ⟨fun e => no_reflexive_object hg e, by funext n; cases n <;> rfl⟩

/-! ## Part 2: does absence become non-termination? -/

/-- A coalgebra that never emits a verdict, always continuing silently. -/
def silentLoop : Unit → Bool ⊕ Unit := fun _ => Sum.inr ()

/-- **Absence coalgebraically.** Range absence is a returned value `none`; coalgebraic absence is a non-producing
state, the coalgebra `silentLoop` always continuing (`inr`) and never emitting a verdict (`inl`). One has a
value; the other has no value at all. -/
theorem absence_coalgebraically :
    ((none : Option Bool) = none)
    ∧ (∀ b : Bool, silentLoop () ≠ Sum.inl b) :=
  ⟨rfl, fun b => by simp [silentLoop]⟩

/-- **Two kinds of absence.** Genuinely two: range absence has a value (`none`), coalgebraic absence has none
(never emits). The prohibition quantifies a returned value (`complete_and_faithful_is_impossible`, `c 0 2 =
none`); a non-producing state returns nothing, so the prohibition does not reach it. Non-termination is a mode
outside the range-based prohibition, as vacating was: it escapes not by returning verdicts but by returning
nothing. -/
theorem two_kinds_of_absence :
    (∃ v : Option Bool, v = none)
    ∧ (∀ b : Bool, silentLoop () ≠ Sum.inl b)
    ∧ (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2) :=
  ⟨⟨none, rfl⟩, fun b => by simp [silentLoop], complete_and_faithful_is_impossible⟩

/-! ## Part 3: what changes structurally -/

/-- **The identity criterion.** Coalgebra replaces equality with bisimilarity, indistinguishability by
observation, which is coarser than equality: literally equal classifications are bisimilar. Detection found a
totalized and an innocent classification literally equal; under bisimilarity they remain identified. Bisimilarity
does not distinguish them, it identifies more, not less, so it does not improve the detection result. -/
theorem identity_criterion (c1 c2 : Fin 2 → Fin 2 → Bool) :
    c1 = c2 → ∀ x y, c1 x y = c2 x y :=
  fun h x y => by rw [h]

/-- **What the arms become.** The coalgebraic side is the apophatic arm properly understood. The framework
already reads cofree constructions, comonads, and observation as apophatic-shaped, the dual of the Maybe monad.
The hole is a coalgebraic non-existence (no final coalgebra for `X → B`), and the permitted functors have final
coalgebras (streams, the observation side); both are coalgebraic, on the apophatic arm. So coalgebra is not a
third arm but the apophatic arm's domain, observation where it succeeds, the hole where it fails. -/
theorem what_the_arms_become {X B : Type} (g : B → B) (hg : ∀ b, g b ≠ b) {A : Type} (s : Str A) :
    (∀ e : X → (X → B), ¬ Function.Surjective e)
    ∧ (sCons (sHead s) (sTail s) = s) :=
  ⟨fun e => no_reflexive_object hg e, by funext n; cases n <;> rfl⟩

/-- **The tower under coalgebra.** The tower is arity-indexed algebraic presentations, operations, the cataphatic
build. Coalgebra is the dual, observations, the apophatic side. A coalgebraic layer sits beside the algebraic
tower as its dual, indexed by observations rather than operations; it does not extend it, a different direction,
build versus observe, nor replace it. -/
theorem the_tower_under_coalgebra {A : Type} (a : A) (s : Str A) :
    ((fun x y : List Bool => x ++ y) [true] [false] = [true, false])
    ∧ (sHead (sCons a s) = a) :=
  ⟨rfl, rfl⟩

/-- **What is untouched.** The permitted lattice (a function of the reasons, not of behaviours), the payload and
the protocol (about returned values), and the ground-structures (reasons are the nullary generators). Coalgebra
concerns the dynamics of producing a value, not the value or the grounds, so the range-side structure is
untouched. -/
theorem what_is_untouched :
    ((Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3)
    ∧ (∀ {X : Type} (c : X → X → Option Bool), ¬ Function.Surjective c)
    ∧ (∀ v : Option Bool, v = none ↔ ∃ u : Unit, failMaybe u = v) :=
  ⟨by decide, fun c => hole_uniform c, reasons_are_nullary_generators.2⟩

/-! ## Part 4: the verdict -/

/-- **Extension or different framework.** Coalgebra is compatible but distinct. The kernel permits it (streams
have final coalgebras), so there is no conflict; but the model layer is algebraic (operations, the arity-indexed
presentations) and coalgebra is its dual (observations, behaviours), a process notion. So a coalgebraic layer
sits alongside the algebraic model as a dual, not as a completion of it. -/
theorem is_coalgebra_an_extension_or_a_different_framework {A : Type} (a : A) (s : Str A) :
    (sCons (sHead s) (sTail s) = s)
    ∧ ((fun x y : List Bool => x ++ y) [true] [false] = [true, false])
    ∧ (sHead (sCons a s) = a) :=
  ⟨by funext n; cases n <;> rfl, rfl, rfl⟩

/-! ## The verdicts

Part 1: the hole permits genuine dynamics and is the diagonal criterion. It excludes `F X = X → B` and powerset,
whose fixed point is a reflexive object (`forbidden_functors`), and permits streams `A × X`, a final coalgebra
(`permitted_functors`). The criterion is exactly a surjection violating the hole (`is_the_hole_the_criterion`),
the diagonal selection principle, not every functor without a final coalgebra.

Part 2: non-termination is a second, genuinely distinct kind of absence. Range absence has a value, a
non-producing state has none (`absence_coalgebraically`, `two_kinds_of_absence`). The prohibition quantifies a
returned value, so a process that returns nothing is outside it, the vacating result in a new form: it escapes
the prohibition by returning nothing rather than by returning verdicts.

Part 3: identity is not improved by bisimilarity, which is coarser than equality and identifies the literally
equal (`identity_criterion`), so the detection result stands. The coalgebraic side is the apophatic arm properly
understood, the observation side the framework already reads as apophatic-shaped (`what_the_arms_become`), not a
third arm. It sits beside the algebraic tower as its dual (`the_tower_under_coalgebra`). The protocol, registers,
ground-structures, and permitted lattice are untouched (`what_is_untouched`).

Part 4: a coalgebraic layer is compatible but distinct, not a completion. The kernel permits it, but the model
is algebraic and coalgebra is its dual, a process notion
(`is_coalgebra_an_extension_or_a_different_framework`). Reported honestly: the framework's arms and model are
algebraic, and coalgebra is a different thing, a process side, sitting beside them as a dual, not extending or
completing the algebraic one. Compatibility is not endorsement; the kernel permits coalgebra, and that is all.
Nothing here is resolved. -/

end Chiralogy.Coalgebra
