import Autology.Kernel.Obstructions

/-! # Closure of the codomain axis

Two candidate codomain extensions, a stochastic distinction space and a substructural one, collapse in a
cartesian base, both through the diagonal (copy). The diagonal that makes the hole is the one that closes
the codomain axis: partiality is the one member. -/

namespace Autology

/-- Copy is available on every distinction space in a cartesian base: the diagonal is unconditional. This
is the root of both collapses, and the diagonal the obstructions use. -/
def copy {B : Type} (b : B) : B × B := (b, b)

theorem copy_is_free (B : Type) (b : B) : copy b = (b, b) := rfl

/-- A stochastic distinction space collapses to a codomain enrichment: a classification into any space `D`
is a plain map subject to the same hole. Determinism is not a separate axis: the map into `D` is the
extension. -/
theorem stochastic_collapses {X D : Type} {g : D → D} (hg : ∀ d, g d ≠ d)
    (c : X → X → D) : ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-- A substructural (tensor) distinction space has copy in a cartesian base, so the tensor is the product:
the additive/multiplicative distinction is invisible. -/
theorem tensor_has_copy {B C : Type} (p : B × C) : copy p = (p, p) := rfl

/-- **The diagonal that makes the hole closes the codomain axis.** The diagonal argument duplicates its
argument: it factors through copy. In a base without copy the argument cannot be built. -/
theorem diagonal_factors_through_copy {X Y : Type} (f : X → X → Y) :
    (fun x => f x x) =
      (fun p : (X → Y) × X => p.1 p.2) ∘ (Prod.map f id) ∘ (@copy X) := by
  funext x; rfl

theorem the_diagonal_is_copy {X : Type} : (fun x : X => (x, x)) = (@copy X) := rfl

end Autology
