import Chiralogy

/-! # Experiment: cost-bounded conformance (Blum-parameterized, at the protocol)

Syntax as an abstract parameter is a Blum numbering: an index type `I`, a denotation `denote : I → (X → X → B)`
that is not injective (two indices may denote the same classification), and a measure `Φ : I → X → ℕ`. Cost
lives on the index, which is finer than what it denotes. No Turing machines, no effective enumeration.

The kernel cannot see cost: it takes a classification and produces the hole uniformly (Lawvere's minimality,
and six prior discards). A conformance condition is different in kind, meant to fail for some objects, and
nothing forbids it from reading the index. This build tests whether a resource bound lives at the protocol:
whether it discriminates (does the bound do work) and whether anything follows from it.

Stays in `Experiments/`; canonical untouched; nothing about P vs NP resolved. -/

open Chiralogy

namespace Chiralogy.CostProtocol

/-! ## Part 1: the structure -/

/-- A Blum numbering, abstractly: indices, a non-injective denotation, and a measure on the index. The
measure is total where the denotation is (both total here) and decidable (`ℕ`-valued). -/
structure Numbering (X B : Type) where
  I : Type
  denote : I → (X → X → B)
  Φ : I → X → ℕ

/-- Cost-conformance at a bound: the classification is denoted by some index whose cost is within `f`. -/
def CostConformantAt {X B : Type} (N : Numbering X B) (c : X → X → B) (f : X → ℕ) : Prop :=
  ∃ i, N.denote i = c ∧ ∀ x, N.Φ i x ≤ f x

/-! ## Part 2: the bound discriminates intensionally -/

/-- **Same denotation, different cost.** Two indices denote the identical classification yet carry different
cost. Cost lives on the index, below the denotation, so it is not read off `denote i`. -/
theorem same_denotation_different_cost :
    ∃ (N : Numbering (Fin 1) Bool) (i j : N.I),
      N.denote i = N.denote j ∧ N.Φ i ≠ N.Φ j :=
  ⟨⟨Bool, fun _ => fun _ _ => true, fun b _ => if b then 0 else 1⟩, true, false,
   rfl, fun h => absurd (congrFun h 0) (by decide)⟩

/-- **Conformance is not a function of the classification.** At a fixed bound, one index conforms and another
with the same denotation does not: the per-index condition discriminates two objects with the identical
classification. Contrast `NonDegenerate`, which is a predicate on the classification itself. -/
theorem conformance_is_not_a_function_of_the_classification :
    ∃ (N : Numbering (Fin 1) Bool) (i j : N.I) (f : Fin 1 → ℕ),
      N.denote i = N.denote j ∧ (∀ x, N.Φ i x ≤ f x) ∧ ¬ (∀ x, N.Φ j x ≤ f x) := by
  refine ⟨⟨Bool, fun _ => fun _ _ => true, fun b _ => if b then 0 else 1⟩, true, false, fun _ => 0,
    rfl, ?_, ?_⟩
  · intro _; show (0 : ℕ) ≤ 0; exact le_refl 0
  · intro h; exact absurd (h 0) (by decide)

/-! ## Part 3: does anything follow from the bound? -/

/-- **The kernel is unchanged under the bound.** The hole holds of every cost-conformant object, exactly as of
every member; the bound hypothesis is unused. The bound adds no obstruction: the layers are separate, not in
tension. -/
theorem kernel_unchanged_under_bound {X : Type} (N : Numbering X (Option Bool))
    (c : X → X → Option Bool) (f : X → ℕ) (_hconf : CostConformantAt N c f) :
    ¬ Function.Surjective c :=
  hole_uniform c

/-- **The only consequence is bound weakening.** Conformance at `f` gives conformance at any larger `f'`. This
is the order on bounds, definitional; no gap or speedup phenomenon follows, since Blum's gap and speedup
theorems require an effective enumeration and the recursion theorem, which the abstract numbering lacks. -/
theorem bound_weakening {X B : Type} (N : Numbering X B) (i : N.I) (f f' : X → ℕ)
    (hf : ∀ x, f x ≤ f' x) (hconf : ∀ x, N.Φ i x ≤ f x) : ∀ x, N.Φ i x ≤ f' x :=
  fun x => le_trans (hconf x) (hf x)

/-! ## Part 4: generality -/

/-- **Measure independence.** The intensional gap holds for any two distinct cost values, so no result depends
on `Φ` being time or space, only on cost being carried by the index. -/
theorem measure_independence (φ₀ φ₁ : ℕ) (h : φ₀ ≠ φ₁) :
    ∃ (N : Numbering (Fin 1) Bool) (i j : N.I),
      N.denote i = N.denote j ∧ N.Φ i ≠ N.Φ j :=
  ⟨⟨Bool, fun _ => fun _ _ => true, fun b _ => if b then φ₀ else φ₁⟩, true, false,
   rfl, fun heq => h (congrFun heq 0)⟩

/-! ## The verdict: discriminates but inert

Part 2: the bound discriminates intensionally. Two indices with the same denotation carry different cost
(`same_denotation_different_cost`), and the per-index condition separates two objects with the identical
classification (`conformance_is_not_a_function_of_the_classification`). Unlike the kernel's six discards, the
index is not selected-and-discarded: the bound does work in the condition it states. But this succeeds by
stipulation, cost being freely assignable on indices; success here is not yet content.

Part 3: nothing follows. The kernel ignores the bound (`kernel_unchanged_under_bound`, the hypothesis unused),
and the only statement true of cost-conformant objects is bound weakening (`bound_weakening`), the order on
bounds. A gap or speedup phenomenon would need an effective enumeration and the recursion theorem, which the
abstract numbering deliberately omits, so none is statable here.

Part 4: everything is measure-independent (`measure_independence`), depending only on cost being carried by
the index, not on time or space.

So the protocol sees cost inertly: the bound discriminates but entails nothing beyond its own statement,
vocabulary with content-free discrimination. Not the seventh discard, the bound is not invisible, but
expressible-and-inert. Nothing here is about P vs NP; this tests whether a bound is expressible at the
protocol, and it is, without consequence. -/

end Chiralogy.CostProtocol
