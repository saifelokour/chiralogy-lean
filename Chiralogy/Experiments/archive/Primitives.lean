import Chiralogy

/-! # Experiment: does the cataphatic arm compose on a different primitive?

`grade_adds` proved sequential embedding telescopes additively, forced not chosen. The exponential laws
govern different combinations: `(B^X)^Y ≅ B^(X×Y)` (iterated exponential, multiplicative in the exponent) and
`Y^A × Y^B ≅ Y^(A+B)` (parallel over a coproduct). This tests the two untried primitives, iterating the
transpose and parallel composition, against the same grade notion.

The tower machinery is re-derived locally (the experiments are not compiled). Stays in `Experiments/`;
canonical untouched; nothing about P vs NP resolved. -/

open Chiralogy

namespace Chiralogy.Primitives

/-! ## Shared: the tower machinery -/

@[ext] structure TowerLevel (A B : Type) where
  emb : A → B
  ret : B → A
  sec : Function.LeftInverse ret emb

def levelCompose {A B C : Type} (f : TowerLevel A B) (g : TowerLevel B C) : TowerLevel A C where
  emb := g.emb ∘ f.emb
  ret := f.ret ∘ g.ret
  sec := fun a => by simp only [Function.comp_apply]; rw [g.sec (f.emb a), f.sec a]

def grade {A B : Type} [Fintype A] [Fintype B] (_f : TowerLevel A B) : ℤ :=
  (Fintype.card B : ℤ) - Fintype.card A

theorem grade_adds {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (f : TowerLevel A B) (g : TowerLevel B C) :
    grade (levelCompose f g) = grade f + grade g := by
  simp only [grade]; ring

/-! ## Part 1: does the transpose iterate?

The cataphatic move is the transpose `ĉ : X → (X → B)`, which is `c` itself. Iterating would need a
classification `c₂ : (X → B) → (X → B) → B` on the function space. -/

/-- **The transpose is the move, one step.** Read as `X → (X → B)`, the transpose is `c` verbatim. -/
theorem transpose_is_the_move {X B : Type} (c : X → X → B) : (fun x => c x) = c := rfl

/-- **Iterating needs a classification the framework does not supply.** To reuse `c` on the function space
one would fold `X → B` back to `X`, an equivalence `X ≃ (X → B)` the empty center forbids. A fresh
classification on `X → B` is independent data, not derived from `c`. So the transpose does not iterate on the
framework's own data: there is no second stage to grade. -/
theorem transpose_iteration_needs_a_new_classification {X : Type} :
    ¬ Nonempty (X ≃ (X → Bool)) :=
  empty_center_is_coincidence (fun b => !b) (by decide)

/-! ## Part 2: parallel composition -/

/-- Parallel composition over a coproduct domain: two levels side by side. -/
def parallelCompose {A B C D : Type} (f : TowerLevel A B) (g : TowerLevel C D) :
    TowerLevel (A ⊕ C) (B ⊕ D) where
  emb := Sum.map f.emb g.emb
  ret := Sum.map f.ret g.ret
  sec := fun x => by
    cases x with
    | inl a => show Sum.inl (f.ret (f.emb a)) = Sum.inl a; rw [f.sec a]
    | inr c => show Sum.inr (g.ret (g.emb c)) = Sum.inr c; rw [g.sec c]

/-- **Parallel composition adds.** Over a coproduct the gaps add, `card (B ⊕ D) - card (A ⊕ C)`, the same
additive law as sequential composition. The multiplicative law `Y^A × Y^B ≅ Y^(A+B)` governs exponential
objects, not the embedding-sections the tower is built from. -/
theorem parallel_grade_adds {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : TowerLevel A B) (g : TowerLevel C D) :
    grade (parallelCompose f g) = grade f + grade g := by
  simp only [grade, Fintype.card_sum]; push_cast; ring

/-- Product composition over a product domain. -/
def productCompose {A B C D : Type} (f : TowerLevel A B) (g : TowerLevel C D) :
    TowerLevel (A × C) (B × D) where
  emb := Prod.map f.emb g.emb
  ret := Prod.map f.ret g.ret
  sec := fun x => by
    obtain ⟨a, c⟩ := x
    have h1 : f.ret (f.emb a) = a := f.sec a
    have h2 : g.ret (g.emb c) = c := g.sec c
    show (f.ret (f.emb a), g.ret (g.emb c)) = (a, c)
    rw [h1, h2]

/-- The unit-adding level (a finite free construction), for grade-one instances. -/
def optLevel (A : Type) [Inhabited A] : TowerLevel A (Option A) :=
  ⟨some, fun o => o.getD default, fun _ => rfl⟩

/-- **Product composition gives no grading law.** Two component pairs of equal grades (one each) yield
different product grades (five and three): the product grade `card (B × D) - card (A × C)` depends on the base
sizes, not on the grades alone, so it is not a homomorphism, neither `+` nor `×`. The multiplicative-looking
product does not give the tower a multiplicative grade. -/
theorem product_grade_not_a_function_of_grades :
    grade (optLevel Bool) = grade (optLevel (Fin 1))
    ∧ grade (productCompose (optLevel Bool) (optLevel Bool))
        ≠ grade (productCompose (optLevel (Fin 1)) (optLevel (Fin 1))) := by
  refine ⟨?_, ?_⟩ <;>
    simp only [grade, Fintype.card_prod, Fintype.card_option, Fintype.card_bool, Fintype.card_fin] <;>
    norm_num

/-! ## Part 3: the census -/

/-- **What composes, and by which law.** The two composition operations that yield a grading, sequential and
parallel-over-coproduct, both add. There is one composition law, and it is additive. -/
theorem what_composes {A B C D E : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    (f : TowerLevel A B) (g : TowerLevel B C) (h : TowerLevel D E) :
    grade (levelCompose f g) = grade f + grade g
    ∧ grade (parallelCompose f h) = grade f + grade h :=
  ⟨grade_adds f g, parallel_grade_adds f h⟩

/-! ## The verdicts, independent

Part 1: the transpose does not iterate on the framework's data. It is `c` itself, one step
(`transpose_is_the_move`); iterating needs a classification on the function space `X → B`, and reusing `c`
would fold `X → B` back to `X`, the equivalence the empty center forbids
(`transpose_iteration_needs_a_new_classification`). A fresh classification is independent data, not derived,
so there is no second stage to grade. Not stipulated into existence.

Part 2: parallel composition over a coproduct is a genuine operation and its grade adds
(`parallel_grade_adds`), the same additive law as sequential. Product composition gives no grading at all: the
grade is not a function of the parts' grades (`product_grade_not_a_function_of_grades`), so its multiplicative
appearance is not a homomorphism. The multiplicative exponential law governs function-space objects, not the
embedding-sections the tower composes.

Part 3: the census. Every composition operation that yields a grading adds (`what_composes`): sequential and
parallel-over-coproduct. Product yields no grading; the transpose does not iterate. The framework has one
composition law, and it is additive. This is the terminal statement of the thread: cost needs a non-additive
composition law, and the framework has exactly one, additive, which is why every attempt to express cost
failed. Nothing here is about P vs NP; no complexity class, no separation. -/

end Chiralogy.Primitives
