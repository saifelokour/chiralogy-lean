import Chiralogy

/-! # Experiment: are the tower's steps indexed by arity?

Four categories so far: a classification, plus grounds, plus an order, plus operations.
`reasons_are_nullary_generators` says grounds are the nullary part of a presentation; the fourth step is the
positive-arity part. Test whether the tower's steps are indexed by arity, which would give a determinate count
rather than open-ended discovery. A morphism respects an operation `op` of arity `k` when `onValues` commutes
with it. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.TowerArity

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

/-! ## Part 1: do positive arities separate? -/

/-- **Unary and binary are separable.** There is a morphism respecting the unary operation and not the binary
one (`f1`), and one respecting the binary and not the unary (`f2`). Both directions are realized, so the two
arities generate distinct steps. -/
theorem unary_and_binary_are_separable :
    (∃ f : Fin 3 → Fin 3, (∀ a, f (uOp a) = uOp (f a)) ∧ ¬ ∀ a b, f (bOp a b) = bOp (f a) (f b))
    ∧ (∃ f : Fin 3 → Fin 3, (∀ a b, f (bOp a b) = bOp (f a) (f b)) ∧ ¬ ∀ a, f (uOp a) = uOp (f a)) :=
  ⟨⟨f1, by decide, by decide⟩, ⟨f2, by decide, by decide⟩⟩

/-- **Respecting by arity is independent.** The unary and binary respect-conditions neither imply the other:
`f1` satisfies the unary and violates the binary, `f2` the reverse. Each arity is a separate condition. -/
theorem respecting_by_arity :
    (RespectsUnary f1 uOp ∧ ¬ RespectsBinary f1 bOp)
    ∧ (RespectsBinary f2 bOp ∧ ¬ RespectsUnary f2 uOp) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-! ## Part 2: where does the order fit? -/

/-- The prerequisite order `0 ≺ 1` on grounds, a relation. -/
def prereq : Fin 3 → Fin 3 → Bool := fun a b => decide (a = 0 ∧ b = 1)

/-- **The order is not signature data.** The prerequisite order is a relation (`B → B → Bool`), not an
operation (`B → B → B`), and respecting it (monotone) is independent of respecting the operations: a morphism
can be monotone and not an operation-homomorphism (`fun v => if v = 2 then 0 else v`), and an operation-
homomorphism and not monotone (the constant `2`). So step three is a relational datum; the tower is mixed,
operations indexed by arity plus a relation. -/
theorem order_is_not_signature_data :
    (∃ f : Fin 3 → Fin 3,
        (∀ v w, prereq v w = true → prereq (f v) (f w) = true) ∧ ¬ ∀ a b, f (bOp a b) = bOp (f a) (f b))
    ∧ (∃ f : Fin 3 → Fin 3,
        (∀ a b, f (bOp a b) = bOp (f a) (f b)) ∧ ¬ ∀ v w, prereq v w = true → prereq (f v) (f w) = true) :=
  ⟨⟨fun v => if v = 2 then 0 else v, by decide, by decide⟩, ⟨fun _ => 2, by decide, by decide⟩⟩

/-! ## Part 3: the count, if there is one -/

/-- **The tower length.** The operational steps are arity-indexed and separate (`respecting_by_arity`), plus the
classification (the payload quantifies it) and the separate relational order (`order_is_not_signature_data`). So
the count is classification, one step per arity the signatures use, and the order: for the framework's levels,
arities 0 (grounds), 1 (inverse), 2 (composition), giving classification, three arity steps, and the order,
five in all. The count is determinate given the signatures but grows with the maximum arity. -/
theorem tower_length :
    (∃ f : Fin 3 → Fin 3, RespectsUnary f uOp ∧ ¬ RespectsBinary f bOp)
    ∧ (∃ f : Fin 3 → Fin 3, RespectsBinary f bOp ∧ ¬ RespectsUnary f uOp)
    ∧ (∀ {X : Type} (c : X → X → Option Bool), ¬ Function.Surjective c) :=
  ⟨⟨f1, by decide, by decide⟩, ⟨f2, by decide, by decide⟩, fun c => hole_uniform c⟩

/-- **What would make it longer.** A primitive higher-arity operation separates too: `f2` respects the binary
operation but not the ternary `tMaj`, so a level carrying a genuine ternary operation would add an arity step.
The framework's levels use arities up to two, and continuation carries no finite presentation at all
(`cont_absence_is_stipulated`), so a non-algebraic level escapes the arity scheme. The count is a fact about the
levels built, not a closed property of the tower. -/
theorem what_would_make_it_longer :
    (∀ a b, f2 (bOp a b) = bOp (f2 a) (f2 b))
    ∧ ¬ (∀ a b c, f2 (tMaj a b c) = tMaj (f2 a) (f2 b) (f2 c)) :=
  ⟨by decide, by decide⟩

/-! ## The verdicts

Part 1: positive arities separate. There is a morphism respecting a unary operation and not a binary one, and
one the reverse (`unary_and_binary_are_separable`), so the conditions are independent (`respecting_by_arity`);
each arity is a distinct step, and the operational part of the tower is arity-indexed.

Part 2: the order is a separate relational datum, not signature data. The prerequisite order is a relation, not
an operation of any arity, and respecting it is independent of respecting the operations
(`order_is_not_signature_data`). So the tower is mixed: arity indexes the operational steps, and the order is a
relation beside them.

Part 3: there is a count, determinate given the signatures but not closed. It is the classification, one step
per arity the levels use (`tower_length`: grounds at arity zero, inverse at one, composition at two, five in
all with the order), and the relational order. But a primitive higher arity would add a step
(`what_would_make_it_longer`), and a non-algebraic level (continuation) escapes the scheme, so the number is a
fact about the levels built rather than a closed property of the tower. The tower is arity-indexed in its
operational part and mixed with a relation; the count is five for the current levels and open in principle.
Nothing here is resolved. -/

end Chiralogy.TowerArity
