import Chiralogy

/-! # Experiment: are there levels with dependent reasons?

The permitted lattice is Boolean because the reasons are independent, the closeable sets all subsets. Test
whether a level can have dependent reasons, closing one forcing another, giving a proper Heyting algebra. If
the level's theory relates the constants (closing `e1` forces closing `e2`), the closeable sets are the
up-sets of the forcing relation, and the up-set lattice of a nondiscrete order is Heyting but not Boolean.

Reasons are `Bool` (`lo = false`, `hi = true`); the forcing is `lo` below `hi`. Stays in `Experiments/`;
canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.DependentReasons

/-! ## Part 1: a level with a forcing relation -/

/-- The quotient action of closing a set of reasons on `Bool ⊕ Bool` (free Except). -/
def closeE (S : Bool → Bool) : Bool ⊕ Bool → Bool ⊕ Bool
  | Sum.inr e => bif S e then Sum.inl true else Sum.inr e
  | Sum.inl b => Sum.inl b

/-- The stipulated severity order: closing `lo` forces closing `hi`. A closure is an up-set of this order. -/
abbrev IsUpSet (close : Bool → Bool) : Prop := close false = true → close true = true

/-- **The closeable sets are the up-sets.** With the forcing, the empty closure, `{hi}`, and the full closure
are up-sets, but `{lo}` (closing `lo` while leaving `hi` open) is not: it violates the forcing. The
supported totalizations are the up-sets, not arbitrary subsets. -/
theorem closeable_sets_are_up_sets :
    IsUpSet (fun _ => false)
    ∧ IsUpSet (fun r => decide (r = true))
    ∧ IsUpSet (fun _ => true)
    ∧ ¬ IsUpSet (fun r => decide (r = false)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **The forcing is stipulated, not carried.** In the free Except, closing `lo` alone is a legitimate
quotient: it identifies the throw `inr false` with a verdict and leaves `inr true` untouched, and nothing in
the free theory forces closing `hi`. The order relating the constants is an added axiom, a non-free quotient,
imposed by us. A naturally dependent level would carry such a relation in its data, which the free
constructions of the tower do not. -/
theorem forcing_is_stipulated :
    (closeE (fun r => decide (r = false)) (Sum.inr false) = Sum.inl true)
    ∧ (closeE (fun r => decide (r = false)) (Sum.inr true) = Sum.inr true)
    ∧ ¬ IsUpSet (fun r => decide (r = false)) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## Part 2: the up-set lattice is properly Heyting

The three up-sets form the chain `0 = ∅ < 1 = {hi} < 2 = {lo,hi}`, modelled as `Fin 3`. -/

def cmeet3 (a b : Fin 3) : Fin 3 := min a b
def cjoin3 (a b : Fin 3) : Fin 3 := max a b
def cimp3 (a b : Fin 3) : Fin 3 := if a ≤ b then 2 else b

/-- **The up-set lattice.** The three up-sets ordered as a chain, with meet and join. -/
theorem up_set_lattice :
    cmeet3 1 2 = 1 ∧ cjoin3 1 2 = 2 ∧ cmeet3 0 1 = 0 := by decide

/-- **Heyting but not Boolean.** The residuation holds exhaustively (`cimp3` is the relative
pseudo-complement, so the lattice is Heyting), yet `{hi}` has no complement (`{hi} ⊔ ¬{hi} ≠ ⊤`) and
`¬¬{hi} ≠ {hi}`. Not a Boolean algebra: dependent reasons give a proper Heyting algebra. This is not a
powerset (three elements, not a power of two), so it is genuinely dependent, not fewer independent reasons. -/
theorem is_heyting_not_boolean :
    (∀ a b c : Fin 3, cmeet3 a c ≤ b ↔ c ≤ cimp3 a b)
    ∧ cjoin3 1 (cimp3 1 0) ≠ 2
    ∧ cimp3 (cimp3 1 0) 0 ≠ 1 := by decide

/-- **What negation means here.** The negation `¬{hi} = {hi} ⇒ ⊥` is `∅`, smaller than the naive complement
`{lo}`, which the forcing excludes (`{lo}` is not an up-set). With dependence, negating a closure collapses
past the forced reasons rather than taking the set complement. -/
theorem what_negation_means_here :
    cimp3 1 0 = 0 ∧ ¬ IsUpSet (fun r => decide (r = false)) := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## Part 3: the boundary under dependence -/

/-- **The permitted count is the number of up-sets, fewer than the independent case.** Two permitted (the
non-full up-sets `∅`, `{hi}`) against three for two independent reasons: dependence removes `{lo}` from the
closeable sets. -/
theorem permitted_count_under_dependence :
    (Finset.univ.filter (fun close : Bool → Bool => IsUpSet close ∧ ¬ ∀ r, close r = true)).card = 2
    ∧ (Finset.univ.filter (fun close : Bool → Bool => ¬ ∀ r, close r = true)).card = 3 := by decide

/-- **The prohibition is still singular.** Exactly one up-set is the full closure, the forbidden one; every
non-full up-set is consistent. Dependence reduces the permitted set but forbids no more than the independent
case. -/
theorem prohibition_still_singular :
    (Finset.univ.filter (fun close : Bool → Bool => IsUpSet close ∧ ∀ r, close r = true)).card = 1 := by decide

/-! ## The verdict

Part 1: a level with a forcing relation is constructible, and its closeable sets are the up-sets of the order
(`closeable_sets_are_up_sets`), not arbitrary subsets. But the forcing is stipulated, not carried
(`forcing_is_stipulated`): the free Except permits closing `lo` alone, so the order relating the constants is
an added, non-free axiom. The free constructions of the tower carry no such relation; a naturally dependent
level would have to supply one.

Part 2: given the order, the up-set lattice is properly Heyting. The residuation holds exhaustively, yet
`{hi}` has no complement and `¬¬{hi} ≠ {hi}` (`is_heyting_not_boolean`): not Boolean. It is a three-element
chain, not a powerset, so genuinely dependent, not fewer independent reasons. The negation collapses past the
forced reasons (`what_negation_means_here`), smaller than the set complement.

Part 3: the permitted moves are the up-sets, two rather than three (`permitted_count_under_dependence`); the
prohibition stays singular, exactly the full closure forbidden (`prohibition_still_singular`).

The verdict: dependent reasons give a proper Heyting algebra, and with them the ethics would be intuitionistic,
double negation failing and some closures committing to others. But the dependence is stipulated: the tower's
free levels have independent constants (Boolean), by freeness. An intuitionistic ethics requires a non-free
theory relating the constants, outside the free family the levels inhabit. The construction shows what such a
level would be, not that the tower contains one. Nothing here is resolved. -/

end Chiralogy.DependentReasons
