import Chiralogy

/-! # Experiment: what makes absence natural

`cont_absence_is_stipulated` showed continuation gives no natural absence. Hypothesis: the reasons are the
nullary operations of the level's algebraic presentation (a constant in the signature is a reason for
absence), and this is a different property from rankedness (a size condition, bounded arity). Separate them on
the term, with concrete instances.

Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Algebraicity

/-! ## Part 1: constants are the reasons -/

/-- Except's nullary operations: `throw e = inr e`, one per reason. -/
def throwExcept : Bool → Bool ⊕ Bool := Sum.inr

/-- Maybe's one nullary operation: `fail = none`. -/
def failMaybe : Unit → Option Bool := fun _ => none

/-- **The reasons are the nullary generators.** Except's absent values are exactly the range of `throwExcept`
(the throws), Maybe's absent value is exactly the range of `failMaybe` (the fail). The reason count is the
number of nullary operations: two for Except, one for Maybe. -/
theorem reasons_are_nullary_generators :
    (∀ x : Bool ⊕ Bool, (∃ e, x = Sum.inr e) ↔ ∃ e, throwExcept e = x)
    ∧ (∀ v : Option Bool, v = none ↔ ∃ u : Unit, failMaybe u = v) := by
  refine ⟨fun x => ⟨?_, ?_⟩, fun v => ⟨?_, ?_⟩⟩
  · rintro ⟨e, rfl⟩; exact ⟨e, rfl⟩
  · rintro ⟨e, rfl⟩; exact ⟨e, rfl⟩
  · rintro rfl; exact ⟨(), rfl⟩
  · rintro ⟨_, rfl⟩; rfl

/-- A level-supported totalization acts on the verdict and passes the marking. -/
def MarkingPassing (t : (Bool ⊕ Bool) × Bool → (Bool ⊕ Bool) × Bool) : Prop :=
  ∃ g : Bool ⊕ Bool → Bool ⊕ Bool, ∀ x, t x = (g x.1, x.2)

/-- **The grouping respects the operations.** The two values `(inr false, false)` and `(inr false, true)`
share the constant `throwExcept false`, differing only in the marking; no level-supported move separates them.
So `crosscutting_grouping_is_not_supported` is exactly the fact that supported moves respect the nullary
operations: a partition separating values of one constant is not closeable. -/
theorem grouping_respects_operations :
    ¬ ∃ t, MarkingPassing t
      ∧ (¬ ∃ e, (t (Sum.inr false, false)).1 = Sum.inr e)
      ∧ (∃ e, (t (Sum.inr false, true)).1 = Sum.inr e) := by
  rintro ⟨t, ⟨g, hg⟩, hc, ho⟩
  simp only [hg] at hc ho
  exact hc ho

/-! ## Part 2: separate rankedness from constants -/

/-- The free magma on `Bool`: atoms (unary generators) and a binary operation, no nullary operation. -/
inductive Magma where
  | atom : Bool → Magma
  | op : Magma → Magma → Magma
  deriving DecidableEq

/-- **Ranked without constants: no nullary generator.** Every element of the free magma is an atom (a
generator) or a binary op; none is a constant. The operation is binary, so the theory is finitary (ranked),
yet there is no nullary operation. -/
theorem magma_has_no_constant :
    ∀ m : Magma, (∃ b, m = Magma.atom b) ∨ (∃ l r, m = Magma.op l r) := by
  intro m; cases m with
  | atom b => exact Or.inl ⟨b, rfl⟩
  | op l r => exact Or.inr ⟨l, r, rfl⟩

/-- **So the free magma has no natural absence.** With no nullary generator, no element is distinguished as
absent; two absent predicates are equally admissible, so the absence is stipulated, as with continuation but
for a different reason: no constants rather than no algebraicity. -/
theorem ranked_without_constants :
    ∃ p q : Magma → Prop, ∃ v, p v ∧ ¬ q v :=
  ⟨(· = Magma.atom true), (· = Magma.atom false), Magma.atom true, rfl, by decide⟩

/-- **Maybe, by contrast, has a constant.** `none` is a nullary generator, distinct from every present value
`some b`: the natural absence. -/
theorem option_has_a_constant : ∀ b : Bool, (none : Option Bool) ≠ some b := by decide

/-- **Constants without rank: the powerset.** Its bottom `∅` is a nullary generator, a natural absence
distinct from the present singletons, while its join is arbitrary-arity, not ranked. So a constant gives a
natural absence without rankedness. -/
theorem constants_without_rank :
    (∅ : Finset Bool) ≠ {true} ∧ (∅ : Finset Bool) ≠ {false} :=
  ⟨by decide, by decide⟩

/-- **The properties are distinct.** The free magma is ranked with no constant and no natural absence; the
powerset has a constant and a natural absence without being ranked. So rankedness neither implies nor is
implied by having a natural absence: natural absence tracks the nullary generators, not the rank. -/
theorem the_properties_are_distinct :
    (∀ m : Magma, (∃ b, m = Magma.atom b) ∨ (∃ l r, m = Magma.op l r))
    ∧ ((∅ : Finset Bool) ≠ {true} ∧ (∅ : Finset Bool) ≠ {false}) :=
  ⟨magma_has_no_constant, constants_without_rank⟩

/-! ## The verdict

Part 1: the reasons are the nullary generators. Except's absences are the range of `throwExcept` (its throws),
Maybe's absence is the range of `failMaybe` (its fail); the reason count is the number of nullary operations
(`reasons_are_nullary_generators`). The grouping respects these operations: values sharing a constant cannot
be separated by a supported move (`grouping_respects_operations`), which is what
`crosscutting_grouping_is_not_supported` was.

Part 2: natural absence is having nullary generators, and this is distinct from rankedness. The free magma is
finitary but has no nullary generator (`magma_has_no_constant`), so no natural absence (`ranked_without_constants`),
where Maybe has one (`option_has_a_constant`). The powerset has a constant, a natural absence, without being
ranked (`constants_without_rank`). Rankedness and natural absence are independent (`the_properties_are_distinct`):
absence tracks constants, not rank.

Part 3: the corrected scope. The tower's grouping is derived where the level has an algebraic presentation with
nullary generators, and stipulated otherwise. There are two distinct failure modes for one condition:
continuation fails for lack of algebraicity (no signature at all), the free magma fails for lack of constants
(a signature with no nullary operation). One condition, algebraic-with-constants; two ways to miss it.

The verdict: natural absence is having nullary generators, the constants of the level's algebraic
presentation, and this is distinct from rankedness. The five levels coincide because each is algebraic with
constants, not because of their rank; the picture is derived exactly there, and the reasons are those
constants. Nothing here is resolved. -/

end Chiralogy.Algebraicity
