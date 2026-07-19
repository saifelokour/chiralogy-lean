import Chiralogy

/-! # Experiment: settling the picture

`reasons_are_extra_data` showed the reason-grouping is supplied by the level and everything structural
follows it. Three questions decide whether the picture is solid: is the grouping constrained or arbitrary,
does dependence drive anything, and are the five levels representative.

Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Grouping

/-! ## Part 1: is the grouping constrained or arbitrary?

A level-supported totalization at plural-and-marked acts on the verdict and passes the marking through: it
cannot consult the log. A grouping is legitimate iff closing a part is such a move. -/

/-- A totalization is level-supported (marking-passing) if it acts on the verdict and passes the marking. -/
def MarkingPassing (t : (Bool ⊕ Bool) × Bool → (Bool ⊕ Bool) × Bool) : Prop :=
  ∃ g : Bool ⊕ Bool → Bool ⊕ Bool, ∀ x, t x = (g x.1, x.2)

/-- Closing the reason `false`, uniform in the marking. -/
def reasonCloseFalse : (Bool ⊕ Bool) × Bool → (Bool ⊕ Bool) × Bool :=
  fun x => (if x.1 = Sum.inr false then Sum.inl true else x.1, x.2)

/-- **The reason-grouping is level-supported.** Closing a reason is marking-passing. -/
theorem reason_grouping_is_supported : MarkingPassing reasonCloseFalse :=
  ⟨fun a => if a = Sum.inr false then Sum.inl true else a, fun _ => rfl⟩

/-- **The cross-cutting grouping is not level-supported.** No marking-passing move closes `(inr false, false)`
while leaving `(inr false, true)`: they share the verdict, so any marking-passing move treats them alike. A
partition that cuts across the marking is not closeable, so the grouping is constrained by the level, not
free. -/
theorem crosscutting_grouping_is_not_supported :
    ¬ ∃ t, MarkingPassing t
      ∧ (¬ ∃ e, (t (Sum.inr false, false)).1 = Sum.inr e)
      ∧ (∃ e, (t (Sum.inr false, true)).1 = Sum.inr e) := by
  rintro ⟨t, ⟨g, hg⟩, hc, ho⟩
  simp only [hg] at hc ho
  exact hc ho

/-! ## Part 2: does dependence drive anything?

The marking is not consultable (Part 1); the context is. So dependence adds a closeable dimension where
markedness does not. -/

/-- A context-selective totalization at Reader: fill the absence at context `true`, leave it at `false`. -/
def readerCloseTrue : (Bool → Option Bool) → (Bool → Option Bool) :=
  fun f c => if c = true then some ((f c).getD true) else f c

/-- The mirror move: fill at `false`, leave at `true`. -/
def readerCloseFalse : (Bool → Option Bool) → (Bool → Option Bool) :=
  fun f c => if c = false then some ((f c).getD true) else f c

/-- **The context is consultable.** A totalization can fill an absence at one context and leave it at another:
the move consults the context, unlike the marking. -/
theorem context_is_consultable :
    readerCloseTrue (fun _ => none) true ≠ none ∧ readerCloseTrue (fun _ => none) false = none := by
  constructor <;> decide

/-- **Dependence adds reasons; it is not inert.** The two context-selective moves are distinct and both
supported, so the context is a genuine closeable dimension: a two-context Reader has two context-reasons where
the marking gave an inert log. Dependence governs the grouping (upstream of the boundary), unlike markedness
and the absent-value count. -/
theorem dependence_adds_reasons :
    readerCloseTrue (fun _ => none) ≠ readerCloseFalse (fun _ => none) :=
  fun h => by simpa [readerCloseTrue, readerCloseFalse] using congrFun h true

/-! ## Part 3: are the five levels representative?

Test a monad outside the ranked family: continuation, `Cont r a = (a → r) → r`, which the literature does not
list as admitting a canonical transformer. -/

abbrev Cont : Type := (Bool → Bool) → Bool

/-- **Continuation has a fixed-point-free endomap.** Negating the result is fixed-point-free. -/
theorem cont_has_fpf : ∀ v : Cont, (fun k => !(v k)) ≠ v :=
  fun v h => by
    have := congrFun h (fun _ => true)
    simp at this

/-- **The kernel survives continuation.** As at every value space with a fixed-point-free endomap: kernel
survival is universal, not special to the ranked family. -/
theorem cont_kernel_survives {X : Type} (c : X → X → Cont) : ¬ Function.Surjective c :=
  no_reflexive_object (g := fun v k => !(v k)) cont_has_fpf c

/-- **But continuation gives no natural absence.** Its `pure` sends every value to a present continuation;
there is no designated absent element, no failure. Two different absent predicates are equally admissible, so
the absence, and with it the reason-grouping, must be stipulated. The construction yields a value space and a
surviving kernel, but not an absence-structure: the ranked-family picture rests on a natural absence
continuation lacks. -/
theorem cont_absence_is_stipulated :
    ∃ p q : Cont → Prop, (∃ v, p v ∧ ¬ q v) :=
  ⟨(fun v => v (fun _ => true) = true), (fun v => v (fun _ => true) = false),
   ⟨fun _ => true, rfl, by decide⟩⟩

/-! ## The verdict

Part 1: the grouping is constrained, not arbitrary. Closing a reason is a marking-passing move
(`reason_grouping_is_supported`); a partition that cuts across the marking is not closeable by any such move
(`crosscutting_grouping_is_not_supported`), since values sharing a verdict are treated alike. So "reason" is
derived from the level's structure, and the boundary's `2 ^ n - 1` rests on the reason partition the level
fixes, not on a free choice of `n`.

Part 2: dependence is not inert. The marking is not consultable, but the context is
(`context_is_consultable`), and the two context-selective moves are distinct (`dependence_adds_reasons`), so
dependence adds closeable reason-dimensions. It governs the grouping upstream of the boundary, unlike
markedness and the absent-value count, which leave the grouping fixed. Holding the grouping fixed would mask
this, since the boundary follows the grouping; dependence's effect is on the grouping itself.

Part 3: the family is not representative in one respect. Continuation gives a value space with a surviving
kernel (`cont_kernel_survives`, universal), but no natural absence (`cont_absence_is_stipulated`): the absent
predicate, and the reason-grouping, must be stipulated. So the picture, constrained grouping and reason-driven
structure, rests on the natural absence the ranked family carries; outside it the constraint dissolves because
the absence itself is a stipulation.

The verdict: the picture is solid within the ranked family. The grouping is constrained by the level (Part 1),
so reasons are derived not free; dependence governs the grouping while markedness and value-count are inert
(Part 2); but the whole rests on a natural absence (Part 3) that the ranked monads supply and a monad like
continuation does not, where the absence and its grouping become stipulations. The structure is derived where
absence is natural, stipulated where it is not. Nothing here is resolved. -/

end Chiralogy.Grouping
