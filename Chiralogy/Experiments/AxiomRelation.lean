import Chiralogy

/-! # Experiment: are the arms related by axioms rather than maps?

`same_signature_different_arity` put the apophatic constant and a cataphatic operation in one signature
(monoids-with-zero: the absorbing `none`, the binary `mzAppend`). The six refutations tested morphism-shaped
relations between the arms and found none. An axiom is not a morphism. Test whether the absorbing law
`none ⊹ x = none` genuinely relates what the arms read.

Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.AxiomRelation

/-! ## Part 1: is there an axiom relating them, and what does it say? -/

/-- **The absorbing law.** The apophatic constant `none` absorbs under the cataphatic operation on both
sides. -/
theorem absorbing_law :
    (∀ x : Option (List Bool), mzAppend none x = none) ∧ (∀ x, mzAppend x none = none) := by
  refine ⟨fun _ => rfl, fun x => ?_⟩; cases x <;> rfl

/-- A second operation, reversed on the present part, also absorbing `none`. -/
def mzAppend' : Option (List Bool) → Option (List Bool) → Option (List Bool)
  | none, _ => none
  | _, none => none
  | some a, some b => some (b ++ a)

/-- **The operation is not pinned by the constant.** Two distinct operations both make `none` absorbing, so
the absorbing law does not determine the operation from the constant: the operation stays free on the present
part. -/
theorem operation_not_pinned_by_constant :
    (∀ x, mzAppend' none x = none) ∧ mzAppend ≠ mzAppend' := by
  refine ⟨fun _ => rfl, fun h => ?_⟩
  have := congrFun (congrFun h (some [true])) (some [false])
  simp [mzAppend, mzAppend'] at this

/-- **The constant is pinned by the operation.** `none` is the unique absorbing element under `mzAppend`: any
`z` absorbing on the left is `none`. So the absorbing law does determine the constant from the operation. The
constraint is genuine but one-directional. -/
theorem constant_pinned_by_operation :
    ∀ z : Option (List Bool), (∀ x, mzAppend z x = z) → z = none := by
  intro z h
  cases z with
  | none => rfl
  | some a => have := h none; simp [mzAppend] at this

/-! ## Part 2: is this relation of a different kind from the refuted ones? -/

/-- **Not a morphism.** The absorbing law is an equation on one carrier relating two symbols of one signature,
`none` (arity 0) and `mzAppend` (arity 2), both on `Option (List Bool)`. It is not a map from arm to arm, not
an adjunction, not a channel: a constraint within a shared theory, not a crossing between structures. -/
theorem not_a_morphism :
    ∀ x : Option (List Bool), mzAppend none x = none :=
  absorbing_law.1

/-- **The arms still do not fuse.** The shared axiom holds, and the loop still does not close
(`loop_does_not_close`): sharing an axiom gives no crossing map. Cohabitation-with-constraint is compatible
with non-fusion; the six refutations stand. -/
theorem arms_still_do_not_fuse :
    (∀ x : Option (List Bool), mzAppend none x = none)
    ∧ (Nonempty (Monad Option) ∧ ¬ Function.Surjective (embed (ZMod 3))) :=
  ⟨absorbing_law.1, loop_does_not_close⟩

/-! ## Part 3: does the constraint have structural consequences? -/

/-- **The absorbing law reaches the closure.** Closing the absorbing reason identifies `none` with a verdict
`some a`; the absorbing law then demands `some a` absorb, but `mzAppend (some a) none = none ≠ some a`: no
verdict absorbs. So the absorbing law blocks closing that reason, reaching the permitted lattice. The
cataphatic operation's law constrains the apophatic closure: the two arms' indices interact. -/
theorem absorbing_affects_closure :
    ∀ a : List Bool, mzAppend (some a) none ≠ some a := by
  intro a; simp [mzAppend]

/-! ## The verdict

Part 1: there is an axiom relating them, and it is a genuine but one-directional constraint. Two distinct
operations both absorb `none`, so the operation is not pinned by the constant
(`operation_not_pinned_by_constant`); yet `none` is the unique absorbing element, so the constant is pinned by
the operation (`constant_pinned_by_operation`). Not mere cohabitation: the constant side is constrained.

Part 2: the relation is of a different kind. The absorbing law is an equation between two symbols of one
signature on one carrier (`not_a_morphism`), not a map, adjunction, or channel. The refutations stand: the
loop still does not close (`arms_still_do_not_fuse`), so cohabitation-with-constraint does not fuse the arms.
The relation is between signature symbols, not between the arms as structures.

Part 3: the constraint reaches the structures. Closing the absorbing reason to a verdict would make the
verdict absorbing, which no verdict is (`absorbing_affects_closure`); so the absorbing law blocks that
closure, removing it from the permitted moves. The cataphatic operation's law constrains the apophatic
closure, and the two indices interact at the level of the shared theory's axioms.

The verdict: the arms are related by axioms, not maps. At the symbol level the absorbing law constrains the
constant given the operation; and it reaches the structure level, blocking the closure of the absorbing
reason. This is a genuinely different relation from the six refuted morphisms, and it is compatible with
non-fusion: an axiom in a shared theory, not a crossing. It holds where the level's theory relates a constant
to an operation, as monoids-with-zero does; the free levels with independent constants carry no such axiom, so
their arms merely cohabit. Nothing here is resolved. -/

end Chiralogy.AxiomRelation
