import Chiralogy

/-! # Experiment: combining the departures, and further directions

Non-freeness has two effects: forcing (constants to constants; closeable sets become up-sets; Heyting) and
blocking (a constant to an operation; a closure removed; the top absent). The space is the subvariety lattice,
which axioms a level carries. The arity split has a name: the full non-nullary reduct is the algebra with the
same universe and only the positive-arity operations, what the cataphatic side reads; the constants are what
the apophatic side reads. Test whether forcing and blocking combine, and whether there are further directions.

Reasons `Bool`, closures `Bool → Bool`. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Departures

abbrev IsUpSet (close : Bool → Bool) : Prop := close false = true → close true = true
abbrev IsBlockable (close : Bool → Bool) : Prop := close false = false

/-! ## Part 1: do forcing and blocking combine? -/

/-- A level carrying both: `lo` forces `hi`, and `lo` is absorbing (blocked). -/
abbrev IsCombined (close : Bool → Bool) : Prop :=
  (close false = true → close true = true) ∧ close false = false

/-- **Both departures are active.** Forcing excludes `{lo}` (not an up-set); blocking excludes the full
closure (it closes the absorbing `lo`). -/
theorem both_departures :
    ¬ IsUpSet (fun r => decide (r = false)) ∧ ¬ IsBlockable (fun _ => true) := by
  refine ⟨by decide, by decide⟩

/-- **The combined family, computed from the moves.** Two closeable sets, `∅` and `{hi}`: blocking `lo` makes
the forcing vacuous (`lo` never closed, so nothing forces `hi`), so the combination is the blocking family,
not up-sets-minus-blocked as one might assume. Compare free four, forcing three, blocking two. -/
theorem combined_family :
    (Finset.univ.filter (fun c : Bool → Bool => IsCombined c)).card = 2 := by decide

/-- **The combination is Boolean, not Heyting.** The family is the two-element chain `∅ < {hi}`, and its top
`{hi}` has a complement `∅` (join the top, meet the bottom). Blocking the forcing's lower element removed the
top of the forcing chain, undoing its non-Booleanness: the departures interact, blocking collapsing forcing's
Heyting order back to Boolean. Blocking a reason outside the forcing order would instead leave the Heyting
order intact. -/
theorem combination_is_boolean :
    IsCombined (fun r => decide (r = true))
    ∧ IsCombined (fun _ => false)
    ∧ cjoin (fun r => decide (r = true)) (fun _ => false) = (fun r => decide (r = true))
    ∧ cmeet (fun r => decide (r = true)) (fun _ => false) = (fun _ => false) := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> · funext r; cases r <;> decide

/-! ## Part 2: are there further directions? -/

/-- **Operation-operation axioms leave the closeable family untouched.** Associativity holds for `mzAppend`
(an axiom among positive-arity symbols), but the closeable family is defined on closures over the constants,
not on the operation, so it is unchanged. Axioms in the reduct do not reach the apophatic index: the arity
split doing work. -/
theorem operation_operation_axioms :
    (∀ a b c : Option (List Bool), mzAppend (mzAppend a b) c = mzAppend a (mzAppend b c))
    ∧ (Finset.univ.filter (fun c : Bool → Bool => IsBlockable c)).card = 2 := by
  refine ⟨fun a b c => ?_, by decide⟩
  cases a <;> cases b <;> cases c <;> simp [mzAppend, List.append_assoc]

/-- A second operation absorbing `none`, reversed on the present part. -/
def mzAppend' : Option (List Bool) → Option (List Bool) → Option (List Bool)
  | none, _ => none
  | _, none => none
  | some a, some b => some (b ++ a)

/-- **The constant does not constrain the operation.** The absorbing law pins the constant from the operation,
not the reverse: two distinct operations share the absorbing constant `none`. So a constant-constrains-operation
axiom reaching the closeable family is not realized in these instances; it would have to be stipulated. The
fourth cell is empty here. -/
theorem operation_constant_other_direction :
    (∀ x, mzAppend none x = none) ∧ (∀ x, mzAppend' none x = none) ∧ mzAppend ≠ mzAppend' := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun h => ?_⟩
  have := congrFun (congrFun h (some [true])) (some [false])
  simp [mzAppend, mzAppend'] at this

/-- **How many directions move the family.** Two of the four axiom-shapes move the closeable family:
constant-constant (forcing, three up-sets) and constant-operation (absorbing, two). Operation-operation does
not (associativity holds, the family unchanged). Constant-constrains-operation is not realized here. Checked at
the small instances. -/
theorem how_many_directions :
    ((Finset.univ.filter (fun c : Bool → Bool => IsUpSet c)).card = 3)
    ∧ ((Finset.univ.filter (fun c : Bool → Bool => IsBlockable c)).card = 2)
    ∧ (∀ a b c : Option (List Bool), mzAppend (mzAppend a b) c = mzAppend a (mzAppend b c)) := by
  refine ⟨by decide, by decide, fun a b c => ?_⟩
  cases a <;> cases b <;> cases c <;> simp [mzAppend, List.append_assoc]

/-! ## The verdict

Part 1: forcing and blocking combine, and they interact. The combined family, computed from the moves, is two
sets (`combined_family`), and it is Boolean (`combination_is_boolean`): blocking the forcing's lower element
made the forcing vacuous and removed the top of its chain, collapsing the Heyting order back to Boolean. Not
the assumed up-sets-minus-blocked, and not still Heyting: the departures are not independent when they overlap.
Blocking a reason outside the forcing order would leave the Heyting order intact, so the interaction depends on
whether the blocked reason participates in the forcing.

Part 2: two of four axiom-shapes move the closeable family, and the arity split explains which. Constant to
constant (forcing) and constant to operation (absorbing) move it; operation to operation does not
(`operation_operation_axioms`), since those axioms live in the reduct the cataphatic side reads while the
reasons are the constants; and the constant-constrains-operation direction is not realized in the instances
(`operation_constant_other_direction`), it would be stipulated. So among the shapes checked, two move the
family, one leaves it fixed, one is empty (`how_many_directions`).

The verdict: the departures interact, blocking able to collapse forcing when they overlap, so non-freeness is
not a sum of independent effects but a genuine two-dimensional space, the subvariety lattice. Of the four
axiom-shapes, the two that relate a constant to something move the apophatic index, the operation-only one does
not, and the reverse constant-operation shape is empty here. The arity split predicts exactly this: axioms
touching a constant reach the reasons, axioms only among operations stay in the reduct. Nothing here is
resolved. -/

end Chiralogy.Departures
