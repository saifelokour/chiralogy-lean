import Chiralogy.Model.Stance

/-! ARCHIVED (fully graduated). The two within-application orders.

GRADUATED to `Model/Stance`, section Orders, in full: all 21 results, because every one of them is
order-NEUTRAL and none asserts a priority. Spec 4.a.21.

The question the brief posed had three readings and the math refused two of them. The orders are NOT co-equal
(they differ at every conflicted cell) and there is NO order-neutral operation subsuming both (at a conflicted
cell the two directions demand different values, so any neutral operation would need a resolution rule, and a
resolution rule is the order). What is true is narrower and is what graduated: the two agree off the released
cells, the reverse is the forward remasked and hence dominated, they agree outright exactly on the
conflict-free stances, and the framework's own three extremes together with the entire one-directional space
are conflict-free and so order-invariant.

The priority claim did NOT graduate and is not stated as a theorem anywhere. `commit_absorbs` explains why the
forward order is the one whose two directions can cooperate, and
`the_reverse_ignores_the_form_at_released_cells` makes that precise, but explaining a definitional choice is
not forcing it.

Typechecks standalone. -/

/-! # Experiment (LIVE): the two within-application orders, and whether the framework prefers one

`Model/Stance` fixes `applyStance` as release-then-form. The reverse, form-then-release, was archived rather
than graduated because canonicalizing one order would assert a priority the arc had not established. This
build derives the relation between the two orders instead of assuming one, and tests three readings: that the
kernel FORCES the forward order, that the two are CO-EQUAL, or that both are instances of ONE order-neutral
operation.

Register-neutral throughout: no statement and no proof mentions any domain, and no name carries a register
term. The names used are order, release, form, conflict, dominated and invariant. All readings are in the
report only.

Live experiment. No canonical edit until the last part, nothing graduated here. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.StanceOrder

section Orders

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- Forming first: write the instruction into whatever is open, leave what is held. -/
def formStep (T : Stance X) (c : Pt X → Pt X → Option Bool) : Pt X → Pt X → Option Bool :=
  fun x y => if c x y = none then T.form c x y else c x y

/-- The reverse application: form first, then release. -/
def applyStanceRev (T : Stance X) (c : Pt X → Pt X → Option Bool) : Pt X → Pt X → Option Bool :=
  partialization (T.drop c) (formStep T c)

theorem formStep_of_open {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : c x y = none) : formStep T c x y = T.form c x y := by simp [formStep, h]

theorem formStep_of_held {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : c x y ≠ none) : formStep T c x y = c x y := by simp [formStep, h]

theorem applyStanceRev_of_dropped {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : T.drop c x y = true) : applyStanceRev T c x y = none := by
  simp [applyStanceRev, partialization, h]

theorem applyStanceRev_of_kept {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : T.drop c x y = false) : applyStanceRev T c x y = formStep T c x y := by
  simp [applyStanceRev, partialization, h]

/-! ## Part 1: where the two orders differ, exactly -/

/-- **OFF THE RELEASED CELLS THE TWO ORDERS AGREE.** Wherever the stance keeps a cell, sequencing is
immaterial. Carrier-general. -/
theorem the_orders_agree_off_the_release {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : T.drop c x y = false) : applyStance T c x y = applyStanceRev T c x y := by
  rw [applyStanceRev_of_kept h]
  by_cases hv : c x y = none
  · rw [applyStance_of_kept_open h hv, formStep_of_open hv]
  · rcases hb : c x y with - | v
    · exact absurd hb hv
    · rw [forming_is_powerless_at_a_held_cell h hb, formStep_of_held hv, hb]

/-- **AND AT A RELEASED CELL THEY DIVERGE COMPLETELY.** One writes what the stance would form there, the other
leaves nothing. So the whole difference between the orders is confined to the cells the stance releases.
Carrier-general. -/
theorem at_a_released_cell {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : T.drop c x y = true) :
    applyStance T c x y = T.form c x y ∧ applyStanceRev T c x y = none :=
  ⟨applyStance_of_dropped h, applyStanceRev_of_dropped h⟩

/-- **THE REVERSE IS THE FORWARD WITH THE RELEASE APPLIED AGAIN.** Form-then-release is exactly
release-then-form followed by re-imposing the same mask, which is what discards the forming done at released
cells. Carrier-general. -/
theorem the_reverse_is_the_forward_remasked (T : Stance X) (c : Pt X → Pt X → Option Bool) :
    applyStanceRev T c = partialization (T.drop c) (applyStance T c) := by
  funext x y
  by_cases h : T.drop c x y = true
  · rw [applyStanceRev_of_dropped h]
    simp [partialization, h]
  · rw [Bool.not_eq_true] at h
    rw [← the_orders_agree_off_the_release h]
    simp [partialization, h]

/-- **SO THE REVERSE ALWAYS LANDS AT OR BELOW THE FORWARD.** Carrier-general, from canonical
`partialization_le_c`. -/
theorem the_reverse_is_dominated (T : Stance X) (c : Pt X → Pt X → Option Bool) :
    cLE (applyStanceRev T c) (applyStance T c) := by
  rw [the_reverse_is_the_forward_remasked]
  exact partialization_le_c _ _

/-! ## Part 2: the conflict, and whether an order-neutral operation exists -/

/-- A cell where the stance's two directions disagree: it releases there and would also form there. -/
def Conflicted (T : Stance X) (c : Pt X → Pt X → Option Bool) (x y : Pt X) : Prop :=
  T.drop c x y = true ∧ T.form c x y ≠ none

/-- A stance whose two directions never both fire at the same cell. -/
def ConflictFree (T : Stance X) : Prop :=
  ∀ c x y, T.drop c x y = true → T.form c x y = none

/-- **THE TWO ORDERS COINCIDE EXACTLY OFF THE CONFLICT.** They give the same result at a classification
precisely when the stance forms nothing at any cell it releases there. So the order is not a global choice: it
is a choice only about cells where the two directions disagree. Carrier-general. -/
theorem the_orders_agree_iff_no_conflict (T : Stance X) (c : Pt X → Pt X → Option Bool) :
    applyStance T c = applyStanceRev T c ↔ ∀ x y : Pt X, T.drop c x y = true → T.form c x y = none := by
  constructor
  · intro h x y hd
    have hc := congrFun (congrFun h x) y
    rw [(at_a_released_cell hd).1, (at_a_released_cell hd).2] at hc
    exact hc
  · intro h
    funext x y
    by_cases hd : T.drop c x y = true
    · rw [(at_a_released_cell hd).1, (at_a_released_cell hd).2, h x y hd]
    · rw [Bool.not_eq_true] at hd
      exact the_orders_agree_off_the_release hd

/-- **A CONFLICT-FREE STANCE IS ORDER-INVARIANT.** Carrier-general. -/
theorem conflictFree_is_order_invariant {T : Stance X} (h : ConflictFree T)
    (c : Pt X → Pt X → Option Bool) : applyStance T c = applyStanceRev T c :=
  (the_orders_agree_iff_no_conflict T c).mpr (fun x y hd => h c x y hd)

/-- Release a named cell and form there, whatever the classification: the two directions collide. -/
def coincident (a b : Pt X) : Stance X :=
  ⟨fun _ x y => decide (x = a ∧ y = b), fun _ x y => if x = a ∧ y = b then some true else none⟩

theorem coincident_conflicts (a b : Pt X) (c : Pt X → Pt X → Option Bool) :
    Conflicted (coincident a b) c a b := by
  refine ⟨by simp [coincident], ?_⟩
  simp only [coincident]
  exact Option.some_ne_none _

/-- **AT A CONFLICTED CELL NO SINGLE VALUE SATISFIES BOTH DIRECTIONS.** The forward order writes what the
stance forms, the reverse leaves nothing, and those differ. So sequencing is not an artefact to be removed by a
cleverer definition: it is the RESOLUTION of a genuine disagreement, and an order-neutral operation would have
to decide the same question by another name. Carrier-general. -/
theorem the_conflict_admits_no_neutral_value {T : Stance X} {c : Pt X → Pt X → Option Bool}
    {x y : Pt X} (h : Conflicted T c x y) :
    applyStance T c x y ≠ applyStanceRev T c x y := by
  rw [(at_a_released_cell h.1).1, (at_a_released_cell h.1).2]
  exact h.2

/-- **AND THE CONFLICT IS NOT VACUOUS.** A stance releasing and forming the same named cell conflicts there at
every classification. Carrier-general, given a cell. -/
theorem the_conflict_is_real (a b : Pt X) (c : Pt X → Pt X → Option Bool) :
    applyStance (coincident a b) c a b ≠ applyStanceRev (coincident a b) c a b :=
  the_conflict_admits_no_neutral_value (coincident_conflicts a b c)

/-! ## Part 3: what the reverse order does with its own forming -/

/-- **THE REVERSE ORDER IGNORES WHAT THE STANCE WOULD FORM AT THE CELLS IT RELEASES.** Two stances with the
same release, whose forming agrees only off the released cells, act identically under the reverse order. So
under form-then-release the forming at a released cell is not merely discarded, it is invisible: the two
directions never interact. Carrier-general. -/
theorem the_reverse_ignores_the_form_at_released_cells (T : Stance X)
    (g : (Pt X → Pt X → Option Bool) → Pt X → Pt X → Option Bool)
    (c : Pt X → Pt X → Option Bool)
    (h : ∀ x y : Pt X, T.drop c x y = false → g c x y = T.form c x y) :
    applyStanceRev ⟨T.drop, g⟩ c = applyStanceRev T c := by
  funext x y
  by_cases hd : T.drop c x y = true
  · rw [applyStanceRev_of_dropped (T := ⟨T.drop, g⟩) hd, applyStanceRev_of_dropped hd]
  · rw [Bool.not_eq_true] at hd
    rw [applyStanceRev_of_kept (T := ⟨T.drop, g⟩) hd, applyStanceRev_of_kept hd]
    by_cases hv : c x y = none
    · rw [formStep_of_open (T := ⟨T.drop, g⟩) hv, formStep_of_open hv]
      exact h x y hd
    · rw [formStep_of_held (T := ⟨T.drop, g⟩) hv, formStep_of_held hv]

/-- **THE FORWARD ORDER DOES NOT IGNORE IT.** The same two stances differ under release-then-form, so the
interaction the reverse order lacks is real and is the forward order's. Carrier-general, given a cell. -/
theorem the_forward_order_uses_it (a b : Pt X) (c : Pt X → Pt X → Option Bool) :
    applyStance (coincident a b) c a b
      ≠ applyStance (⟨(coincident a b).drop, fun _ _ _ => none⟩ : Stance X) c a b := by
  rw [applyStance_of_dropped (T := coincident a b) (by simp [coincident]),
    applyStance_of_dropped (T := (⟨(coincident a b).drop, fun _ _ _ => none⟩ : Stance X))
      (by simp [coincident])]
  simp only [coincident]
  exact Option.some_ne_none _

/-- **A HELD CELL CANNOT BE CARRIED TO A NEW VALUE BY THE REVERSE ORDER.** In one application it can only be
kept or emptied. This is the capability the release-first order has and the form-first order does not, and it
follows from the same fact: the reverse order's forming runs before the release, so it never sees the opening
the release makes. Carrier-general. -/
theorem the_reverse_cannot_reassign {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (hv : c x y ≠ none) : applyStanceRev T c x y = c x y ∨ applyStanceRev T c x y = none := by
  by_cases hd : T.drop c x y = true
  · exact Or.inr (applyStanceRev_of_dropped hd)
  · rw [Bool.not_eq_true] at hd
    rw [applyStanceRev_of_kept hd, formStep_of_held hv]
    exact Or.inl rfl

/-! ### The framework's own three extremes are conflict-free -/

theorem dropAll_conflictFree : ConflictFree (dropAll : Stance X) := fun _ _ _ _ => rfl

theorem holdAll_conflictFree : ConflictFree (holdAll : Stance X) := fun _ _ _ _ => rfl

theorem formAll_conflictFree : ConflictFree (formAll : Stance X) := by
  intro c x y h
  exact absurd h (by simp [formAll])

/-- **SO THE THREE EXTREMES ARE ORDER-INVARIANT.** Releasing everything, keeping everything and forming
everywhere give the same result under either order, because none of them ever releases and forms the same cell.
The two failure modes the arc identified are therefore properties of the stance, not of the sequencing.
Carrier-general. -/
theorem the_extremes_are_order_invariant (c : Pt X → Pt X → Option Bool) :
    applyStance (dropAll : Stance X) c = applyStanceRev (dropAll : Stance X) c
      ∧ applyStance (holdAll : Stance X) c = applyStanceRev (holdAll : Stance X) c
      ∧ applyStance (formAll : Stance X) c = applyStanceRev (formAll : Stance X) c :=
  ⟨conflictFree_is_order_invariant dropAll_conflictFree c,
   conflictFree_is_order_invariant holdAll_conflictFree c,
   conflictFree_is_order_invariant formAll_conflictFree c⟩

/-- **AND SO IS EVERY ONE-DIRECTIONAL RULE.** A policy read as a stance forms nothing, so it never conflicts:
the whole earlier one-directional space is order-invariant, and the question of sequencing arises only once
both directions are present. Carrier-general. -/
theorem the_one_directional_space_is_order_invariant (S : Policy X)
    (c : Pt X → Pt X → Option Bool) :
    applyStance (ofMask S) c = applyStanceRev (ofMask S) c :=
  conflictFree_is_order_invariant (fun _ _ _ _ => rfl) c

end Orders

/-! ## THE VERDICTS

PART 1: THE TWO ORDERS DIFFER EXACTLY AT THE CELLS THE STANCE RELEASES, AND NOWHERE ELSE.

`the_orders_agree_off_the_release` and `at_a_released_cell` locate the difference completely. Wherever the
stance keeps a cell, the two orders give the same answer. At a cell it releases, release-then-form writes what
the stance would form there and form-then-release leaves nothing. That is the whole of the difference.

`the_reverse_is_the_forward_remasked` states it as an identity: FORM-THEN-RELEASE IS RELEASE-THEN-FORM WITH THE
SAME MASK APPLIED AGAIN. The reverse order is not a different construction, it is the forward one with a second
imposition of the release, and that second imposition is exactly what discards the forming at released cells.

`the_reverse_is_dominated` follows at once from canonical `partialization_le_c`: the reverse always lands at or
below the forward in the information order.

PART 2: THE ORDER IS THE RESOLUTION OF A GENUINE CONFLICT, AND IT IS NOT ELIMINABLE.

This is the finding, and it settles the three readings the brief posed by refusing the first two.

`the_orders_agree_iff_no_conflict` is exact: the two orders give the same result at a classification PRECISELY
WHEN the stance forms nothing at any cell it releases there. So sequencing is not a global commitment. It is a
choice about one set of cells: the CONFLICTED ones, where the stance's two directions disagree, one wanting the
cell open and the other wanting it filled.

`the_conflict_admits_no_neutral_value` shows the choice cannot be dissolved. At a conflicted cell the forward
order gives what the stance forms and the reverse gives nothing, and those are different values. NO SINGLE
VALUE SATISFIES BOTH DIRECTIONS. An order-neutral operation would therefore have to decide the same question
under another name: it would need a resolution rule, and a resolution rule IS the order. `the_conflict_is_real`
confirms the conflicted cells are not vacuous.

SO READING (iii) IS REFUTED: there is no order-neutral two-directional operation that subsumes both, because
the two directions genuinely disagree at a nonempty set of cells. And reading (ii), that the orders are
co-equal, is refuted in the strong form: they are not interchangeable, since they differ at every conflicted
cell.

PART 3: WHAT THE REVERSE ORDER'S OWN STRUCTURE IS, AND IT IS A NON-INTERACTION.

`the_reverse_ignores_the_form_at_released_cells` is the sharp statement of what the archived build called
waste, and it is stronger than waste. Two stances with the same release, whose forming agrees only OFF the
released cells, act IDENTICALLY under the reverse order. So under form-then-release, what the stance would form
at a cell it releases is not merely discarded, it is INVISIBLE. The two directions never interact.
`the_forward_order_uses_it` confirms the interaction is real and belongs to the forward order.

`the_reverse_cannot_reassign` is the same fact seen from the cell: under the reverse order a held cell can only
be kept or emptied in one application, never carried to a new value, because the forming runs before the
release and so never sees the opening the release makes.

BUT THE REVERSE ORDER IS NOT DEGENERATE, AND READING (i) IS NOT ESTABLISHED EITHER. The archived build proved
that a retuned rule reproduces the period-two cycle under the reverse order, and that restoration to an
arbitrary target still reaches it, in two applications rather than one. So the reverse order supports orbits
and repair. What it lacks is one-step reassignment and the cooperation of its two directions. That is a
capability gap, not a collapse, and a capability gap does not by itself make the other order canonical.

`the_extremes_are_order_invariant` and `the_one_directional_space_is_order_invariant` place the whole question.
The three extremes never release and form the same cell, so they are conflict-free and give the same result
under either order. So does every one-directional rule, since a policy forms nothing. THE TWO PATHOLOGIES THE
ARC IDENTIFIED ARE PROPERTIES OF THE STANCE AND NOT OF THE SEQUENCING, and the sequencing question arises only
once both directions are genuinely present and pointed at the same cell.

PART 4: WHAT THE FRAMEWORK ESTABLISHES, AND WHAT IT DOES NOT.

ESTABLISHED, and order-neutral to state: the two orders differ exactly on the conflicted cells; they coincide
off them; the reverse is the forward remasked and is therefore dominated; the conflict admits no neutral value,
so an order must be chosen wherever both directions point at one cell; the reverse order's two directions never
interact; and the framework's own three extremes, together with the entire one-directional space, are
conflict-free and so order-invariant.

NOT ESTABLISHED: that the kernel FORCES release-then-form. `commit_absorbs` explains why the forward order is
the one in which the release can make room for the form, and `the_reverse_ignores_the_form_at_released_cells`
makes that precise. But explaining a choice is not forcing it. The reverse order is a coherent composite that
supports orbits and repair, and nothing here shows it inconsistent or useless. What is shown is narrower and
should be stated as what it is: THE FORWARD ORDER IS THE ONLY ONE OF THE TWO IN WHICH THE STANCE'S TWO
DIRECTIONS COOPERATE.

REGISTER READINGS. Report only, defeasible, supplied by the register rather than derived.

  ON THE CONFLICT. The order matters only where clearing and building are aimed at the same site. Everywhere
  else the sequence is immaterial, which is most of what any rule does. Where they do collide, something has to
  decide, and no amount of care in stating the rule removes the decision: the site cannot be both left open and
  filled.

  ON WHAT THE CHOICE BUYS. Clearing first is what lets the clearing make room for the building. Building first
  means the building can only go where there was already room, and whatever it would have put on the cleared
  site is not merely lost but never consulted. That is why replacing something standing takes one act under one
  order and two under the other.

  ON WHAT DOES NOT DEPEND ON IT. Neither failure mode is a matter of sequencing. Giving everything up, keeping
  everything and settling everything come out the same under either order, because none of them tries to clear
  and build the same thing at once.

AXIOM PROFILE AND GRADUATION. Every result is at baseline or below. Graduation IS proposed for the
order-neutral content of Parts 1 to 3, which asserts no priority: the conflict characterization, the remasking
identity, the domination, the non-interaction, and the order-invariance of the extremes and of the
one-directional space. Graduation is NOT proposed for any claim that one order is canonical.

WHAT REMAINS OPEN

1. The reverse order's orbits and its two-application repair are proved in the archived build and are not
   re-derived here. Whether every forward-order orbit has a reverse-order analogue is not settled.
2. A resolution-parameterized operation, taking the choice at conflicted cells as an argument, is definable and
   is not built: it would make the choice explicit rather than remove it.
3. Nothing here compares runs. The orders are compared one application at a time. -/

#print axioms formStep_of_open
#print axioms formStep_of_held
#print axioms applyStanceRev_of_dropped
#print axioms applyStanceRev_of_kept
#print axioms the_orders_agree_off_the_release
#print axioms at_a_released_cell
#print axioms the_reverse_is_the_forward_remasked
#print axioms the_reverse_is_dominated
#print axioms the_orders_agree_iff_no_conflict
#print axioms conflictFree_is_order_invariant
#print axioms coincident_conflicts
#print axioms the_conflict_admits_no_neutral_value
#print axioms the_conflict_is_real
#print axioms the_reverse_ignores_the_form_at_released_cells
#print axioms the_forward_order_uses_it
#print axioms the_reverse_cannot_reassign
#print axioms dropAll_conflictFree
#print axioms holdAll_conflictFree
#print axioms formAll_conflictFree
#print axioms the_extremes_are_order_invariant
#print axioms the_one_directional_space_is_order_invariant

end Chiralogy.StanceOrder
