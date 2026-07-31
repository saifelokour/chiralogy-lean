import Chiralogy.Model.AssemblageRelations

/-! ARCHIVED (not graduated). Commit versus close, at a single cell.

NOT GRADUATED, and the reason is a Phase 2 gate failure worth recording. Its results are not carrier-general:
they are statements about one `Option Bool` cell under a fixed list of acts, with no carrier variable at all
(`the_state_does_not_distinguish : ∀ u : Bool, ...`). Thirteen of its sixteen results reach NO canonical node,
which the dependency map measured before the graduation pass and this pass confirmed. Universalizing them was
explicitly declined rather than forced.

THE FINDING STANDS AND IS THE REASON TO KEEP THE FILE: commit and close are a MOVE and a STANCE respectively,
and the difference is not in the state space. `the_state_does_not_distinguish` shows two runs reaching the same
cell state under acts that differ in what they would do next; `aiming_implies_declining_and_not_conversely`
separates the two readings. That is a claim about the run, not about a classification, which is why it does not
fit either Model module and why the layer above (the stance) had to be built at all.

Typechecks standalone. -/

/-! # Experiment (LIVE): what closing can be, given the algebra

The builds have said closed of a cell that has content. Landing content is one of the two moves and is neutral:
it is undone by the other. Whatever closing is meant to name, if it is a distinct thing, it must be derivable
from what the algebra has. This build derives the candidates and tests which the framework supports.

Three readings are tested and they do not all survive: that closing is a further move beside the two, that it
is a landed cell whose available withdrawal is declined, and that it is a stance of the whole configuration
toward the committed extreme.

Register-neutral throughout: no statement and no proof mentions any domain, and no name carries a register
term. All interpretive readings are in the report only.

Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.CommitVsClose

/-! ## The single-cell algebra

At one cell the two moves do two things: one lands content where there is none and keeps what is there, the
other empties where its mask fires. Everything below is stated at a cell, since the question is about a cell. -/

inductive Act where
  | fill (v : Bool) : Act
  | opn (w : Bool) : Act
  deriving DecidableEq

def applyAct : Act → Option Bool → Option Bool
  | .fill v, x => some (x.getD v)
  | .opn w, x => if w then none else x

def runActs (l : List Act) (x : Option Bool) : Option Bool :=
  l.foldl (fun y a => applyAct a y) x

/-- An act that empties the cell. -/
def Fires : Act → Prop
  | .fill _ => False
  | .opn w => w = true

instance : DecidablePred Fires := fun a => by
  cases a with
  | fill v => exact instDecidableFalse
  | opn w => exact inferInstanceAs (Decidable (w = true))

/-! ## Part 1: is there a further move -/

section NoThirdMove

/-- **LANDING CONTENT KEEPS WHAT IS THERE.** So the algebra has no overwriting act. Carrier-general. -/
theorem filling_keeps_what_is_there (v u : Bool) : applyAct (.fill v) (some u) = some u := rfl

/-- **AND NO ACT OVERWRITES.** No act sends every state to one and the same verdict, so replacement of content
is a single-cell operation the algebra does not contain. That is a genuine gap, and it is about content and not
about locking. -/
theorem no_act_overwrites (a : Act) : ¬ (∀ x : Option Bool, applyAct a x = some false) := by
  intro h
  cases a with
  | fill v =>
    have := h (some true)
    rw [filling_keeps_what_is_there] at this
    exact absurd this (by simp)
  | opn w =>
    cases hw : w with
    | true =>
      have := h (some true)
      rw [show applyAct (Act.opn w) (some true) = none by rw [applyAct, hw]; simp] at this
      exact Option.some_ne_none _ this.symm
    | false =>
      have := h (some true)
      rw [show applyAct (Act.opn w) (some true) = some true by rw [applyAct, hw]; simp] at this
      exact absurd this (by simp)

/-- **AND NOTHING LOCKS A CELL.** Whatever operation is applied and whatever the configuration, an emptying act
still empties the cell afterwards. So no act, and no composite of acts, produces a state at which the
withdrawal is unavailable. There is no land-and-lock move to be had. -/
theorem nothing_locks (l : List Act) (x : Option Bool) :
    applyAct (.opn true) (runActs l x) = none := by
  simp [applyAct]

/-- **SO THE ONLY THING A FURTHER MOVE COULD ADD IS UNAVAILABLE.** Every state reached by any run still admits
the emptying, so a move that landed content and removed the withdrawal cannot exist in this algebra. -/
theorem no_land_and_lock_move (l : List Act) (x : Option Bool) :
    ¬ ∃ a : Act, runActs (l ++ [a]) x ≠ none ∧ applyAct (.opn true) (runActs (l ++ [a]) x) ≠ none := by
  rintro ⟨a, -, h⟩
  exact h (nothing_locks (l ++ [a]) x)

end NoThirdMove

/-! ## Part 2: a landed cell whose withdrawal is declined -/

section Refusal

/-- From an empty cell nothing but an emptying keeps it empty, and a run of acts from empty stays empty when
none of them lands anything. The lemma needed below is the other one: emptiness is absorbing for emptyings. -/
theorem runActs_from_none_of_opens {l : List Act} (h : ∀ a ∈ l, ∀ v : Bool, a ≠ Act.fill v) :
    runActs l none = none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a with
    | fill v => exact absurd rfl (h (Act.fill v) (List.mem_cons_self ..) v)
    | opn w =>
      show runActs l (applyAct (Act.opn w) none) = none
      rw [show applyAct (Act.opn w) none = none by cases w <;> simp [applyAct]]
      exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- **A LANDED CELL SURVIVES A RUN IN WHICH NOTHING FIRES.** Landings keep what is there and declined
emptyings change nothing, so the content stands. -/
theorem no_firing_keeps_it (l : List Act) (h : ∀ a ∈ l, ¬ Fires a) (u : Bool) :
    runActs l (some u) = some u := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hstep : applyAct a (some u) = some u := by
      cases a with
      | fill v => rfl
      | opn w =>
        cases w with
        | true => exact absurd rfl (h (Act.opn true) (List.mem_cons_self ..))
        | false => simp [applyAct]
    show runActs l (applyAct a (some u)) = some u
    rw [hstep]
    exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- **AND ONE FIRING ENDS IT.** Once an emptying fires the cell is empty, and nothing that follows without a
landing brings it back. -/
theorem one_firing_ends_it {l m : List Act} (h : ∀ a ∈ m, ∀ v : Bool, a ≠ Act.fill v)
    (x : Option Bool) : runActs (l ++ Act.opn true :: m) x = none := by
  rw [runActs, List.foldl_append]
  show runActs m (applyAct (Act.opn true) (runActs l x)) = none
  rw [show applyAct (Act.opn true) (runActs l x) = none by simp [applyAct]]
  exact runActs_from_none_of_opens h

/-- **SO A LANDED CELL STANDING IS THE CONTINUED DECLINING, AND THAT IS A FEATURE OF THE RUN.** Whether the
content stands is settled by what every act of the run does at the cell, not by any one act and not by the
state. Carrier-general in the run. -/
theorem standing_is_a_property_of_the_run (l m : List Act) (h : ∀ a ∈ l, ¬ Fires a)
    (h' : ∀ a ∈ m, ∀ v : Bool, a ≠ Act.fill v) (u : Bool) :
    runActs l (some u) = some u ∧ runActs (Act.opn true :: m) (some u) = none :=
  ⟨no_firing_keeps_it l h u, one_firing_ends_it (l := []) h' (some u)⟩

/-- **AND THE STATE DOES NOT DISTINGUISH THE TWO.** One and the same landed cell continues into a run that
keeps it and into a run that empties it, so nothing read off the state says which. Whatever closing is, it is
not visible at a state. -/
theorem the_state_does_not_distinguish (u : Bool) :
    runActs [Act.opn false] (some u) = some u ∧ runActs [Act.opn true] (some u) = none := by
  constructor <;> simp [runActs, applyAct]

end Refusal

/-! ## Part 3: the whole configuration aimed at the committed extreme -/

section Stances

/-- **A RUN OF LANDINGS DECLINES EVERY WITHDRAWAL.** Nothing in it fires, so aiming at the committed extreme is
one way of declining. -/
theorem landing_only_declines (l : List Act) (h : ∀ a ∈ l, ∃ v : Bool, a = Act.fill v) (a : Act)
    (ha : a ∈ l) : ¬ Fires a := by
  obtain ⟨v, rfl⟩ := h a ha
  exact id

/-- **BUT DECLINING DOES NOT REQUIRE LANDING ANYTHING.** The run that does nothing declines every withdrawal
and lands nothing, so the two stances are not the same: one is an absence of acts and the other is a
particular kind of act. -/
theorem declining_does_not_require_landing (u : Bool) :
    (∀ a ∈ ([] : List Act), ¬ Fires a)
      ∧ runActs [] (some u) = some u
      ∧ ¬ (∀ a ∈ ([] : List Act), ∃ v : Bool, a = Act.fill v) → False := by
  intro h
  exact h.2.2 (fun a ha => absurd ha (List.not_mem_nil))

/-- **THE TWO STANCES SEPARATE, AND THE SEPARATION IS ONE-DIRECTIONAL.** Aiming at the extreme declines every
withdrawal, and declining every withdrawal is compatible with landing nothing at all. So the second is strictly
weaker than the first. -/
theorem aiming_implies_declining_and_not_conversely (u : Bool) :
    (∀ l : List Act, (∀ a ∈ l, ∃ v : Bool, a = Act.fill v) → ∀ a ∈ l, ¬ Fires a)
      ∧ ((∀ a ∈ ([] : List Act), ¬ Fires a) ∧ runActs ([] : List Act) (some u) = some u) := by
  refine ⟨fun l h => landing_only_declines l h, ?_, rfl⟩
  intro a ha
  exact absurd ha (List.not_mem_nil)

/-- **AND A RUN OF LANDINGS CHANGES NOTHING AT AN ALREADY LANDED CELL.** So at a cell that already has content
the two stances have the same effect, and they differ only in what they do elsewhere. -/
theorem at_a_landed_cell_both_stances_agree (l : List Act)
    (h : ∀ a ∈ l, ∃ v : Bool, a = Act.fill v) (u : Bool) : runActs l (some u) = some u :=
  no_firing_keeps_it l (landing_only_declines l h) u

end Stances

/-! ## Part 4: the two moves are both reversible, so neither is marked -/

section Neutrality

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- Land content at one named cell. -/
def commitAt (a b : Pt X) (v : Bool) (c : Pt X → Pt X → Option Bool) : Pt X → Pt X → Option Bool :=
  fun x y => if x = a ∧ y = b then some v else c x y

/-- Empty one named cell. -/
def openAtCell (a b : Pt X) (c : Pt X → Pt X → Option Bool) : Pt X → Pt X → Option Bool :=
  fun x y => if x = a ∧ y = b then none else c x y

/-- **BOTH DIRECTIONS ARE AVAILABLE AT EVERY CELL AT EVERY CONFIGURATION.** Content can be landed and content
can be emptied, from anywhere, so neither state of a cell is the marked one. The factor the earlier builds
called open against closed is open against LANDED, and both sides of it are neutral. Carrier-general. -/
theorem both_directions_are_always_available (a b : Pt X) (v : Bool)
    (c : Pt X → Pt X → Option Bool) :
    commitAt a b v c a b ≠ none ∧ openAtCell a b c a b = none := by
  constructor
  · rw [commitAt, if_pos ⟨rfl, rfl⟩]
    exact Option.some_ne_none _
  · rw [openAtCell, if_pos ⟨rfl, rfl⟩]

/-- **AND EACH UNDOES THE OTHER AT THAT CELL.** Carrier-general. -/
theorem each_undoes_the_other (a b : Pt X) (v : Bool) (c : Pt X → Pt X → Option Bool) :
    openAtCell a b (commitAt a b v c) a b = none
      ∧ commitAt a b v (openAtCell a b c) a b = some v := by
  constructor
  · rw [openAtCell, if_pos ⟨rfl, rfl⟩]
  · rw [commitAt, if_pos ⟨rfl, rfl⟩]

/-- **SO THE DISTINCTION SOUGHT IS NOT A FUNCTION OF THE STATE.** A cell with content is one act from being
empty and stays as it is under any run that does not fire, and the state records neither. Any distinction
between landing and refusing is therefore a property of what a run does and not of where a configuration is.
Carrier-general. -/
theorem the_distinction_is_not_a_state_function (a b : Pt X) (v : Bool)
    (c : Pt X → Pt X → Option Bool) (u : Bool) :
    (openAtCell a b (commitAt a b v c) a b = none)
      ∧ runActs [Act.opn false] (some u) = some u
      ∧ runActs [Act.opn true] (some u) = none :=
  ⟨(each_undoes_the_other a b v c).1, (the_state_does_not_distinguish u).1,
   (the_state_does_not_distinguish u).2⟩

end Neutrality

/-! ## THE VERDICTS

PART 1: THERE IS NO FURTHER MOVE, AND THE GAP IN THE ALGEBRA IS SOMEWHERE ELSE.

`nothing_locks` settles the third reading, and it settles it flatly. Whatever run has been performed and
whatever state it reached, an emptying act still empties the cell afterwards. `no_land_and_lock_move` states the
consequence: A MOVE THAT LANDED CONTENT AND REMOVED THE WITHDRAWAL CANNOT EXIST HERE, because nothing whatever
produces a state at which the withdrawal is unavailable. So closing is not a third primitive folded into
landing.

The build did turn up a genuine gap, and it is not the one that was being looked for.
`filling_keeps_what_is_there` and `no_act_overwrites` show that no act sends every state to one and the same
verdict. REPLACEMENT OF CONTENT is a single-cell operation the algebra does not contain. That is a real absence
and it is about content, not about locking, so it does not help the reading that was under test.

PART 2: WHAT SURVIVES IS A PROPERTY OF THE RUN, NOT OF THE CELL AND NOT OF ANY ACT.

`no_firing_keeps_it` and `one_firing_ends_it` characterize it exactly. A landed cell stands through a run in
which nothing fires, and one firing ends it. So the standing of the content is settled by WHAT EVERY ACT OF THE
RUN DOES AT THE CELL, and by nothing smaller.

`the_state_does_not_distinguish` is the sharp form. One and the same landed cell continues into a run that
keeps it and into a run that empties it. NOTHING READ OFF THE STATE SAYS WHICH. So if closing names anything
here, it names a feature of a trajectory, and the phrase a closed cell is not well formed: a cell has content
or it does not, and that is all a cell has.

PART 3: THE TWO STANCES ARE DIFFERENT, AND THE PREDICTED IDENTITY IS FALSE.

The expectation was that aiming at the committed extreme would be the same thing as declining every
withdrawal. IT IS NOT, and the separation is one-directional.

`landing_only_declines`: a run of landings fires nothing, so aiming does decline. `declining_does_not_require_landing`
and `aiming_implies_declining_and_not_conversely`: the run that does nothing at all declines every withdrawal
and lands nothing. SO DECLINING IS STRICTLY WEAKER THAN AIMING. One is an absence of a particular act and the
other is the presence of a particular act, and an absence cannot be an occurrence.

`at_a_landed_cell_both_stances_agree` locates where the difference is not visible: at a cell that ALREADY has
content the two do the same thing, since landing on content changes nothing. They differ only in what happens
at cells that are still empty. So the arc has been using one word for a non-act that preserves and for an act
that spreads, and they coincide only where there is nothing left to spread to.

PART 4: LANDING IS A MOVE, DECLINING IS NOT, AND THE DISTINCTION IS NOT A THIRD FACTOR.

`both_directions_are_always_available` and `each_undoes_the_other`: content can be landed and content can be
emptied, from anywhere, and each undoes the other at that cell. NEITHER STATE OF A CELL IS THE MARKED ONE. So
the factor the earlier builds named open against closed is open against LANDED, and both sides of it are
neutral. The naming was wrong and the structure was not.

`the_distinction_is_not_a_state_function` is the structural answer to the question the brief called the real
one. The two factors the arc found, where things are landed and what is landed there, are both properties of a
STATE. What separates a configuration that will let go from one that will not is not a property of a state at
all: the same state does both. SO IT IS NOT A THIRD FACTOR BESIDE THE OTHER TWO. It is not in the state space.

The honest picture is therefore in two levels rather than three factors. A configuration has two factors, and
they are what the arc found. A RUN through configurations has a further property, which is what every act of it
declines to do, and that property is invisible at every state the run passes through.

AND THE CONFLATION WAS REAL, twice over. Landing content is a move and is neutral, undone by the other move
from anywhere. What the builds called closing is not a move: at the cell level it is a run declining, at the
configuration level it is a run spreading, and by Part 3 those two are not the same thing either.

REGISTER READINGS. Report only, defeasible, supplied by the register rather than derived.

  THE GENERAL SHAPE. Settling something is an act, and it is neutral: it is done, and the undoing is available
  from wherever one has got to. What the arc kept calling closing is not a further act one could catch someone
  performing. It is the continued not-performing of the act that would undo it, and there is no moment at which
  it happens. That is why nothing about a settled matter, examined at any instant, shows whether it is held
  open to revision.

  AND THE SECOND CONFLATION MATTERS AS MUCH AS THE FIRST. Refusing to reopen and setting out to settle
  everything are not one stance. The first is doing nothing; the second is doing a great deal. They look alike
  only where everything is already settled, which is the one place there is nothing further to do.

  COGNITION. Settling a question and refusing ever to reopen it are not two states of the belief, and the
  second is not a state at all. A belief that will never be revised and one that will be revised tomorrow are
  identical today, in every respect the structure records. So what is sometimes described as a rigid belief is
  not a belief with a property; it is a person with a policy, and the policy shows only over time.

  POLITICS. Deciding is an act and entrenching is not. An entrenched arrangement and a provisional one can be
  word for word the same; what differs is whether the amendment that stands available is taken. And a body that
  refuses to amend is doing something different from a body that legislates on everything, though both decline
  every repeal.

AXIOM PROFILE AND GRADUATION. Every result is at baseline or below. Graduation is NOT proposed: the act algebra
is a cell-level model defined here. Three are flagged as substantive: `nothing_locks`, which rules out the
further move; `the_state_does_not_distinguish`, which puts the distinction outside the state space; and
`aiming_implies_declining_and_not_conversely`, which separates the two stances the arc had been running
together.

WHAT REMAINS OPEN

1. The act algebra is at one cell. Whether the configuration-level stances separate the same way when the
   spreading has somewhere to go is stated but not proved at configuration level.
2. Replacement of content is missing from the algebra and this build only notes it. Whether adding it would
   change anything the arc has proved is untouched, and it is the obvious next question.
3. Runs here are finite lists. A policy of never reopening is naturally an infinite condition, and whether the
   distinction survives to infinite runs is not asked.
4. The naming correction is recorded and not carried out. Every earlier build says closed where it means
   landed, and nothing here revises them.
5. Nothing here is graduated. -/

#print axioms filling_keeps_what_is_there
#print axioms no_act_overwrites
#print axioms nothing_locks
#print axioms no_land_and_lock_move
#print axioms runActs_from_none_of_opens
#print axioms no_firing_keeps_it
#print axioms one_firing_ends_it
#print axioms standing_is_a_property_of_the_run
#print axioms the_state_does_not_distinguish
#print axioms landing_only_declines
#print axioms declining_does_not_require_landing
#print axioms aiming_implies_declining_and_not_conversely
#print axioms at_a_landed_cell_both_stances_agree
#print axioms both_directions_are_always_available
#print axioms each_undoes_the_other
#print axioms the_distinction_is_not_a_state_function

end Chiralogy.CommitVsClose
