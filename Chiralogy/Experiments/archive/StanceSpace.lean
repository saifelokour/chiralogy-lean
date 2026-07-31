import Chiralogy.Experiments.archive.StanceCore

/-! ARCHIVED (fully graduated). The policy over withdrawals, as an object.

GRADUATED to `Model/Stance`: `step_takeAll`, `step_takeNone`, `the_run_carries_one_policy`,
`the_bottom_pole_fixes_everything`, `the_bottom_pole_never_restores`, `the_stability_asymmetry`. Spec 4.a.19.

The asymmetry graduated under standard names: the taking pole is a CONSTANT map and the declining pole is the
IDENTITY map, which is the honest statement of what the file called the two poles. No attractor is claimed.

Typechecks standalone. -/

/-! # Experiment (LIVE): the policy over withdrawals, as an object

What separates a configuration that will let go from one that will not is not a property of a configuration.
This build makes it an object: a policy saying, at every configuration and every cell, whether the available
withdrawal is taken. The object is new to the arc, so the build defines it, derives its structure, and asks
whether it has laws of its own.

Register-neutral throughout: no statement and no proof mentions any domain, and no name carries a register
term. The names used are policy, take, decline, step and fixed. All interpretive readings are in the report
only.

Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy
open Chiralogy.StanceCore

set_option linter.unusedSectionVars false

namespace Chiralogy.StanceSpace

/-! ## Part 1: the object

A policy is a rule assigning, to each configuration, the mask of cells at which it takes the withdrawal. So a
policy is a function from configurations to masks, and applying it once is the opening its mask names. -/

section Object

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-! The object, the operator, the iterator and the three named policies are `StanceCore`'s: this file adds no
copy of them. -/

/-- **TAKING EVERYTHING EMPTIES EVERYTHING, IN ONE STEP, FROM ANYWHERE.** Carrier-general, from canonical
`full_partialization_is_bot`. -/
theorem step_takeAll (c : Pt X → Pt X → Option Bool) :
    step (takeAll : Policy X) c = botC (Pt X) := full_partialization_is_bot c

/-- **AND TAKING NOTHING CHANGES NOTHING, AT EVERY CONFIGURATION.** Carrier-general. -/
theorem step_takeNone (c : Pt X → Pt X → Option Bool) : step (takeNone : Policy X) c = c := by
  funext x y
  simp [step, takeNone, partialization]

theorem step_takeAt_at (a b : Pt X) (c : Pt X → Pt X → Option Bool) :
    step (takeAt a b) c a b = none := by simp [step, takeAt, partialization]

theorem step_takeAt_elsewhere (a b : Pt X) (c : Pt X → Pt X → Option Bool) {x y : Pt X}
    (h : ¬ (x = a ∧ y = b)) : step (takeAt a b) c x y = c x y := by
  simp [step, takeAt, partialization, h]

/-- **THE TWO POLES DIFFER WHEREVER ANYTHING IS HELD.** Carrier-general. -/
theorem the_poles_differ {c : Pt X → Pt X → Option Bool} {a b : Pt X} (h : c a b ≠ none) :
    step (takeAll : Policy X) c ≠ step (takeNone : Policy X) c := by
  rw [step_takeAll, step_takeNone]
  intro he
  exact h (congrFun (congrFun he a) b).symm

/-- **AND THE SELECTIVE POLICIES ARE BETWEEN THEM.** Taking at one cell only leaves every other cell as it was
and empties that one, so it agrees with neither pole wherever two cells are held. Carrier-general. -/
theorem the_policies_form_a_spectrum {c : Pt X → Pt X → Option Bool} {a b a' b' : Pt X}
    (h : c a b ≠ none) (h' : c a' b' ≠ none) (hne : ¬ (a' = a ∧ b' = b)) :
    step (takeAt a b) c ≠ step (takeAll : Policy X) c
      ∧ step (takeAt a b) c ≠ step (takeNone : Policy X) c := by
  constructor
  · rw [step_takeAll]
    intro he
    exact h' (by rw [← step_takeAt_elsewhere a b c hne, he]; rfl)
  · rw [step_takeNone]
    intro he
    exact h (by rw [← step_takeAt_at a b c, he])

/-- **A POLICY IS NOT A FEATURE OF A CONFIGURATION.** Two policies can agree at one configuration and differ at
another, so no configuration determines a policy. Carrier-general, given a cell. -/
theorem a_configuration_does_not_determine_a_policy {c : Pt X → Pt X → Option Bool} {a b : Pt X}
    (h : c a b ≠ none) :
    (takeNone : Policy X) c = (fun d _ _ => decide (d a b = none) : Policy X) c
      ∧ (takeNone : Policy X) (botC (Pt X)) ≠ (fun d _ _ => decide (d a b = none) : Policy X)
          (botC (Pt X)) := by
  constructor
  · funext x y
    simp [takeNone, h]
  · intro he
    have := congrFun (congrFun he a) b
    simp [takeNone, botC] at this

end Object

/-! ## Part 2: the structure of the space -/

section Structure

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

theorem policyLE_refl (S : Policy X) : PolicyLE S S := fun _ _ _ h => h

theorem policyLE_trans {S T U : Policy X} (h1 : PolicyLE S T) (h2 : PolicyLE T U) :
    PolicyLE S U := fun c x y h => h2 c x y (h1 c x y h)

theorem takeNone_is_bottom (S : Policy X) : PolicyLE (takeNone : Policy X) S := by
  intro c x y h
  exact absurd h (by simp [takeNone])

theorem takeAll_is_top (S : Policy X) : PolicyLE S (takeAll : Policy X) := fun _ _ _ _ => rfl

/-- Taking wherever either takes, and wherever both take. -/
def policyJoin (S T : Policy X) : Policy X := fun c x y => S c x y || T c x y

def policyMeet (S T : Policy X) : Policy X := fun c x y => S c x y && T c x y

theorem le_policyJoin_left (S T : Policy X) : PolicyLE S (policyJoin S T) := by
  intro c x y h
  simp [policyJoin, h]

theorem policyMeet_le_left (S T : Policy X) : PolicyLE (policyMeet S T) S := by
  intro c x y h
  by_contra hs
  rw [Bool.not_eq_true] at hs
  simp [policyMeet, hs] at h

/-- **TAKING MORE DESCENDS FURTHER.** A policy that takes wherever another does lands at or below where the
other lands, so the order on policies is carried to the order on configurations, REVERSED. Carrier-general. -/
theorem taking_more_descends_further {S T : Policy X} (h : PolicyLE S T)
    (c : Pt X → Pt X → Option Bool) : cLE (step T c) (step S c) := by
  intro x y
  by_cases hT : T c x y = true
  · exact Or.inl (by simp [step, partialization, hT])
  · have hS : S c x y ≠ true := fun hh => hT (h c x y hh)
    refine Or.inr ?_
    simp [step, partialization, hT, hS]

/-! ### And the space is the first thing in the arc that can read the verdicts -/

/-- A policy blind to what is committed: it gives the same mask at configurations holding the same cells. -/
def SupportBlind (S : Policy X) : Prop :=
  ∀ c c' : Pt X → Pt X → Option Bool, (∀ x y : Pt X, c x y = none ↔ c' x y = none) → S c = S c'

theorem the_poles_are_support_blind :
    SupportBlind (takeAll : Policy X) ∧ SupportBlind (takeNone : Policy X) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- The policy that takes only where one verdict stands. -/
def takeTheFalse : Policy X := fun d x y => decide (d x y = some false)

theorem oneCells_have_the_same_support (a b : Pt X) (x y : Pt X) :
    oneCell a b true x y = none ↔ oneCell a b false x y = none := by
  by_cases h : x = a ∧ y = b
  · obtain ⟨rfl, rfl⟩ := h
    rw [oneCell_at, oneCell_at]
    simp
  · rw [oneCell_elsewhere a b true h, oneCell_elsewhere a b false h]

/-- **A POLICY CAN READ THE VERDICTS.** Two configurations holding exactly the same cells with different
verdicts receive different masks, so the space of policies is not blind to what is committed. This is the first
object in the arc that is not. Carrier-general. -/
theorem policies_can_read_the_verdicts (a b : Pt X) :
    ¬ SupportBlind (takeTheFalse : Policy X) := by
  intro h
  have he := congrFun (congrFun (h (oneCell a b true) (oneCell a b false)
    (oneCells_have_the_same_support a b)) a) b
  have h1 : (takeTheFalse : Policy X) (oneCell a b true) a b = false := by
    simp [takeTheFalse, oneCell_at]
  have h2 : (takeTheFalse : Policy X) (oneCell a b false) a b = true := by
    simp [takeTheFalse, oneCell_at]
  rw [h1, h2] at he
  exact absurd he (by simp)

end Structure

/-! ## Part 3: what a policy does, and whether anything does anything to it -/

section Dynamics

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- **A RUN IS PARAMETRIZED BY ONE POLICY THROUGHOUT.** Every step of a trajectory applies the same rule, and
nothing along the trajectory enters it. Carrier-general. -/
theorem the_run_carries_one_policy (S : Policy X) (c : Pt X → Pt X → Option Bool) (k : ℕ) :
    runPolicy S c (k + 1) = step S (runPolicy S c k) := rfl

/-- **THE TOP POLE REACHES ITS FIXED POINT IN ONE STEP FROM EVERY CONFIGURATION, AND STAYS.** Carrier-general.
-/
theorem the_top_pole_absorbs (c : Pt X → Pt X → Option Bool) :
    step (takeAll : Policy X) c = botC (Pt X)
      ∧ step (takeAll : Policy X) (botC (Pt X)) = botC (Pt X)
      ∧ ∀ k : ℕ, runPolicy (takeAll : Policy X) c (k + 1) = botC (Pt X) := by
  refine ⟨step_takeAll c, step_takeAll _, fun k => ?_⟩
  rw [the_run_carries_one_policy]
  exact step_takeAll _

/-- **THE BOTTOM POLE FIXES EVERY CONFIGURATION.** Every configuration whatever is invariant under it, so it
has no distinguished fixed point at all. Carrier-general. -/
theorem the_bottom_pole_fixes_everything (c : Pt X → Pt X → Option Bool) (k : ℕ) :
    runPolicy (takeNone : Policy X) c k = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [the_run_carries_one_policy, ih]
    exact step_takeNone c

/-- **AND SO A DEPARTURE IS NEVER REPAIRED BY THE BOTTOM POLE.** Whatever configuration a perturbation leaves
it at, it stays there, so the invariance is preservation of wherever it happens to be and not restoration of
anything. Carrier-general. -/
theorem the_bottom_pole_never_restores {c d : Pt X → Pt X → Option Bool} (hne : d ≠ c) (k : ℕ) :
    runPolicy (takeNone : Policy X) d k ≠ c := by
  rw [the_bottom_pole_fixes_everything d k]
  exact hne

/-- **WHERE THE TOP POLE REPAIRS EVERY DEPARTURE IN ONE STEP.** Whatever configuration a perturbation leaves it
at, one application returns it to the same place it always returns to. Carrier-general. -/
theorem the_top_pole_restores_from_anywhere (d : Pt X → Pt X → Option Bool) :
    step (takeAll : Policy X) d = botC (Pt X) := step_takeAll d

/-- **THE STABILITY ASYMMETRY, IN ONE STATEMENT.** One pole has a single fixed point which every configuration
reaches in one step and which absorbs every departure. The other fixes every configuration and restores none,
so what it preserves is wherever it was left. Carrier-general, given a configuration holding something. -/
theorem the_stability_asymmetry {c : Pt X → Pt X → Option Bool} {a b : Pt X} (h : c a b ≠ none) :
    (∀ d : Pt X → Pt X → Option Bool, step (takeAll : Policy X) d = botC (Pt X))
      ∧ (∀ d : Pt X → Pt X → Option Bool, step (takeNone : Policy X) d = d)
      ∧ (∀ k : ℕ, runPolicy (takeNone : Policy X) (step (takeAt a b) c) k ≠ c) := by
  refine ⟨step_takeAll, step_takeNone, fun k => ?_⟩
  refine the_bottom_pole_never_restores ?_ k
  intro he
  have := congrFun (congrFun he a) b
  rw [step_takeAt_at a b c] at this
  exact h this.symm

end Dynamics

/-! ## THE VERDICTS

PART 1: THE OBJECT, AND IT IS A FUNCTION SPACE.

A policy is a rule assigning to each configuration the mask of cells at which it takes the withdrawal, so THE
OBJECT IS A FUNCTION FROM CONFIGURATIONS TO MASKS and applying it once is the opening its mask names. That is
the whole of the definition and nothing further was needed: the arc already had masks, and the new object is
masks made to depend on where one is.

`step_takeAll` and `step_takeNone` fix the two poles and they are as different as they could be. Taking
everything empties everything IN ONE STEP FROM ANYWHERE. Taking nothing changes nothing at every configuration.
`the_poles_differ` confirms they part company wherever anything is held.

`the_policies_form_a_spectrum` settles the two-or-many question: taking at one cell only agrees with neither
pole wherever two cells are held. SO THE SPACE IS A SPECTRUM AND NOT A PAIR, and the poles are the extremes of
selectivity rather than the only options.

`a_configuration_does_not_determine_a_policy` is the separation from the state space, and it is the point of
the object. Two policies agree at one configuration and differ at another, so no configuration determines a
policy. A policy is defined everywhere at once, and is not a feature of anywhere.

PART 2: THE SPACE IS ORDERED, THE ORDER REVERSES INTO THE CONFIGURATIONS, AND THE SPACE READS THE VERDICTS.

`policyLE_refl`, `policyLE_trans`, `takeNone_is_bottom` and `takeAll_is_top` give the order with its two poles.
`le_policyJoin_left` and `policyMeet_le_left` give the bounds pointwise, so the space is at least a bounded
ordered space with joins and meets computed cellwise.

`taking_more_descends_further` is the connection to the arc and it is order-REVERSING. A policy taking wherever
another does lands at or below where the other lands, so the order on policies maps to the order on
configurations upside down: more taking is lower landing.

`policies_can_read_the_verdicts` is the finding of this part and it was not anticipated by the brief's frame.
Two configurations holding exactly the same cells with different verdicts receive different masks from a policy
that reads what is committed. So THE POLICY SPACE IS THE FIRST OBJECT IN THE ARC THAT IS NOT BLIND TO THE
VERDICTS. Every structure the arc built before this one, the coupling graph, the classes, the loads, the
containment, the mobility, read only where things are committed. A policy can read what is committed there.
`the_poles_are_support_blind` records that the two poles do not use that power, which is why the earlier
framing did not notice it was available.

PART 3: A POLICY DOES A GREAT DEAL AND NOTHING DOES ANYTHING TO IT.

`the_run_carries_one_policy` is the inertness, stated as what it is. Every step of a trajectory applies the same
rule and nothing along the trajectory enters it. The framework supplies no operation taking a policy to a
policy: the moves have configurations as their arguments and results, and a change of policy is not among them.
THAT IS RECORDED RATHER THAN PROVED, since it is a claim about what is definable and not a theorem, and it puts
policy change in the same place as the tie-break at a contest and the setter of prices. A POLICY IS EXOGENOUS.

But its ACTION has laws, and the asymmetry between the poles is a stability fact.

`the_top_pole_absorbs`: one fixed point, reached from EVERY configuration in ONE step, and held thereafter.
`the_bottom_pole_fixes_everything`: every configuration whatever is invariant, so this pole has no
distinguished fixed point at all.

`the_bottom_pole_never_restores` and `the_top_pole_restores_from_anywhere` are the sharp contrast, and it is not
the contrast the brief predicted. The brief expected the holding pole to be unstable, decaying under a lapse.
IT IS NOT UNSTABLE. It is perfectly stable and that is exactly the problem: it preserves WHEREVER IT HAPPENS TO
BE, including wherever a departure left it, and restores nothing. A perturbation is not decayed away, it is
KEPT.

`the_stability_asymmetry` puts the three together. One pole has an absorbing fixed point that repairs every
departure. The other has universal invariance that repairs none. So the asymmetry is not attracting against
repelling: BOTH ARE STABLE, and what differs is that one has a place it returns to and the other has none, so
that under the first a departure is undone and under the second a departure is permanent.

PART 4: WHAT IT IS AND WHETHER IT HAS DYNAMICS.

WHAT IT IS. A policy: a function from configurations to masks, forming a bounded ordered space with cellwise
meets and joins, whose order carries into the configurations reversed, with a spectrum of selective policies
between the two poles, and which is the first object in the arc able to read the verdicts.

WHETHER IT HAS DYNAMICS OF ITS OWN. No, as far as the framework goes. Nothing in the algebra takes a policy to
a policy, and a run carries one policy unchanged from beginning to end. A change of policy is external input.

WHETHER ITS ACTION HAS LAWS. Yes, and they are the asymmetry the arc has been circling, now stated at the level
where it lives. The taking pole has one place it goes and goes there from anywhere, in one step, and returns
there after any departure. The declining pole goes nowhere and stays wherever it is put, so nothing it suffers
is ever undone.

REGISTER READINGS. Report only, defeasible, supplied by the register rather than derived.

  ON WHAT THE THING IS. A stance toward revision is not a belief, not a state and not a history. It is a rule
  covering situations one is not in, which is why it cannot be read off any moment and why it is intelligible
  to ask what someone would do rather than only what they did. And it admits degrees: one can be willing to
  give up some things and not others, and that middle is most of the space.

  ON WHETHER IT CHANGES BY ITSELF. Nothing in the ordinary movement of what one holds changes what one is
  willing to give up. Changing that is a different kind of act and this framework does not contain it, which is
  the same shape as the other things it has had to leave outside: who breaks a tie, who sets the cost.

  ON THE STABILITY, WITH THE CORRECTION. The expectation was that holding on would be fragile and decay under a
  lapse. It is the reverse. Holding on is perfectly stable, and that is what is wrong with it: it keeps
  whatever it is handed, including damage, and has nowhere it returns to. Letting go is stable too, and it has
  somewhere it returns to, so what happens to it is undone. THE DIFFERENCE IS NOT FRAGILITY AGAINST ROBUSTNESS.
  It is having a place one comes back to against having none.

  COGNITION. A policy of revising is not a belief and does not compete with beliefs. It survives every change
  of belief unchanged, and no argument about any particular matter touches it. Its virtue is not that it is
  hard to disturb, since the opposite policy is just as hard to disturb; it is that it has a resting place, so
  a mistake gets returned from. The opposite policy holds a mistake exactly as firmly as anything else.

  POLITICS. Whether an arrangement is revisable is not one of its provisions and is not changed by amending
  any of them. Both an open and an entrenched arrangement are stable against ordinary business. What separates
  them is that the first has a condition it returns to and the second keeps whatever it was last left with,
  including what was done to it.

AXIOM PROFILE AND GRADUATION. Every result is at baseline or below. Graduation is NOT proposed: the object is
defined here and has not been placed. Three are flagged as substantive and carrier-general:
`taking_more_descends_further`, which links the new order to the arc's; `policies_can_read_the_verdicts`, which
is the first sighting of the second factor from a structure; and `the_stability_asymmetry`, which states the
asymmetry at the level where it lives.

WHAT REMAINS OPEN

1. The order on policies has bounds and cellwise meets and joins. Whether it is a lattice in the full sense,
   and whether it is complete, is not established.
2. Only the two poles and the one-cell selective policies are examined. The verdict-reading policies are shown
   to exist and are not surveyed, and they are where the second factor first becomes visible.
3. Inertness is recorded as a fact about what the framework defines and is not a theorem. A framework with a
   policy-editing operation is not ruled out by anything here.
4. Fixed points are examined for the two poles only. Which configurations are fixed by a selective policy, and
   whether a policy can have several, is untouched.
5. Nothing here is graduated. -/

#print axioms step_takeAll
#print axioms step_takeNone
#print axioms step_takeAt_at
#print axioms step_takeAt_elsewhere
#print axioms the_poles_differ
#print axioms the_policies_form_a_spectrum
#print axioms a_configuration_does_not_determine_a_policy
#print axioms policyLE_refl
#print axioms policyLE_trans
#print axioms takeNone_is_bottom
#print axioms takeAll_is_top
#print axioms le_policyJoin_left
#print axioms policyMeet_le_left
#print axioms taking_more_descends_further
#print axioms the_poles_are_support_blind
#print axioms oneCells_have_the_same_support
#print axioms policies_can_read_the_verdicts
#print axioms the_run_carries_one_policy
#print axioms the_top_pole_absorbs
#print axioms the_bottom_pole_fixes_everything
#print axioms the_bottom_pole_never_restores
#print axioms the_top_pole_restores_from_anywhere
#print axioms the_stability_asymmetry

end Chiralogy.StanceSpace
