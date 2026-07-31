import Chiralogy.Experiments.archive.StanceCore

/-! ARCHIVED (fully graduated). The policies that read what is committed.

GRADUATED to `Model/StanceContent`: `keepSupported_reads_content`, `the_two_act_identically`,
`the_recommendation_is_a_region`, `keepSupported_fixed_iff`, `keepSupported_is_neither_pole`, the ordering of
the derived family, and the `uniformExcept` witnesses. Spec 4.a.20.

`keepSupported_fixed_iff` graduated as a fixed-point characterization in Mathlib's sense.

Typechecks standalone. -/

/-! # Experiment (LIVE): the policies that read what is committed

A policy assigns to each configuration the mask of withdrawals it takes. The two poles do not look at what is
committed anywhere. This build surveys the policies that do, which is where a recommendation about content
first becomes sayable.

Register-neutral throughout: no statement and no proof mentions any domain, and no name carries a register
term. The names used are policy, take, decline, supported, uniform and fixed. All interpretive readings are in
the report only.

Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy
open Chiralogy.StanceCore

set_option linter.unusedSectionVars false

namespace Chiralogy.ContentStance

attribute [local instance] Classical.propDecidable

section Space

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

/-! The object, the operator, the order on policies, the cell bookkeeping and their basic lemmas are
`StanceCore`'s: this file adds no copy of them. -/

end Space

/-! ## Part 1: the policies that look at what is committed -/

section Derived

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

/-- Take exactly where something is held off the diagonal and the two rows are not held apart by present
values. -/
noncomputable def dropUnsupported : Policy X :=
  fun c x y => decide (x ≠ y ∧ c x y ≠ none ∧ ¬ presentCarried c x y)

/-- Every verdict a configuration holds is the same one. -/
def Uniform (c : Pt X → Pt X → Option Bool) : Prop :=
  ∀ x y x' y' : Pt X, c x y ≠ none → c x' y' ≠ none → c x y = c x' y'

/-- Take everything off the diagonal exactly when the configuration commits only one verdict. -/
noncomputable def dropUniform : Policy X := fun c x y => decide (x ≠ y ∧ Uniform c)

/-- **UNIFORMITY BLOCKS PRESENT SUPPORT EVERYWHERE.** Carrier-general. -/
theorem uniform_blocks_present_support {c : Pt X → Pt X → Option Bool} (h : Uniform c) (x x' : Pt X) :
    ¬ presentCarried c x x' := by
  rintro ⟨y, b1, b2, h1, h2, hb⟩
  have := h x y x' y (by rw [h1]; exact Option.some_ne_none _)
    (by rw [h2]; exact Option.some_ne_none _)
  rw [h1, h2] at this
  exact hb (Option.some_inj.mp this)

/-! ### Two configurations that hold the same cells and differ in what they hold -/

def uniformExcept (a b : Pt X) : Pt X → Pt X → Option Bool :=
  fun x y => if x = a ∧ y = b then none else some true

theorem uniformExcept_hole (a b : Pt X) : uniformExcept a b a b = none := by simp [uniformExcept]

theorem uniformExcept_elsewhere (a b : Pt X) {x y : Pt X} (h : ¬ (x = a ∧ y = b)) :
    uniformExcept a b x y = some true := by simp [uniformExcept, h]

theorem the_two_hold_the_same_cells (a b : Pt X) (x y : Pt X) :
    punctured a b x y = none ↔ uniformExcept a b x y = none := by
  by_cases hq : x = a ∧ y = b
  · obtain ⟨rfl, rfl⟩ := hq
    rw [uniformExcept_hole]
    simp [punctured]
  · rw [punctured_elsewhere a b hq, uniformExcept_elsewhere a b hq]
    simp

/-- And one pair of the second is not. Carrier-general, given three distinct points. -/
theorem uniformExcept_is_unsupported {a b x : Pt X} (hab : a ≠ b) (hax : a ≠ x) :
    ¬ presentCarried (uniformExcept a b) a x := by
  rintro ⟨y, b1, b2, h1, h2, hb⟩
  by_cases hy : y = b
  · subst hy
    rw [uniformExcept_hole] at h1
    exact Option.some_ne_none _ h1.symm
  · rw [uniformExcept_elsewhere a b (fun hq => hy hq.2)] at h1
    rw [uniformExcept_elsewhere a b (fun hq => hax hq.1.symm)] at h2
    exact hb ((Option.some_inj.mp h1.symm).trans (Option.some_inj.mp h2))

/-- **THE KEEP-SUPPORTED POLICY READS WHAT IS COMMITTED.** Two configurations holding exactly the same cells, one
committing by agreement and one uniformly, receive different masks: it declines at the first and takes at the
second. Carrier-general, given three distinct points. -/
theorem keepSupported_reads_content {a b x : Pt X} (hab : a ≠ b) (hax : a ≠ x) :
    (∀ p q : Pt X, punctured a b p q = none ↔ uniformExcept a b p q = none)
      ∧ keepSupported (punctured a b) a x = false
      ∧ keepSupported (uniformExcept a b) a x = true :=
  ⟨the_two_hold_the_same_cells a b,
   keepSupported_declines (punctured_is_supported hab hax),
   keepSupported_takes hax (uniformExcept_is_unsupported hab hax)⟩

/-- **AND IT IS NEITHER POLE.** It declines somewhere, so it is not the taking pole, and it takes somewhere, so
it is not the declining one. Carrier-general, given three distinct points. -/
theorem keepSupported_is_neither_pole {a b x : Pt X} (hab : a ≠ b) (hax : a ≠ x) :
    keepSupported (punctured a b) a x ≠ (takeAll : Policy X) (punctured a b) a x
      ∧ keepSupported (uniformExcept a b) a x ≠ (takeNone : Policy X) (uniformExcept a b) a x := by
  refine ⟨?_, ?_⟩
  · rw [keepSupported_declines (punctured_is_supported hab hax)]
    simp [takeAll]
  · rw [keepSupported_takes hax (uniformExcept_is_unsupported hab hax)]
    simp [takeNone]

end Derived

/-! ## Part 2: how the derived policies sit, and whether one is singled out -/

section Region

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

/-- **THE SELECTIVE POLICY IS BELOW THE KEEP-SUPPORTED ONE.** Taking only where something is held and unsupported
is taking a subset of where the keep-supported policy takes. Carrier-general. -/
theorem dropUnsupported_le_keepSupported :
    PolicyLE (dropUnsupported : Policy X) (keepSupported : Policy X) := by
  intro c x y h
  simp only [dropUnsupported, decide_eq_true_eq] at h
  exact keepSupported_takes h.1 h.2.2

/-- **AND SO IS THE UNIFORMITY POLICY.** At a configuration committing only one verdict nothing is held apart by
present values, so the keep-supported policy takes everywhere the uniformity policy does. Carrier-general. -/
theorem dropUniform_le_keepSupported :
    PolicyLE (dropUniform : Policy X) (keepSupported : Policy X) := by
  intro c x y h
  simp only [dropUniform, decide_eq_true_eq] at h
  exact keepSupported_takes h.1 (uniform_blocks_present_support h.2 x y)

/-- **THE KEEP-SUPPORTED POLICY IS AN UPPER BOUND OF THE DERIVED FAMILY.** Carrier-general. -/
theorem keepSupported_bounds_the_family :
    PolicyLE (dropUnsupported : Policy X) (keepSupported : Policy X)
      ∧ PolicyLE (dropUniform : Policy X) (keepSupported : Policy X) :=
  ⟨dropUnsupported_le_keepSupported, dropUniform_le_keepSupported⟩

/-- **BUT TWO OF THEM ACT IDENTICALLY.** The keep-supported policy and the selective one differ only at cells where
nothing is held, and taking a withdrawal where nothing is held does nothing. So they are distinct policies with
the same effect at every configuration. Carrier-general. -/
theorem the_two_act_identically (c : Pt X → Pt X → Option Bool) :
    step (keepSupported : Policy X) c = step (dropUnsupported : Policy X) c := by
  funext x y
  by_cases hv : c x y = none
  · rw [step_preserves_absence hv, step_preserves_absence hv]
  · by_cases hs : presentCarried c x y
    · simp only [step, partialization, keepSupported, dropUnsupported]
      simp [hs]
    · by_cases hxy : x = y
      · simp only [step, partialization, keepSupported, dropUnsupported]
        simp [hxy]
      · simp only [step, partialization, keepSupported, dropUnsupported]
        simp [hs, hv, hxy]

/-- **AND THEY ARE NOT THE SAME POLICY.** At a cell where nothing is held and nothing is supported they
disagree, so the recommendation fixes an ACTION and not a policy: what is picked out is a region of the space
and not a point. Carrier-general, given a pair with nothing held and nothing supported. -/
theorem the_recommendation_is_a_region {c : Pt X → Pt X → Option Bool} {x y : Pt X} (hxy : x ≠ y)
    (hv : c x y = none) (hs : ¬ presentCarried c x y) :
    keepSupported c x y ≠ dropUnsupported c x y := by
  rw [keepSupported_takes hxy hs]
  simp [dropUnsupported, hv]

end Region

/-! ## Part 3: where the keep-supported policy comes to rest -/

section Rest

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

/-- **THE KEEP-SUPPORTED POLICY RESTS EXACTLY WHERE EVERYTHING HELD IS SUPPORTED.** Carrier-general. -/
theorem keepSupported_fixed_iff (c : Pt X → Pt X → Option Bool) :
    step (keepSupported : Policy X) c = c
      ↔ ∀ x y : Pt X, x ≠ y → c x y ≠ none → presentCarried c x y := by
  constructor
  · intro h x y hxy hv
    by_contra hs
    have hc := congrFun (congrFun h x) y
    simp only [step, partialization] at hc
    rw [if_pos (by rw [keepSupported_takes hxy hs])] at hc
    exact hv hc.symm
  · intro h
    funext x y
    by_cases hv : c x y = none
    · rw [step_preserves_absence hv, hv]
    · by_cases hxy : x = y
      · simp only [step, partialization]
        rw [if_neg (by simp [keepSupported, hxy])]
      · simp only [step, partialization]
        rw [if_neg (by rw [keepSupported_declines (h x y hxy hv)]; simp)]

/-- **THE WHOLLY UNCOMMITTED CONFIGURATION IS ONE RESTING PLACE.** Carrier-general. -/
theorem the_empty_configuration_rests :
    step (keepSupported : Policy X) (botC (Pt X)) = botC (Pt X) :=
  (keepSupported_fixed_iff _).mpr (fun _ _ _ h => absurd rfl h)

/-- **AND SO IS A CONFIGURATION HOLDING NEARLY EVERYTHING.** Every pair of distinct rows of it is held apart by
present values, so the keep-supported policy takes nothing there. The resting places are not all empty.
Carrier-general, given two distinct points. -/
theorem a_rich_configuration_rests {a b : Pt X} (hab : a ≠ b) :
    step (keepSupported : Policy X) (punctured a b) = punctured a b :=
  (keepSupported_fixed_iff _).mpr (fun _ _ hxy _ => punctured_is_supported hab hxy)

/-- **SO THE KEEP-SUPPORTED POLICY HAS MANY RESTING PLACES AND NO SINGLE ONE.** It rests at the wholly uncommitted
configuration and at a configuration holding nearly everything, so unlike the taking pole it does not go to one
place from anywhere. Carrier-general, given two distinct points. -/
theorem the_resting_places_are_many {a b : Pt X} (hab : a ≠ b) :
    step (keepSupported : Policy X) (botC (Pt X)) = botC (Pt X)
      ∧ step (keepSupported : Policy X) (punctured a b) = punctured a b
      ∧ (punctured a b : Pt X → Pt X → Option Bool) ≠ botC (Pt X) := by
  refine ⟨the_empty_configuration_rests, a_rich_configuration_rests hab, ?_⟩
  intro he
  have hc := congrFun (congrFun he a) a
  rw [punctured_elsewhere a b (fun hq => hab (hq.1.symm.trans hq.2))] at hc
  exact Option.some_ne_none _ hc

/-- **AND IT ALWAYS DESCENDS, STRICTLY UNTIL IT RESTS.** Every application only empties, and where it does
anything it holds strictly fewer cells, so on a finite carrier the iteration reaches a resting place.
Carrier-general. -/
theorem it_descends_strictly_until_it_rests (S : Policy X) (c : Pt X → Pt X → Option Bool)
    (h : step S c ≠ c) : heldCells (step S c) ⊂ heldCells c := by
  refine ⟨fun p hp => ?_, fun hsub => ?_⟩
  · rw [mem_heldCells] at hp ⊢
    rcases step_deflationary S c p.1 p.2 with hn | he
    · exact absurd hn hp
    · rw [← he]; exact hp
  · refine h ?_
    funext x y
    rcases step_deflationary S c x y with hn | he
    · by_cases hv' : c x y = none
      · rw [hn, hv']
      · have hmem : (x, y) ∈ heldCells c := mem_heldCells.mpr hv'
        have hm := hsub hmem
        rw [mem_heldCells] at hm
        exact absurd hn hm
    · exact he

/-- **THE THREE RESTING BEHAVIOURS, SIDE BY SIDE.** The taking pole rests at one configuration and reaches it
from anywhere in one step. The declining pole rests at every configuration. The keep-supported policy rests exactly
where everything held is supported, which is neither one place nor all of them. Carrier-general, given two
distinct points. -/
theorem the_three_resting_behaviours {a b : Pt X} (hab : a ≠ b) :
    (∀ c : Pt X → Pt X → Option Bool, step (takeAll : Policy X) c = botC (Pt X))
      ∧ (∀ c : Pt X → Pt X → Option Bool, step (takeNone : Policy X) c = c)
      ∧ (∀ c : Pt X → Pt X → Option Bool, step (keepSupported : Policy X) c = c
            ↔ ∀ x y : Pt X, x ≠ y → c x y ≠ none → presentCarried c x y)
      ∧ step (keepSupported : Policy X) (punctured a b) = punctured a b := by
  refine ⟨fun c => full_partialization_is_bot c, fun c => ?_, keepSupported_fixed_iff,
    a_rich_configuration_rests hab⟩
  funext x y
  simp [step, takeNone, partialization]

end Rest

/-! ## THE VERDICTS

PART 1: THE CONTENT-READING POLICIES EXIST AND ARE ORDINARY TO WRITE DOWN.

Three come out naturally. `keepSupported` declines wherever two rows are held apart by present values and takes
everywhere else. `dropUnsupported` takes exactly where something is held and is not so held apart.
`dropUniform` takes everything exactly when the configuration commits only one verdict.

`keepSupported_reads_content` shows the first of these does what the previous build said was possible
and nothing had yet done. Two configurations holding EXACTLY THE SAME CELLS, one committing by agreement and one
committing uniformly, receive DIFFERENT MASKS: it declines at the first and takes at the second. So the second
factor is not merely visible from this level, it is ACTED ON.

`keepSupported_is_neither_pole` places it: it declines somewhere and takes somewhere, so it is neither
the taking pole nor the declining one. It is a genuine interior policy that looks at what is committed.

PART 2: THE FAMILY IS ORDERED, AND WHAT IS PICKED OUT IS AN ACTION AND NOT A POLICY.

`dropUnsupported_le_keepSupported` and `dropUniform_le_keepSupported` order the family, with the discerning
policy above both. The second uses that uniformity blocks present support everywhere, so the uniformity policy
takes only where the discerning one already does.

`the_two_act_identically` is the finding of this part. The discerning policy and the selective one differ ONLY
at cells where nothing is held, and taking a withdrawal where nothing is held does nothing. SO THEY ARE
DISTINCT POLICIES WITH THE SAME EFFECT AT EVERY CONFIGURATION.

`the_recommendation_is_a_region` draws the consequence, and it answers the question the brief called the test.
What a recommendation of this kind fixes is an ACTION and not a policy. Policies differing only where nothing is
held are indistinguishable in everything they do, so the recommendation picks out A REGION OF THE POLICY SPACE
AND NOT A POINT, and the region is exactly the policies agreeing on the held cells.

PART 3: THE RESTING BEHAVIOUR REFINES, AND THE PREDICTION WAS TOO STRONG.

`keepSupported_fixed_iff` is the characterization and it is exact: the discerning policy rests at a
configuration precisely when EVERYTHING HELD IS SUPPORTED.

`a_rich_configuration_rests` is the payoff and it does hold. A configuration holding nearly every cell, every
pair of whose distinct rows is held apart by present values, is a resting place. SO THE DISCERNING POLICY HAS
RESTING PLACES THAT ARE NOT EMPTY, which the taking pole does not: that one always ends at the wholly
uncommitted configuration.

BUT THE PREDICTION THAT IT RETURNS TO A DISTINGUISHED RICH PLACE FROM ANYWHERE IS FALSE.
`the_resting_places_are_many`: it also rests at the wholly uncommitted configuration, vacuously, since nothing
held is nothing to be unsupported. THERE IS NO SINGLE PLACE IT GOES. Where it comes to rest depends on where it
started, and both an empty and a nearly full resting place exist.

`it_descends_strictly_until_it_rests` says what is true instead, and it is enough to matter. Every application
only empties, and wherever it does anything at all it holds strictly fewer cells afterwards. On a finite carrier
that cannot go on, so the iteration always reaches a resting place. IT ALWAYS COMES TO REST, AND WHERE IS NOT
FIXED IN ADVANCE.

`the_three_resting_behaviours` puts the three together. One place from anywhere. Every place. Or a place that
depends on where one started, always reached, and characterized exactly by everything held being supported.

PART 4: ASSEMBLED.

The content-reading policies are ordinary objects and the discerning one is the natural member of the family.
It is the first thing in the arc that acts on the second factor rather than merely being unable to see it.

What a recommendation about content fixes is an action, not a policy: a region, and the region is the policies
agreeing on the held cells.

And the resting behaviour is a genuine third case between the poles, with the payoff intact and the prediction
corrected. The rest is not empty, which was the point. But it is not unique and it is not reached from
anywhere, which was the overreach. What is guaranteed is that it always arrives somewhere, and that wherever it
arrives, everything still held is held apart by what is present rather than by what is absent.

REGISTER READINGS. Report only, defeasible, supplied by the register rather than derived.

  ON WHAT IS NOW SAYABLE. Until this point the only counsel available was about whether to hold on at all.
  There is now a counsel about WHAT to hold: keep what is held apart by what is actually present, release what
  is held apart only by what has not been said. That is a policy one can state, and it is neither of the two
  extremes.

  ON WHAT IT PICKS OUT. It does not pick out one way of proceeding. Any two ways agreeing about everything one
  actually holds are the same in every effect, and they can differ freely about what to do with matters one has
  not taken up. So the counsel is about one's holdings and is silent about one's dispositions elsewhere, which
  is the right amount for a counsel about content to say.

  COGNITION, WITH THE CORRECTION. Discernment is not emptying the mind, and its resting place is not blank: a
  view every part of which is held apart from its rivals by things that are actually so is a resting place, and
  a nearly complete one. That much of the hoped-for result survives.

  What does not survive is the idea that discernment returns one to some best understanding from wherever one
  starts. It does not. It always comes to rest, and where depends on where one began: someone starting with
  little arrives at little, and the emptiness of that resting place is not a failure of the policy but a fact
  about the starting point. What the policy guarantees is only this, and it is not nothing: whatever one ends
  up still holding is held up by something, and not by what one has declined to consider.

  POLITICS. An arrangement that keeps what rests on grounds it can actually exhibit, and releases what rests
  only on what is not raised, comes to rest, and what it rests on can be extensive. But it does not converge to
  a best arrangement from any starting point: it sheds and it settles, and what remains after settling depends
  on what was there to begin with.

AXIOM PROFILE AND GRADUATION. Every result is at baseline or below. Graduation is NOT proposed: the policies are
defined here and the object they live in has not been placed. Three are flagged as substantive and
carrier-general: `keepSupported_reads_content`, which is the second factor first acted on;
`the_two_act_identically`, which shows the recommendation is a region; and `keepSupported_fixed_iff`, which
characterizes the resting places exactly.

WHAT REMAINS OPEN

1. Support is taken at the level of a pair of rows, since that is where the canonical notion lives. A genuinely
   cell-level notion of support is not defined, and whether one exists that behaves better is not asked.
2. Termination is argued from the strict descent and finiteness, and the iteration to a resting place is not
   formed as an object. The resting place as a function of the start is therefore not studied.
3. The uniformity policy is defined and barely used. Where it sits relative to the selective one is not
   settled, and the two look incomparable.
4. Nothing here treats a policy that both takes and lands. Every policy in this build only empties, so the
   whole survey is on one arm.
5. Nothing here is graduated. -/

#print axioms uniform_blocks_present_support
#print axioms uniformExcept_hole
#print axioms uniformExcept_elsewhere
#print axioms the_two_hold_the_same_cells
#print axioms uniformExcept_is_unsupported
#print axioms keepSupported_reads_content
#print axioms keepSupported_is_neither_pole
#print axioms dropUnsupported_le_keepSupported
#print axioms dropUniform_le_keepSupported
#print axioms keepSupported_bounds_the_family
#print axioms the_two_act_identically
#print axioms the_recommendation_is_a_region
#print axioms keepSupported_fixed_iff
#print axioms the_empty_configuration_rests
#print axioms a_rich_configuration_rests
#print axioms the_resting_places_are_many
#print axioms it_descends_strictly_until_it_rests
#print axioms the_three_resting_behaviours

end Chiralogy.ContentStance
