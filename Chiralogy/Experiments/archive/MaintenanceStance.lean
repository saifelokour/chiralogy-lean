import Chiralogy.Experiments.archive.StanceCore

/-! ARCHIVED (partly graduated). The stances that form as well as release.

GRADUATED to `Model/Stance`: the band and its two exits (`the_band_has_two_exits`, now stated with canonical
`isTotal`, so the exits are the order-bottom and the order-maxima of 4.a.15), the three extremes, the
period-two periodic orbit (`there_is_a_cycle`, `an_invariant_band_without_a_resting_place`),
`the_two_extremes_are_distinct_failures`, and `restoreTo` with its constant-map behaviour. To
`Model/StanceContent`: `the_return_is_to_a_supported_position`. Spec 4.a.19, 4.a.20.

NOT GRADUATED, retained here as the record: the whole REVERSE-ORDER half (`applyStanceRev`, `formStep`,
`the_orders_differ`, `the_reverse_admits_a_null_step`, `applyStance_can_reassign_where_reverse_cannot`,
`there_is_a_reverse_cycle`, `restoreToRev_second_application_reaches_target`). It is carrier-general and it
verifies, but it is a SECOND operator on the same object whose place in the module is not settled: the
within-application order is a definitional choice, and graduating one order as canonical while the other lives
in an experiment would assert a priority the arc has not established. It stays a live finding.

`Saturated` was dropped as a re-derivation of canonical `isTotal`.

Typechecks standalone. -/

/-! # Experiment (LIVE): the stances that form as well as release

Every stance built so far only releases. This build adds the other direction. A stance is given two parts: a
mask of cells it releases and an instruction of what to form, and one application releases first and then forms
into whatever is open. Forming into what is already held does nothing, which is the kernel's own behaviour for a
commit and is not an extra assumption.

The questions are whether the enlarged space contains anything the releasing-only space could not express,
whether a quantity can be held steady by continued action rather than merely stopped at, and whether the
enlarged space has a second extreme at the opposite end from the empty one.

Register-neutral throughout: no statement and no proof mentions any domain, and no name carries a register
term. The names used are stance, release, form, band, mobile, saturated and restore. All readings are in the
report only, and are flagged provisional.

The moves are the canonical ones. Releasing is `partialization` at the mask the stance names, and forming has
the shape of the derived fill: it writes only where nothing is held. Neither is a new primitive.

Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy
open Chiralogy.StanceCore

set_option linter.unusedSectionVars false

namespace Chiralogy.MaintenanceStance

/-! The stance object, its two operators, the iterator, the policy embedding and the deflationary lemmas are
`StanceCore`'s: this file adds no copy of them. -/

section Space

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

end Space

/-! ## Part 1: the three extremes, and the one that is new -/

section Extremes

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

/-- Release everything, form nothing. -/
def dropAll : Stance X := ⟨fun _ _ _ => true, fun _ _ _ => none⟩

/-- Release nothing, form nothing. -/
def holdAll : Stance X := ⟨fun _ _ _ => false, fun _ _ _ => none⟩

/-- Release nothing, form everywhere. -/
def formAll : Stance X := ⟨fun _ _ _ => false, fun _ _ _ => some true⟩

theorem applyStance_dropAll (c : Pt X → Pt X → Option Bool) : applyStance (dropAll : Stance X) c = botC (Pt X) := by
  funext x y
  rw [applyStance_of_dropped (T := (dropAll : Stance X)) rfl]
  rfl

theorem applyStance_holdAll (c : Pt X → Pt X → Option Bool) : applyStance (holdAll : Stance X) c = c := by
  funext x y
  by_cases hv : c x y = none
  · rw [applyStance_of_kept_open (T := (holdAll : Stance X)) rfl hv, hv]
    rfl
  · rcases hb : c x y with - | v
    · exact absurd hb hv
    · rw [forming_is_powerless_at_a_held_cell (T := (holdAll : Stance X)) rfl hb]

theorem applyStance_formAll (c : Pt X → Pt X → Option Bool) (x y : Pt X) :
    applyStance (formAll : Stance X) c x y = if c x y = none then some true else c x y := by
  by_cases hv : c x y = none
  · rw [applyStance_of_kept_open (T := (formAll : Stance X)) rfl hv, if_pos hv]
    rfl
  · rcases hb : c x y with - | v
    · exact absurd hb hv
    · rw [forming_is_powerless_at_a_held_cell (T := (formAll : Stance X)) rfl hb]
      simp

/-- **FORMING EVERYWHERE LEAVES NOTHING OPEN, IN ONE APPLICATION FROM ANYWHERE.** Carrier-general. -/
theorem formAll_saturates (c : Pt X → Pt X → Option Bool) :
    isTotal (applyStance (formAll : Stance X) c) := by
  intro x y
  rw [applyStance_formAll]
  by_cases hv : c x y = none
  · rw [if_pos hv]; exact Option.some_ne_none _
  · rw [if_neg hv]; exact hv

/-- **AND IT KEEPS WHAT IT REACHES.** Carrier-general. -/
theorem formAll_fixes_the_saturated {c : Pt X → Pt X → Option Bool} (h : isTotal c) :
    applyStance (formAll : Stance X) c = c := by
  funext x y
  rw [applyStance_formAll, if_neg (h x y)]

/-- **THE FORMING EXTREME IS NOT EXPRESSIBLE BY RELEASING ALONE.** At the wholly uncommitted configuration it
lands everywhere, where every never-forming stance stays. So the enlarged space is strictly larger, and the
extreme at the far end is the one the earlier space structurally could not name. Carrier-general, given a
point. -/
theorem formAll_is_new (a : Pt X) :
    applyStance (formAll : Stance X) (botC (Pt X)) a a = some true
      ∧ ∀ T : Stance X, FormsNothing T → applyStance T (botC (Pt X)) a a = none := by
  refine ⟨?_, fun T h => formsNothing_preserves_absence h rfl⟩
  rw [applyStance_formAll]
  rfl

/-- **AND THE THREE EXTREMES ARE THREE DIFFERENT STANCES.** Releasing everything lands at nothing held, forming
everywhere lands at nothing open, and holding all keeps whatever it is handed. Carrier-general, given a point.
-/
theorem the_three_extremes_differ (a : Pt X) :
    applyStance (dropAll : Stance X) (botC (Pt X)) a a = none
      ∧ applyStance (formAll : Stance X) (botC (Pt X)) a a = some true
      ∧ applyStance (holdAll : Stance X) (botC (Pt X)) = botC (Pt X) := by
  refine ⟨by rw [applyStance_dropAll]; rfl, ?_, applyStance_holdAll _⟩
  rw [applyStance_formAll]
  rfl

end Extremes

/-! ## Part 2: the band, and whether it can be held -/

section Band

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

theorem heldCells_nonempty_iff {c : Pt X → Pt X → Option Bool} :
    (heldCells c).Nonempty ↔ ∃ x y : Pt X, c x y ≠ none := by
  rw [heldCells, Finset.filter_nonempty_iff]
  exact ⟨fun ⟨p, _, hp⟩ => ⟨p.1, p.2, hp⟩, fun ⟨x, y, h⟩ => ⟨(x, y), Finset.mem_univ _, h⟩⟩

theorem fillableCells_nonempty_iff {c : Pt X → Pt X → Option Bool} :
    (fillableCells c).Nonempty ↔ ∃ x y : Pt X, c x y = none := by
  rw [fillableCells, Finset.filter_nonempty_iff]
  exact ⟨fun ⟨p, _, hp⟩ => ⟨p.1, p.2, hp⟩, fun ⟨x, y, h⟩ => ⟨(x, y), Finset.mem_univ _, h⟩⟩

theorem mobile_iff {c : Pt X → Pt X → Option Bool} :
    Mobile c ↔ (∃ x y : Pt X, c x y ≠ none) ∧ (∃ x y : Pt X, c x y = none) := by
  rw [Mobile, heldCells_nonempty_iff, fillableCells_nonempty_iff]

/-- **THE BAND HAS EXACTLY TWO EXITS.** A configuration fails to be mobile precisely when nothing is held or
nothing is open, and those are the two ends. Carrier-general. -/
theorem the_band_has_two_exits (c : Pt X → Pt X → Option Bool) :
    ¬ Mobile c ↔ (c = botC (Pt X) ∨ isTotal c) := by
  rw [mobile_iff]
  constructor
  · intro h
    by_cases hh : ∃ x y : Pt X, c x y ≠ none
    · refine Or.inr (fun x y => ?_)
      by_contra hv
      exact h ⟨hh, ⟨x, y, hv⟩⟩
    · refine Or.inl ?_
      funext x y
      by_contra hv
      exact hh ⟨x, y, hv⟩
  · rintro (rfl | hs) ⟨hheld, hopen⟩
    · obtain ⟨x, y, hx⟩ := hheld
      exact hx rfl
    · obtain ⟨x, y, hx⟩ := hopen
      exact hs x y hx

/-- **AND A RELEASING-ONLY STANCE CAN REACH ONLY ONE OF THEM.** What is open stays open, so no never-forming
stance ever leaves the band at the forming end. The second exit is invisible from the releasing-only space.
Carrier-general. -/
theorem the_second_exit_is_out_of_reach {T : Stance X} (h : FormsNothing T)
    {c : Pt X → Pt X → Option Bool} (hm : Mobile c) : ¬ isTotal (applyStance T c) := by
  obtain ⟨-, hopen⟩ := mobile_iff.mp hm
  obtain ⟨x, y, hxy⟩ := hopen
  intro hs
  exact hs x y (formsNothing_preserves_absence h hxy)

/-! ### A stance that returns to a named configuration -/

/-- Release whatever disagrees with a named configuration, and form that configuration into the openings. -/
def restoreTo (t : Pt X → Pt X → Option Bool) : Stance X :=
  ⟨fun c x y => decide (c x y ≠ t x y), fun _ x y => t x y⟩

/-- **THE RESTORING STANCE ARRIVES AT ITS TARGET IN ONE APPLICATION FROM EVERY CONFIGURATION.** Where the
configuration disagrees it releases and forms again; where it agrees it leaves it. Carrier-general. -/
theorem restoreTo_returns_from_anywhere (t c : Pt X → Pt X → Option Bool) :
    applyStance (restoreTo t) c = t := by
  funext x y
  by_cases hne : c x y ≠ t x y
  · rw [applyStance_of_dropped (T := restoreTo t) (by simp [restoreTo, hne])]
    rfl
  · rw [not_not] at hne
    by_cases hv : c x y = none
    · rw [applyStance_of_kept_open (T := restoreTo t) (by simp [restoreTo, hne]) hv]
      rfl
    · rcases hb : c x y with - | v
      · exact absurd hb hv
      · rw [forming_is_powerless_at_a_held_cell (T := restoreTo t) (by simp [restoreTo, hne]) hb,
          ← hne, hb]

theorem restoreTo_fixes_its_target (t : Pt X → Pt X → Option Bool) :
    applyStance (restoreTo t) t = t := restoreTo_returns_from_anywhere t t

/-- **AND ITS TARGET NEED NOT BE THE EMPTY CONFIGURATION.** On the releasing-only arm the one place reached from
everywhere had to be the empty one. Here it can be any configuration at all, in particular one inside the band.
Carrier-general, given two distinct points. -/
theorem the_limit_need_not_be_empty {a b : Pt X} (hab : a ≠ b) :
    (∀ c : Pt X → Pt X → Option Bool,
        applyStance (restoreTo (oneCell a b true)) c = oneCell a b true)
      ∧ (oneCell a b true : Pt X → Pt X → Option Bool) ≠ botC (Pt X)
      ∧ Mobile (oneCell a b true : Pt X → Pt X → Option Bool) := by
  refine ⟨restoreTo_returns_from_anywhere _, ?_, mobile_iff.mpr ⟨⟨a, b, ?_⟩, ⟨a, a, ?_⟩⟩⟩
  · intro he
    have hc := congrFun (congrFun he a) b
    rw [oneCell_at] at hc
    exact Option.some_ne_none _ hc
  · rw [oneCell_at]
    exact Option.some_ne_none _
  · exact oneCell_elsewhere a b true (fun hq => hab hq.2)

/-! ### A band held with no resting place in it -/

/-- Release everything, and form at one of two named cells according to which of them is held. -/
def swapBetween (a b : Pt X) : Stance X :=
  ⟨fun _ _ _ => true,
   fun c x y => if c a b ≠ none then oneCell b a true x y else oneCell a b true x y⟩

theorem applyStance_swapBetween_of_held {a b : Pt X} {c : Pt X → Pt X → Option Bool} (h : c a b ≠ none) :
    applyStance (swapBetween a b) c = oneCell b a true := by
  funext x y
  rw [applyStance_of_dropped (T := swapBetween a b) rfl]
  simp [swapBetween, h]

theorem applyStance_swapBetween_of_open {a b : Pt X} {c : Pt X → Pt X → Option Bool} (h : c a b = none) :
    applyStance (swapBetween a b) c = oneCell a b true := by
  funext x y
  rw [applyStance_of_dropped (T := swapBetween a b) rfl]
  simp [swapBetween, h]

theorem oneCell_mobile {a b : Pt X} (hab : a ≠ b) (v : Bool) :
    Mobile (oneCell a b v : Pt X → Pt X → Option Bool) :=
  mobile_iff.mpr ⟨⟨a, b, by rw [oneCell_at]; exact Option.some_ne_none _⟩,
    ⟨a, a, oneCell_elsewhere a b v (fun hq => hab hq.2)⟩⟩

/-- **THERE IS A TWO-STEP CYCLE.** The stance moves between two configurations and back, so the enlarged space
has orbits. Carrier-general, given two distinct points. -/
theorem there_is_a_cycle {a b : Pt X} (hab : a ≠ b) :
    applyStance (swapBetween a b) (oneCell a b true) = oneCell b a true
      ∧ applyStance (swapBetween a b) (oneCell b a true) = oneCell a b true := by
  refine ⟨applyStance_swapBetween_of_held ?_, applyStance_swapBetween_of_open ?_⟩
  · rw [oneCell_at]
    exact Option.some_ne_none _
  · exact oneCell_elsewhere b a true (fun hq => hab hq.1)

/-- **AND A RELEASING-ONLY STANCE HAS NO SUCH CYCLE.** Two applications returning to where they started means
nothing moved at all, since the order runs one way only. So orbits are new. Carrier-general. -/
theorem releasing_only_has_no_cycle {T : Stance X} (h : FormsNothing T)
    {c : Pt X → Pt X → Option Bool} (hc : applyStance T (applyStance T c) = c) : applyStance T c = c := by
  funext x y
  rcases formsNothing_deflationary h c x y with h1 | h1
  · have h2 := formsNothing_deflationary h (applyStance T c) x y
    rw [hc] at h2
    rcases h2 with h2 | h2
    · rw [h1, h2]
    · exact h2.symm
  · exact h1

/-- **SO A BAND CAN BE HELD WITH NO RESTING PLACE INSIDE IT.** Two mobile configurations, each carried to the
other, neither of them fixed, and nothing outside the pair is ever reached from within it. On the releasing-only
arm an invariant set of non-empty configurations always contained a fixed one; here it need not.
Carrier-general, given two distinct points. -/
theorem an_invariant_band_without_a_resting_place {a b : Pt X} (hab : a ≠ b) :
    (∀ c : Pt X → Pt X → Option Bool,
        (c = oneCell a b true ∨ c = oneCell b a true) →
          (applyStance (swapBetween a b) c = oneCell a b true
            ∨ applyStance (swapBetween a b) c = oneCell b a true))
      ∧ Mobile (oneCell a b true : Pt X → Pt X → Option Bool)
      ∧ Mobile (oneCell b a true : Pt X → Pt X → Option Bool)
      ∧ applyStance (swapBetween a b) (oneCell a b true) ≠ oneCell a b true
      ∧ applyStance (swapBetween a b) (oneCell b a true) ≠ oneCell b a true := by
  obtain ⟨h1, h2⟩ := there_is_a_cycle hab
  have hne : (oneCell a b true : Pt X → Pt X → Option Bool) ≠ oneCell b a true := by
    intro he
    have hc := congrFun (congrFun he a) b
    rw [oneCell_at, oneCell_elsewhere b a true (fun hq => hab hq.1)] at hc
    exact Option.some_ne_none _ hc
  refine ⟨?_, oneCell_mobile hab true, oneCell_mobile (Ne.symm hab) true, ?_, ?_⟩
  · rintro c (rfl | rfl)
    · exact Or.inr h1
    · exact Or.inl h2
  · rw [h1]
    exact fun he => hne he.symm
  · rw [h2]
    exact hne

end Band

/-! ## Part 3: returning to a supported position, and the second extreme -/

section Return

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

theorem punctured_mobile {a b : Pt X} (hab : a ≠ b) :
    Mobile (punctured a b : Pt X → Pt X → Option Bool) :=
  mobile_iff.mpr ⟨⟨a, a, by
      rw [punctured_elsewhere a b (fun hq => hab (hq.1.symm.trans hq.2))]
      exact Option.some_ne_none _⟩,
    ⟨a, b, punctured_hole a b⟩⟩

/-- **AN ARBITRARY DEPARTURE IS RETURNED TO A CONFIGURATION THAT IS MOBILE, HOLDS NEARLY EVERYTHING, AND HOLDS
EVERY PAIR OF ITS DISTINCT ROWS APART BY PRESENT VALUES.** From any configuration whatever, in one application.
Carrier-general, given two distinct points. -/
theorem the_return_is_to_a_supported_position {a b : Pt X} (hab : a ≠ b) :
    (∀ c : Pt X → Pt X → Option Bool, applyStance (restoreTo (punctured a b)) c = punctured a b)
      ∧ Mobile (punctured a b : Pt X → Pt X → Option Bool)
      ∧ (∀ x x' : Pt X, x ≠ x' → presentCarried (punctured a b) x x') :=
  ⟨restoreTo_returns_from_anywhere _, punctured_mobile hab,
   fun _ _ hxx => punctured_is_supported hab hxx⟩

/-- **AND THE RETURN IS BY ACTION IN BOTH DIRECTIONS, NOT BY DESCENT.** From a departure that holds a cell the
target leaves open, the stance releases; from one that leaves open a cell the target holds, it forms. Neither
alone would do. Carrier-general, given two distinct points. -/
theorem the_return_uses_both_directions {a b : Pt X} (hab : a ≠ b) :
    (restoreTo (punctured a b)).drop (fun _ _ => some true) a b = true
      ∧ (restoreTo (punctured a b)).form (botC (Pt X)) a a = some true
      ∧ applyStance (restoreTo (punctured a b)) (botC (Pt X)) a a = some true := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [restoreTo, decide_eq_true_eq, punctured_hole]
    exact Option.some_ne_none _
  · simp only [restoreTo]
    rw [punctured_elsewhere a b (fun hq => hab (hq.1.symm.trans hq.2))]
    simp
  · rw [restoreTo_returns_from_anywhere,
      punctured_elsewhere a b (fun hq => hab (hq.1.symm.trans hq.2))]
    simp

/-! ### The two extremes at the ends of the band -/

/-- **THE TWO EXTREMES LEAVE THE BAND AT OPPOSITE ENDS, AND NEITHER IS THE INERT STANCE.** Releasing everything
lands where nothing is held. Forming everywhere lands where nothing is open. Both are outside the band, they are
not the same stance, and the stance that keeps whatever it is handed is a third thing which leaves a mobile
configuration mobile. Carrier-general, given two distinct points. -/
theorem the_two_extremes_are_distinct_failures {a b : Pt X} (hab : a ≠ b) :
    ¬ Mobile (applyStance (dropAll : Stance X) (oneCell a b true))
      ∧ ¬ Mobile (applyStance (formAll : Stance X) (oneCell a b true))
      ∧ applyStance (dropAll : Stance X) (oneCell a b true)
          ≠ applyStance (formAll : Stance X) (oneCell a b true)
      ∧ Mobile (applyStance (holdAll : Stance X) (oneCell a b true)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [applyStance_dropAll]
    exact (the_band_has_two_exits _).mpr (Or.inl rfl)
  · exact (the_band_has_two_exits _).mpr (Or.inr (formAll_saturates _))
  · intro he
    have hc := congrFun (congrFun he a) a
    rw [applyStance_dropAll] at hc
    rw [applyStance_formAll, if_pos (oneCell_elsewhere a b true (fun hq => hab hq.2))] at hc
    exact Option.some_ne_none _ hc.symm
  · rw [applyStance_holdAll]
    exact oneCell_mobile hab true

/-- **AND THE FORMING EXTREME IS STABLE WHERE IT LANDS.** It reaches a configuration with nothing open and keeps
it, so it is a failure mode of its own and not a passage to anything. Carrier-general. -/
theorem the_forming_extreme_settles (c : Pt X → Pt X → Option Bool) :
    isTotal (applyStance (formAll : Stance X) c)
      ∧ applyStance (formAll : Stance X) (applyStance (formAll : Stance X) c) = applyStance (formAll : Stance X) c :=
  ⟨formAll_saturates c, formAll_fixes_the_saturated (formAll_saturates c)⟩

/-- **THE THREE FAILURE MODES AND THE ONE MAINTAINED BAND, TOGETHER.** Releasing everything ends where nothing is
held. Forming everywhere ends where nothing is open. Keeping everything ends wherever it was left, restoring
nothing. And the restoring stance returns to a mobile configuration from anywhere. Carrier-general, given two
distinct points. -/
theorem the_picture {a b : Pt X} (hab : a ≠ b) :
    (∀ c : Pt X → Pt X → Option Bool, applyStance (dropAll : Stance X) c = botC (Pt X))
      ∧ (∀ c : Pt X → Pt X → Option Bool, isTotal (applyStance (formAll : Stance X) c))
      ∧ (∀ c : Pt X → Pt X → Option Bool, applyStance (holdAll : Stance X) c = c)
      ∧ (∀ c : Pt X → Pt X → Option Bool,
          applyStance (restoreTo (punctured a b)) c = punctured a b)
      ∧ Mobile (punctured a b : Pt X → Pt X → Option Bool) :=
  ⟨applyStance_dropAll, formAll_saturates, applyStance_holdAll, restoreTo_returns_from_anywhere _,
   punctured_mobile hab⟩

end Return

/-! ## Part 4: the other order

Everything above releases first and forms second within one application. The reverse is unbuilt until now:
form first, into whatever is open in the configuration handed to the application, then release, using the same
two rules read off that same configuration. Both orders read the same input; only the order of writing changes.
-/

section Reverse

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

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

theorem actRev_of_dropped {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : T.drop c x y = true) : applyStanceRev T c x y = none := by simp [applyStanceRev, partialization, h]

theorem actRev_of_kept {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : T.drop c x y = false) : applyStanceRev T c x y = formStep T c x y := by
  simp [applyStanceRev, partialization, h]

/-- **THE REVERSE ORDER CANNOT REASSIGN A CELL IT KEEPS HELD.** Forming has already had its one chance, before
the cell's own content was visible to it as open, so a held cell can only survive unchanged or be emptied in
one application, never carried to a different held value. Carrier-general. -/
theorem actRev_cannot_reassign_a_held_cell {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (hv : c x y ≠ none) : applyStanceRev T c x y = c x y ∨ applyStanceRev T c x y = none := by
  by_cases hd : T.drop c x y = true
  · exact Or.inr (actRev_of_dropped hd)
  · rw [Bool.not_eq_true] at hd
    rw [actRev_of_kept hd, formStep_of_held hv]
    exact Or.inl rfl

/-! ### A stance that releases and forms the same cell -/

/-- Release a named cell and form true there, whatever the configuration. -/
def coincident (a b : Pt X) : Stance X :=
  ⟨fun _ x y => decide (x = a ∧ y = b), fun _ x y => if x = a ∧ y = b then some true else none⟩

theorem applyStance_coincident_always_commits (a b : Pt X) (c : Pt X → Pt X → Option Bool) :
    applyStance (coincident a b) c a b = some true := by
  rw [applyStance_of_dropped (T := coincident a b) (by simp [coincident])]
  simp [coincident]

theorem actRev_coincident_never_commits (a b : Pt X) (c : Pt X → Pt X → Option Bool) :
    applyStanceRev (coincident a b) c a b = none :=
  actRev_of_dropped (T := coincident a b) (by simp [coincident])

/-- **THE TWO ORDERS DIFFER, AT EVERY CONFIGURATION.** Release-then-form always commits there. Form-then-release
never does. Not a witness at one configuration: the whole family of configurations parts the two orders at this
cell. Carrier-general. -/
theorem the_orders_differ (a b : Pt X) (c : Pt X → Pt X → Option Bool) :
    applyStance (coincident a b) c a b ≠ applyStanceRev (coincident a b) c a b := by
  rw [applyStance_coincident_always_commits, actRev_coincident_never_commits]
  exact Option.some_ne_none _

/-- **AND THE REVERSE ORDER ADMITS A STEP THAT DOES NOTHING AT ALL.** Wherever the cell starts open, forming
writes into it and releasing immediately takes the write back, so the whole application is the identity there
and everywhere else. Release-then-form cannot do this: wherever it would release an open cell it forms into the
same opening in the same step. Carrier-general, given a cell starting open. -/
theorem the_reverse_admits_a_null_step (a b : Pt X) {c : Pt X → Pt X → Option Bool} (h : c a b = none) :
    applyStanceRev (coincident a b) c = c := by
  funext x y
  by_cases hxy : x = a ∧ y = b
  · obtain ⟨rfl, rfl⟩ := hxy
    rw [actRev_coincident_never_commits]
    exact h.symm
  · have hd : (coincident a b : Stance X).drop c x y = false := by
      simp only [coincident, decide_eq_false_iff_not]
      exact hxy
    rw [actRev_of_kept hd]
    by_cases hv : c x y = none
    · rw [formStep_of_open hv]
      have hf : (coincident a b : Stance X).form c x y = none := by simp [coincident, hxy]
      rw [hf, hv]
    · rw [formStep_of_held hv]

/-- **SO RELEASE-THEN-FORM CAN REASSIGN A HELD CELL, AND FORM-THEN-RELEASE CANNOT.** The same stance, applied to
a configuration already holding the opposite value at the named cell, is carried to the new value under one
order and only ever reaches the old value or emptiness under the other. Carrier-general, given two distinct
points. -/
theorem applyStance_can_reassign_where_reverse_cannot (a b : Pt X) :
    applyStance (coincident a b) (oneCell a b false) a b = some true
      ∧ applyStanceRev (coincident a b) (oneCell a b false) a b ≠ some true := by
  have hv : (oneCell a b false : Pt X → Pt X → Option Bool) a b ≠ none := by
    rw [oneCell_at]; exact Option.some_ne_none _
  refine ⟨applyStance_coincident_always_commits a b _, fun he => ?_⟩
  rcases actRev_cannot_reassign_a_held_cell (T := coincident a b) hv with h | h
  · rw [h, oneCell_at] at he; exact absurd he (by simp)
  · rw [h] at he; exact absurd he (by simp)

/-! ### The band under the reverse order: one construction collapses, another does not -/

/-- **THE ORBIT-MAKING STANCE COLLAPSES UNDER THE REVERSE ORDER.** The construction that gave a two-step cycle
released everything, relying on forming to run afterward and refill the swap target. Run in reverse, the same
blanket release has the last word and wipes out whatever was just formed, everywhere, from every configuration.
Carrier-general. -/
theorem actRev_swapBetween_collapses (a b : Pt X) (c : Pt X → Pt X → Option Bool) :
    applyStanceRev (swapBetween a b) c = botC (Pt X) := by
  funext x y
  exact actRev_of_dropped (T := swapBetween a b) rfl

/-- Release only whichever of the two named cells is currently held, and form the swap target: tuned so the
release does not undo what forming just built. -/
def swapRev (a b : Pt X) : Stance X :=
  ⟨fun c x y => decide ((x = a ∧ y = b ∧ c a b ≠ none) ∨ (x = b ∧ y = a ∧ c b a ≠ none)),
   fun c x y => if c a b ≠ none then oneCell b a true x y else oneCell a b true x y⟩

theorem actRev_swapRev_of_ab {a b : Pt X} (hab : a ≠ b) :
    applyStanceRev (swapRev a b) (oneCell a b true) = oneCell b a true := by
  have hab_at : (oneCell a b true : Pt X → Pt X → Option Bool) a b = some true := oneCell_at a b true
  have hba : (oneCell a b true : Pt X → Pt X → Option Bool) b a = none :=
    oneCell_elsewhere a b true (fun hq => hab hq.1.symm)
  funext x y
  by_cases hxy : x = a ∧ y = b
  · rw [hxy.1, hxy.2]
    have hd : (swapRev a b : Stance X).drop (oneCell a b true) a b = true := by
      have hne : (oneCell a b true : Pt X → Pt X → Option Bool) a b ≠ none := by
        rw [hab_at]; exact Option.some_ne_none _
      simp [swapRev, hne]
    rw [actRev_of_dropped hd]
    exact (oneCell_elsewhere b a true (fun hq => hab hq.1)).symm
  · by_cases hyx : x = b ∧ y = a
    · rw [hyx.1, hyx.2]
      have hd : (swapRev a b : Stance X).drop (oneCell a b true) b a = false := by
        simp only [swapRev, decide_eq_false_iff_not]
        rintro (⟨h1, -, -⟩ | ⟨-, -, h3⟩)
        · exact hab h1.symm
        · exact h3 hba
      rw [actRev_of_kept hd, formStep_of_open hba]
      simp only [swapRev]
      rw [if_pos (show (oneCell a b true : Pt X → Pt X → Option Bool) a b ≠ none by
        rw [hab_at]; exact Option.some_ne_none _)]
    · have hc : (oneCell a b true : Pt X → Pt X → Option Bool) x y = none :=
        oneCell_elsewhere a b true hxy
      have hd : (swapRev a b : Stance X).drop (oneCell a b true) x y = false := by
        simp only [swapRev, decide_eq_false_iff_not]
        rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩)
        · exact hxy ⟨h1, h2⟩
        · exact hyx ⟨h1, h2⟩
      rw [actRev_of_kept hd, formStep_of_open hc]
      simp only [swapRev]
      rw [if_pos (show (oneCell a b true : Pt X → Pt X → Option Bool) a b ≠ none by
        rw [hab_at]; exact Option.some_ne_none _)]

theorem actRev_swapRev_of_ba {a b : Pt X} (hab : a ≠ b) :
    applyStanceRev (swapRev a b) (oneCell b a true) = oneCell a b true := by
  have hba_at : (oneCell b a true : Pt X → Pt X → Option Bool) b a = some true := oneCell_at b a true
  have hab' : (oneCell b a true : Pt X → Pt X → Option Bool) a b = none :=
    oneCell_elsewhere b a true (fun hq => hab hq.1)
  funext x y
  by_cases hyx : x = b ∧ y = a
  · rw [hyx.1, hyx.2]
    have hd : (swapRev a b : Stance X).drop (oneCell b a true) b a = true := by
      have hne : (oneCell b a true : Pt X → Pt X → Option Bool) b a ≠ none := by
        rw [hba_at]; exact Option.some_ne_none _
      simp [swapRev, hne]
    rw [actRev_of_dropped hd]
    exact (oneCell_elsewhere a b true (fun hq => hab hq.2)).symm
  · by_cases hxy : x = a ∧ y = b
    · rw [hxy.1, hxy.2]
      have hd : (swapRev a b : Stance X).drop (oneCell b a true) a b = false := by
        simp only [swapRev, decide_eq_false_iff_not]
        rintro (⟨-, -, h3⟩ | ⟨h1, -, -⟩)
        · exact h3 hab'
        · exact hab h1
      rw [actRev_of_kept hd, formStep_of_open hab']
      simp only [swapRev]
      rw [if_neg (show ¬ (oneCell b a true : Pt X → Pt X → Option Bool) a b ≠ none by
        rw [hab']; simp)]
    · have hc : (oneCell b a true : Pt X → Pt X → Option Bool) x y = none :=
        oneCell_elsewhere b a true hyx
      have hd : (swapRev a b : Stance X).drop (oneCell b a true) x y = false := by
        simp only [swapRev, decide_eq_false_iff_not]
        rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩)
        · exact hxy ⟨h1, h2⟩
        · exact hyx ⟨h1, h2⟩
      rw [actRev_of_kept hd, formStep_of_open hc]
      simp only [swapRev]
      rw [if_neg (show ¬ (oneCell b a true : Pt X → Pt X → Option Bool) a b ≠ none by
        rw [hab']; simp)]

/-- **AND A RETUNED CONSTRUCTION HAS THE SAME TWO-STEP CYCLE UNDER THE REVERSE ORDER.** So orbits are not a
casualty of the order itself. What fails to carry over is a rule that releases indiscriminately; a rule that
releases only what it is about to leave behind survives the reversal intact. Carrier-general, given two
distinct points. -/
theorem there_is_a_reverse_cycle {a b : Pt X} (hab : a ≠ b) :
    applyStanceRev (swapRev a b) (oneCell a b true) = oneCell b a true
      ∧ applyStanceRev (swapRev a b) (oneCell b a true) = oneCell a b true :=
  ⟨actRev_swapRev_of_ab hab, actRev_swapRev_of_ba hab⟩

/-! ### Restoration under the reverse order: still universal, but not always in one step -/

/-- Release a held cell that disagrees with the target; never release an open one. -/
def restoreToRev (t : Pt X → Pt X → Option Bool) : Stance X :=
  ⟨fun c x y => decide (c x y ≠ t x y ∧ c x y ≠ none), fun _ x y => t x y⟩

/-- **ONE APPLICATION EITHER REACHES THE TARGET AT A CELL, OR EMPTIES A CELL THAT WAS HELD AND WRONG.** The
exact case analysis, from which everything else in this part follows. Carrier-general. -/
theorem restoreToRev_apply (t c : Pt X → Pt X → Option Bool) (x y : Pt X) :
    applyStanceRev (restoreToRev t) c x y = t x y
      ∨ (c x y ≠ none ∧ c x y ≠ t x y ∧ applyStanceRev (restoreToRev t) c x y = none) := by
  by_cases h1 : c x y = none
  · left
    have hd : (restoreToRev t : Stance X).drop c x y = false := by simp [restoreToRev, h1]
    rw [actRev_of_kept hd, formStep_of_open h1]
    rfl
  · by_cases h2 : c x y = t x y
    · left
      have hd : (restoreToRev t : Stance X).drop c x y = false := by simp [restoreToRev, h2]
      rw [actRev_of_kept hd, formStep_of_held h1, h2]
    · right
      refine ⟨h1, h2, ?_⟩
      have hd : (restoreToRev t : Stance X).drop c x y = true := by simp [restoreToRev, h1, h2]
      exact actRev_of_dropped hd

/-- **THE FIRST APPLICATION CAN MISS THE TARGET AT A CELL ALREADY HELD TO THE WRONG VALUE.** Carrier-general,
given two distinct points. -/
theorem restoreToRev_one_step_can_fail {a b : Pt X} :
    applyStanceRev (restoreToRev (oneCell a b true)) (oneCell a b false) ≠ oneCell a b true := by
  intro he
  have hc := congrFun (congrFun he a) b
  have hd : (restoreToRev (oneCell a b true) : Stance X).drop (oneCell a b false) a b = true := by
    simp only [restoreToRev, decide_eq_true_eq, oneCell_at]
    exact ⟨by simp, Option.some_ne_none _⟩
  rw [actRev_of_dropped hd, oneCell_at] at hc
  exact absurd hc (by simp)

/-- **BUT THE SECOND APPLICATION ALWAYS REACHES THE TARGET.** Whatever the first application leaves, either it
already matches the target, or the cell was emptied by the first application, and an empty cell is filled in one
more step. So restoration is universal under the reverse order too, at a cost of one extra step exactly where
the first order needed none. Carrier-general. -/
theorem restoreToRev_second_application_reaches_target (t c : Pt X → Pt X → Option Bool) :
    applyStanceRev (restoreToRev t) (applyStanceRev (restoreToRev t) c) = t := by
  funext x y
  rcases restoreToRev_apply t (applyStanceRev (restoreToRev t) c) x y with h2 | ⟨h2ne, h2neq, -⟩
  · exact h2
  · exfalso
    rcases restoreToRev_apply t c x y with h1 | ⟨-, -, h1none⟩
    · exact h2neq h1
    · exact h2ne h1none

end Reverse

/-! ## THE VERDICTS

Read in the registers first, as the brief asks. The theorem content is neutral and the register statements
below are readings, defeasible and provisional.

PART 1: A STANCE THAT SHEDS AND FORMS, AND THE THIRD EXTREME.

A stance is now two things at once: what it lets go of, and what it takes up. One application lets go first and
then takes up into whatever is open. `the_deflationary_stances_embed` shows the earlier space sits inside this one
as the stances that never take anything up, and `formsNothing_deflationary` shows those and only those run downhill.

The first finding is about what could not be said before. `formAll_is_new`: the stance that takes up everywhere
lands where every releasing-only stance stays put, so the enlarged space is strictly larger, and the thing it
adds is AN EXTREME AT THE OPPOSITE END. `formAll_saturates` and `formAll_fixes_the_saturated`: it reaches a
position with nothing left open, in one application from anywhere, and stays. `the_three_extremes_differ`
separates it from releasing everything and from keeping everything.

  COGNITION. There are now three ways to be, not two. Give everything up. Keep whatever you have. And SETTLE
  EVERYTHING: leave no question open. The third was unsayable while the only available applyStance was letting go, and
  it is the one a mind that insists on completeness performs.

  IMMUNOLOGY. Clearing and repairing are different acts and a system that only clears cannot be described as
  doing the second. The third extreme is the one that fills every space it finds.

  POLITICS. Repealing and legislating are different acts. An arrangement that can only repeal cannot be
  described as building anything, and the arrangement that legislates on every matter whatever is a distinct
  extreme from the one that never amends.

FORMING CANNOT OVERWRITE. `forming_is_powerless_at_a_held_cell` and `a_change_requires_a_release`: whatever a
stance would take up at a cell it keeps, that cell holds what it held; and if a cell holds something different
afterwards, the stance released it. This is not an assumption added for effect, it is what a commit does in the
kernel, which writes only into absence.

  COGNITION. NO BELIEF IS REPLACED WITHOUT FIRST BEING GIVEN UP. One cannot form over a standing commitment;
  the standing one has to go first, and only then does what one forms take hold. Renewal requires release, and
  that is a structural fact about the acts available, not a counsel about how to hold things well.

  POLITICS. There is no amendment that is not a repeal followed by an enactment. What is on the books cannot be
  written over.

PART 2: THE BAND, AND HOLDING IT.

`the_band_has_two_exits` is the geography, and it is exact: a position fails to have both directions available
precisely when nothing is held or nothing is open. Two ends, and the band is between them.
`the_second_exit_is_out_of_reach` says what the earlier arm could see: a stance that only releases can never
leave the band at the forming end, since what it opens stays open. THE SECOND EXIT WAS STRUCTURALLY INVISIBLE
THERE.

`restoreTo_returns_from_anywhere` is the maintenance result and it is as strong as it could be. The stance that
releases whatever disagrees with a named position and forms that position into the openings ARRIVES AT IT FROM
EVERY POSITION WHATEVER, in one application. `the_limit_need_not_be_empty` draws the contrast with the earlier
arm, where the one place reached from everywhere HAD to be the empty one: here it can be any position at all,
and in particular one inside the band.

`an_invariant_band_without_a_resting_place` is the finding of this part and it refutes the earlier collapse.
Two mobile positions, each carried to the other, NEITHER OF THEM FIXED, and nothing outside the pair reached
from within it. On the releasing-only arm an invariant set of non-empty positions always contained a fixed one,
which is why resting there could only mean stopping. Here a band can be held with no resting place inside it.
`releasing_only_has_no_cycle` confirms the difference is real and not an artefact of the example: two
applications returning to where they started means nothing moved at all, when the only applyStance is letting go. SO
ORBITS ARE NEW.

  COGNITION. There is now a difference between a mind that has stopped and a mind that is being kept. The first
  arrives somewhere and does nothing further. The second is doing something at every moment, and it is not
  doing the same thing twice; what is steady is the CONDITION, not the contents. A view can be alive in the
  sense that it is continuously being let go of and re-formed while remaining mobile and supported throughout,
  and this is provably not the same shape as coming to rest.

  IMMUNOLOGY. Homeostasis in the proper sense is now expressible: a band held by continued action in both
  directions, with no single state the system sits in. The earlier picture could only offer a stopping point.

  POLITICS. An arrangement can be kept revisable by continuous action rather than by arriving at a good
  settlement and halting. What is preserved is that there is always something held and always something open,
  not any particular provision.

PART 3: RETURNING TO A BODY OF HOLDINGS, AND THE SECOND FAILURE.

`the_return_is_to_a_supported_position` is the strongest form of the repair result. From ANY position whatever, in
one application, the restoring stance returns to a position that is mobile, holds nearly every cell, and holds
every pair of its distinct rows apart BY PRESENT VALUES rather than by what has not been said. So the place
returned to is not blank and is not held up by absences.

`the_return_uses_both_directions` shows the return is not descent. Faced with a position holding what the target
leaves open, the stance releases; faced with one leaving open what the target holds, it forms. Removing either
direction breaks it.

  COGNITION. Health can now be said to REPAIR rather than merely to halt. The earlier arm could say only that
  letting go has somewhere it comes back to, and that somewhere was blankness. Here what is returned to after
  damage is a nearly complete body of commitments, every part of it held apart from its rivals by something
  actually present, and still mobile. That is healing rather than bleeding out.

  IMMUNOLOGY. Clearing alone returns a system to nothing. Clearing together with repair returns it to a
  maintained condition, and the theorem is that the second requires both directions and cannot be had from
  either alone.

`the_two_extremes_are_distinct_failures` is the second finding. The two exits from the band are reached by two
DIFFERENT stances, and both are failures: releasing everything ends where nothing is held, forming everywhere
ends where nothing is open. They are not the same stance, and the stance that keeps whatever it is handed is a
third thing which leaves a mobile position mobile. `the_forming_extreme_settles` adds that the forming extreme
is stable where it lands, so it is a failure mode in its own right and not a passage to anything.

  COGNITION. There are TWO ways to kill a living view, not one, and the earlier arm could only express one of
  them. The first is to refuse to give anything up, which keeps whatever it was handed including the damage.
  The second is to insist on settling everything, which leaves nothing open and is perfectly stable there. The
  dogmatist and the totalizer are different stances with different failures, and both leave the band that has
  both directions available.

  IMMUNOLOGY. The first failure is not clearing what should be cleared. The second is filling every space,
  which is what the theorem describes and what the register would have to name; the framework says only that it
  is a distinct and stable end position with nothing left open.

  POLITICS. Never amending and legislating on everything are two distinct deaths, and the second is not a
  degree of the first. One keeps whatever it was left with. The other closes every question and holds.

PART 4: THE OTHER ORDER, AND WHETHER MAINTENANCE SURVIVES THE REVERSAL.

Everything above releases first and forms second. This part builds the mirror, form-then-release, reading the
same two rules off the same input configuration, and asks whether it is the same dynamics wearing a different
name, or a different thing.

`the_orders_differ` is not a witness at one configuration: for the stance that releases and forms the SAME
named cell, release-then-form commits there at EVERY configuration whatever, and form-then-release never does,
at any configuration. The two orders are not two routes to the same place.

  COGNITION. Clearing then rebuilding and rebuilding then clearing are not the same applyStance performed in a
  different sequence. Applied to the same belief, one always lands it and the other never does.

  IMMUNOLOGY. Clear-then-repair and repair-then-clear are not interchangeable descriptions of one process; run
  on the same site, they reach opposite outcomes, every time.

`the_reverse_admits_a_null_step` is the sharper form of the same fact. Wherever the named cell starts open,
form-then-release is the IDENTITY there and everywhere: it builds and then immediately discards what it built,
and the configuration is untouched. Release-then-form cannot do this; wherever it would release an open cell it
fills the very same opening in the same step, so it never merely churns.

  COGNITION. Rebuilding-then-clearing admits idle motion that clearing-then-rebuilding forbids: a belief can be
  formed and abandoned in the same breath, work that changes nothing, a possibility the other order structurally
  excludes.

  POLITICS. A regime that legislates and then repeals in the same session can pass a law that never takes
  effect. A regime that repeals and then legislates in the same session cannot; whatever it repeals, it
  immediately re-enacts something there.

`actRev_cannot_reassign_a_held_cell`, confirmed by `applyStance_can_reassign_where_reverse_cannot`, is the deeper
asymmetry and it is a capability gap, not merely a difference of outcome. Under release-then-form, a held cell
CAN be carried to a new held value in one step, since the release opens it and the form immediately refills it
in the very same application. Under form-then-release, forming has already had its one chance before the
release runs, so a held cell can only survive unchanged or be emptied; IT CAN NEVER BE REASSIGNED TO SOMETHING
ELSE IN ONE STEP.

  COGNITION. A view that clears first and rebuilds second can revise a standing commitment to a new one in a
  single applyStance of reconsideration. A view that would rebuild first and clear second cannot: any commitment it
  already holds can only be kept as is or given up, and giving up is all the second order can ever do to it in
  one step; forming a replacement is a separate, later applyStance.

  IMMUNOLOGY. Repairing before clearing cannot convert damaged tissue directly into the correct tissue in one
  pass; the pass can only leave the damage or remove it, and rebuilding the correct tissue there is a further
  pass. Clearing before repairing can do both in one.

`actRev_swapBetween_collapses` shows the cost of the gap concretely: the construction that gave a genuine
two-step cycle under the first order, RELEASE EVERYTHING and let forming refill the target, is not a weaker
version of a cycle under the reverse order; it is NO cycle at all. Run in reverse, the same blanket release runs
after forming and wipes out everything it just built, from every configuration, collapsing to the always-empty
stance.

  IMMUNOLOGY. A regimen of aggressive, indiscriminate clearing followed by targeted repair can maintain a
  steady state. The same regimen with the order swapped, targeted repair followed by aggressive, indiscriminate
  clearing, maintains nothing: the clearing step, unchanged, erases the repair every time. THE SAME GESTURE THAT
  WAS SAFE BEFORE BUILDING IS CATASTROPHIC AFTER IT.

  POLITICS. Broad repeal followed by precise legislation can keep an arrangement live and revisable. Precise
  legislation followed by the SAME broad repeal keeps nothing: whatever was just enacted is swept away by the
  repeal that follows it, every round.

`there_is_a_reverse_cycle` is the correction to a hasty reading of that collapse. Orbits are not a casualty of
the reversal ITSELF; `swapRev`, tuned to release only whichever of the two cells is currently held rather than
releasing everything, reproduces the identical two-step cycle under the reverse order. WHAT FAILED WAS A
PARTICULAR RECIPE, NOT MAINTENANCE UNDER THE REVERSAL.

  COGNITION. Homeostasis is available under either order. What must change when the order changes is not
  whether one can stay mobile-and-supported, but HOW PRECISELY THE CLEARING HAS TO BE AIMED: a mind that forms
  first must let go only of exactly what it is about to replace, where a mind that lets go first could afford to
  clear more broadly and trust the forming step to refill what mattered.

`restoreToRev_apply`, `restoreToRev_second_application_reaches_target` and `restoreToRev_one_step_can_fail` give
the general repair picture and it is a genuine positive result, at a measured cost. Restoration to an arbitrary
target from an arbitrary departure is UNIVERSAL under the reverse order too: two applications always suffice.
But one does not always suffice, exactly where a held cell must be carried to a different held value; there the
first application can only open it, and the second fills it.

  COGNITION. Repairing-before-clearing still gets a mind all the way back to a supported view from anywhere.
  What it costs is TEMPO: reconsidering a standing belief takes one extra beat under this order, an applyStance of
  noticing-and-releasing before the applyStance of replacing, where clearing-first does both at once.

  IMMUNOLOGY. A repair-first regimen still reaches a fully healed state from any injury, but healing a
  MISDIRECTED repair (tissue rebuilt in the wrong place) costs one extra cycle: the wrong repair must first be
  cleared, then the right one built, where a clear-first regimen would have gotten it right immediately.

  POLITICS. A legislate-first regime can still reach any target arrangement from any starting one, but
  overturning a standing provision to something new costs an extra legislative round: repeal, then enact, where
  repeal-first regimes can do both in the single round that follows a repeal.

PART 5: ASSEMBLED, IN THE REGISTERS.

WHAT THE FILLING ARM ADDS. Stances that let go and take up. The earlier space embeds as those that never take
up. Strictly larger, and what it adds is an extreme at the far end plus orbits.

IS THERE GENUINE MAINTENANCE. Yes. A band can be held by continued action with no resting place inside it,
which the releasing-only arm provably could not have, and a named position can be returned to from anywhere.
The steady thing can be the condition rather than the contents. This survives the reversal of order, though not
under the identical construction: a rule that releases indiscriminately must become a rule that releases
precisely.

DOES RENEWAL REQUIRE RELEASE. Yes, and structurally, under both orders. Forming cannot overwrite; a cell
changes only if the stance releases it, whichever order the application runs in. What the order decides is
WHETHER RELEASE AND FORM CAN LAND IN THE SAME STEP: release-then-form can reassign a held cell in one
application; form-then-release cannot, and needs one further application wherever it must.

CAN HEALTH REPAIR. Yes, under both orders, with a one-step cost difference exactly where a held cell must
change to a new held value.

IS THERE A SECOND FAILURE MODE. Yes, and it was structurally invisible before commitment was available at all.
The band has exactly two exits, reached by two different stances, both stable at their ends.

DOES THE ORDER OF CLEARING AND FORMING MATTER. Yes, sharply, though not by making maintenance impossible in
either direction. The two orders are never the same applyStance reordered: applied to the identical stance, they can
diverge at every configuration, and form-then-release admits an idle build-and-abandon step that
release-then-form structurally forbids. What is lost under the reversal is not the capacity to maintain, but the
capacity to reassign a held cell in a single step, and the specific recipe that maintained a cycle by releasing
everything; both losses are repairable, the first by an extra application, the second by aiming the release
precisely instead of broadly.

WHAT IS STILL OUTSIDE. Nothing here changes a stance. The stance is fixed for the whole run, under either
order, so what one is willing to do remains exogenous. Both orders are now built; a stance whose two parts are
allowed to disagree about the very same cell, rather than one part unconditionally deciding it, is not.

AXIOM PROFILE AND GRADUATION. Every result is at baseline or below. Graduation is NOT proposed: the objects are
defined here and have not been placed. Nine are flagged as substantive and carrier-general:
`forming_is_powerless_at_a_held_cell`, which is the release-before-forming constraint;
`the_band_has_two_exits`, which is the geography; `an_invariant_band_without_a_resting_place`, which is
maintenance without rest and refutes the earlier collapse; `the_return_is_to_a_supported_position`, which is
repair to a non-blank position; `the_two_extremes_are_distinct_failures`, which is the second failure mode;
`the_orders_differ` and `the_reverse_admits_a_null_step`, which separate the two orders outright;
`actRev_cannot_reassign_a_held_cell`, which is the capability gap the reversal opens; and
`restoreToRev_second_application_reaches_target`, which is universal repair under the reversal at a measured
cost.

WHAT REMAINS OPEN

1. Both orders are now built. A stance whose two parts are allowed to disagree about the same cell, with a
   further rule for which one wins, rather than one part unconditionally deciding, is not.
2. The restoring stance is given its target as a parameter and returns in one or two steps depending on the
   order. Stances that approach a band gradually, and how long the return takes when the target is not written
   into the rule, are not studied.
3. The cycle exhibited has period two under both orders. Which periods occur, and whether every finite orbit
   realized under one order has a retuned analogue under the other, is asked here only for this one witness, not
   answered in general.
4. Maintenance is shown for a named target and for a two-element band, under both orders. There is no
   characterization of which subsets of the band are invariant regions of some stance, under either order.
5. A stance is still fixed for the whole run. Nothing here takes a stance to a stance.
6. Nothing here is graduated. -/

#print axioms applyStance_dropAll
#print axioms applyStance_holdAll
#print axioms applyStance_formAll
#print axioms formAll_saturates
#print axioms formAll_fixes_the_saturated
#print axioms formAll_is_new
#print axioms the_three_extremes_differ
#print axioms heldCells_nonempty_iff
#print axioms fillableCells_nonempty_iff
#print axioms mobile_iff
#print axioms the_band_has_two_exits
#print axioms the_second_exit_is_out_of_reach
#print axioms restoreTo_returns_from_anywhere
#print axioms restoreTo_fixes_its_target
#print axioms the_limit_need_not_be_empty
#print axioms applyStance_swapBetween_of_held
#print axioms applyStance_swapBetween_of_open
#print axioms oneCell_mobile
#print axioms there_is_a_cycle
#print axioms releasing_only_has_no_cycle
#print axioms an_invariant_band_without_a_resting_place
#print axioms punctured_mobile
#print axioms the_return_is_to_a_supported_position
#print axioms the_return_uses_both_directions
#print axioms the_two_extremes_are_distinct_failures
#print axioms the_forming_extreme_settles
#print axioms the_picture
#print axioms formStep_of_open
#print axioms formStep_of_held
#print axioms actRev_of_dropped
#print axioms actRev_of_kept
#print axioms actRev_cannot_reassign_a_held_cell
#print axioms applyStance_coincident_always_commits
#print axioms actRev_coincident_never_commits
#print axioms the_orders_differ
#print axioms the_reverse_admits_a_null_step
#print axioms applyStance_can_reassign_where_reverse_cannot
#print axioms actRev_swapBetween_collapses
#print axioms actRev_swapRev_of_ab
#print axioms actRev_swapRev_of_ba
#print axioms there_is_a_reverse_cycle
#print axioms restoreToRev_apply
#print axioms restoreToRev_one_step_can_fail
#print axioms restoreToRev_second_application_reaches_target

end Chiralogy.MaintenanceStance
