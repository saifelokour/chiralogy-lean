import Chiralogy.Model.Stance
import Chiralogy.Model.Apophatic

/-! # The content-reading stances

`Model/Stance` carries the rules that read only WHERE a classification holds things. This module adds the ones
that read WHAT it holds, which needs the apophatic present-support notion of `Model/Apophatic`
(`presentCarried`): a separation is supported when the two rows are held apart by values that are actually
present, rather than by what has not been said.

The layering is not a convenience. Measured against the dependency graph, the content half is a strict
extension of the openness half: every content result also uses the moves and the order, and NO result uses
present-support without them. So this module sits ON `Model/Stance`, not beside it.

The two headline facts. `keepSupported_reads_content` exhibits two classifications holding exactly the same
cells and receiving different masks, so a rule at this level ACTS on what is held and is not merely able to see
it. And `they_are_independent` shows that reading only structure and having a non-bottom fixed point are
independent properties: all four combinations occur, so what a rule reads does not determine whether it can
rest while still holding something.

Register-neutral throughout: no statement and no proof mentions any domain. -/

namespace Chiralogy

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

section Content

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

/-- Decline wherever the two rows are held apart by present values, and on the diagonal; take elsewhere. -/
noncomputable def keepSupported : Policy X :=
  fun c x y => decide (x ≠ y ∧ ¬ presentCarried c x y)

theorem keepSupported_declines {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : presentCarried c x y) : keepSupported c x y = false := by
  simp [keepSupported, h]

theorem keepSupported_takes {c : Pt X → Pt X → Option Bool} {x y : Pt X} (hxy : x ≠ y)
    (h : ¬ presentCarried c x y) : keepSupported c x y = true := by
  simp [keepSupported, hxy, h]

/-- Every pair of distinct rows of it is held apart by present values. Carrier-general. -/
theorem punctured_is_supported {a b : Pt X} (hab : a ≠ b) {x x' : Pt X} (hxx : x ≠ x') :
    presentCarried (punctured a b) x x' := by
  by_cases hp : x = a ∧ x' = b
  · obtain ⟨hxa, hxb⟩ := hp
    refine ⟨a, true, false, ?_, ?_, by simp⟩
    · rw [hxa, punctured_elsewhere a b (fun hq => hab hq.2)]; simp
    · rw [hxb, punctured_elsewhere a b (fun hq => hab hq.2)]; simp [Ne.symm hab]
  · refine ⟨x', false, true, ?_, ?_, by simp⟩
    · rw [punctured_elsewhere a b hp]; simp [hxx]
    · rw [punctured_elsewhere a b (fun hq => hab (hq.1.symm.trans hq.2))]; simp

/-! ## Two classifications holding the same cells and holding different things -/

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

/-! ## The family the recommendation picks out, and where it rests -/

/-- Every verdict a configuration holds is the same one. -/
def Uniform (c : Pt X → Pt X → Option Bool) : Prop :=
  ∀ x y x' y' : Pt X, c x y ≠ none → c x' y' ≠ none → c x y = c x' y'

/-- **UNIFORMITY BLOCKS PRESENT SUPPORT EVERYWHERE.** Carrier-general. -/
theorem uniform_blocks_present_support {c : Pt X → Pt X → Option Bool} (h : Uniform c) (x x' : Pt X) :
    ¬ presentCarried c x x' := by
  rintro ⟨y, b1, b2, h1, h2, hb⟩
  have := h x y x' y (by rw [h1]; exact Option.some_ne_none _)
    (by rw [h2]; exact Option.some_ne_none _)
  rw [h1, h2] at this
  exact hb (Option.some_inj.mp this)

/-- Take exactly where something is held off the diagonal and the two rows are not held apart by present
values. -/
noncomputable def dropUnsupported : Policy X :=
  fun c x y => decide (x ≠ y ∧ c x y ≠ none ∧ ¬ presentCarried c x y)

/-- Take everything off the diagonal exactly when the configuration commits only one verdict. -/
noncomputable def dropUniform : Policy X := fun c x y => decide (x ≠ y ∧ Uniform c)

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

/-! ## Return to a supported classification, using both directions -/

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

/-! ## Reading structure and resting are independent -/

/-- A policy that reads only where things are held: it gives the same mask at any two configurations holding
the same cells, whatever those cells hold. -/
def ReadsOnlyStructure (S : Policy X) : Prop :=
  ∀ c c' : Pt X → Pt X → Option Bool, (∀ x y : Pt X, c x y = none ↔ c' x y = none) → S c = S c'

theorem heldCells_eq_of_same_support {c c' : Pt X → Pt X → Option Bool}
    (h : ∀ x y : Pt X, c x y = none ↔ c' x y = none) : heldCells c = heldCells c' := by
  ext p
  rw [mem_heldCells, mem_heldCells]
  exact not_congr (h p.1 p.2)

theorem fillableCells_eq_of_same_support {c c' : Pt X → Pt X → Option Bool}
    (h : ∀ x y : Pt X, c x y = none ↔ c' x y = none) : fillableCells c = fillableCells c' := by
  ext p
  rw [mem_fillableCells, mem_fillableCells]
  exact h p.1 p.2

/-- Take wherever anything is held. -/
def takeIfHeld : Policy X := fun c x y => decide (c x y ≠ none)

/-- Take everywhere exactly while both moves remain available. -/
noncomputable def takeIfMobile : Policy X := fun c _ _ => decide (Mobile c)

/-- Take the cells holding one verdict, and the others only once none of the first remain. -/
noncomputable def takeTrueFirst : Policy X :=
  fun c x y => decide (c x y = some true ∨ (c x y = some false ∧ ∀ p q : Pt X, c p q ≠ some true))

theorem takeIfHeld_reads_structure : ReadsOnlyStructure (takeIfHeld : Policy X) := by
  intro c c' h
  funext x y
  simp only [takeIfHeld]
  exact decide_eq_decide.mpr (not_congr (h x y))

theorem takeIfMobile_reads_structure : ReadsOnlyStructure (takeIfMobile : Policy X) := by
  intro c c' h
  have hm : Mobile c ↔ Mobile c' := by
    simp only [Mobile, heldCells_eq_of_same_support h, fillableCells_eq_of_same_support h]
  funext x y
  simp only [takeIfMobile]
  exact decide_eq_decide.mpr hm

/-- Two cells of one column, with named verdicts. -/
def colCell (a b : Pt X) (v w : Bool) : Pt X → Pt X → Option Bool :=
  fun x y => if y = a then (if x = a then some v else if x = b then some w else none) else none

theorem colCell_at_a (a b : Pt X) (v w : Bool) : colCell a b v w a a = some v := by
  simp [colCell]

theorem colCell_at_b {a b : Pt X} (hba : b ≠ a) (v w : Bool) : colCell a b v w b a = some w := by
  simp [colCell, hba]

theorem colCell_off_column (a b : Pt X) (v w : Bool) {x y : Pt X} (h : y ≠ a) :
    colCell a b v w x y = none := by simp [colCell, h]

theorem colCell_other_row {a b : Pt X} (v w : Bool) {x : Pt X} (hxa : x ≠ a) (hxb : x ≠ b)
    (y : Pt X) : colCell a b v w x y = none := by
  by_cases hy : y = a
  · simp [colCell, hy, hxa, hxb]
  · simp [colCell, hy]

/-- The verdicts do not change which cells are held. Carrier-general. -/
theorem colCell_same_support (a b : Pt X) (v w v' w' : Bool) (x y : Pt X) :
    colCell a b v w x y = none ↔ colCell a b v' w' x y = none := by
  by_cases hy : y = a
  · by_cases hx : x = a
    · simp [colCell, hx, hy]
    · by_cases hx' : x = b
      · by_cases hba : b = a
        · simp [colCell, hx', hy, hba]
        · simp [colCell, hx', hy, hba]
      · simp [colCell, hx, hx', hy]
  · simp [colCell, hy]

theorem colCell_supported {a b : Pt X} (hba : b ≠ a) :
    presentCarried (colCell a b true false) a b :=
  ⟨a, true, false, colCell_at_a a b true false, colCell_at_b hba true false, by simp⟩

theorem colCell_unsupported {a b : Pt X} (hba : b ≠ a) :
    ¬ presentCarried (colCell a b true true) a b := by
  rintro ⟨y, b1, b2, h1, h2, hne⟩
  by_cases hy : y = a
  · subst hy
    rw [colCell_at_a] at h1
    rw [colCell_at_b hba] at h2
    exact hne ((Option.some_inj.mp h1).symm.trans (Option.some_inj.mp h2))
  · rw [colCell_off_column a b true true hy] at h1
    exact Option.some_ne_none _ h1.symm

/-- **AND THE SECOND CONTENT READER IS NOT ONE EITHER, WITH THE DIFFERENCE AT A CELL IT HOLDS.** Its mask at a
held cell depends on what is held elsewhere, so the content it reads is content that bears on what it does.
Carrier-general, given two distinct points. -/
theorem colCell_false_has_no_true (a b : Pt X) (p q : Pt X) :
    colCell a b false false p q ≠ some true := by
  by_cases hq : q = a
  · by_cases hp : p = a
    · rw [hp, hq, colCell_at_a]; simp
    · by_cases hp' : p = b
      · have hba : b ≠ a := fun hh => hp (hp'.trans hh)
        rw [hp', hq, colCell_at_b hba]; simp
      · rw [colCell_other_row false false hp hp' q]; simp
  · rw [colCell_off_column a b false false hq]; simp

/-- **A CONTENT READER IS NOT A STRUCTURE READER.** Two configurations holding exactly the same cells receive
different masks, because one holds its two cells in agreement and the other does not. Carrier-general, given
two distinct points. -/
theorem keepSupported_is_not_a_structure_reader {a b : Pt X} (hab : a ≠ b) :
    ¬ ReadsOnlyStructure (keepSupported : Policy X) := by
  intro h
  have he := congrFun (congrFun (h (colCell a b true false) (colCell a b true true)
    (colCell_same_support a b true false true true)) a) b
  rw [keepSupported_declines (colCell_supported (Ne.symm hab)),
    keepSupported_takes hab (colCell_unsupported (Ne.symm hab))] at he
  exact absurd he (by simp)

theorem takeTrueFirst_is_not_a_structure_reader {a b : Pt X} (hab : a ≠ b) :
    ¬ ReadsOnlyStructure (takeTrueFirst : Policy X)
      ∧ colCell a b true false b a ≠ none ∧ colCell a b false false b a ≠ none := by
  have hba : b ≠ a := Ne.symm hab
  have h1 : (takeTrueFirst : Policy X) (colCell a b true false) b a = false := by
    simp only [takeTrueFirst, decide_eq_false_iff_not]
    rintro (hT | ⟨-, hno⟩)
    · rw [colCell_at_b hba] at hT
      exact absurd (Option.some_inj.mp hT) (by simp)
    · exact hno a a (colCell_at_a a b true false)
  have h2 : (takeTrueFirst : Policy X) (colCell a b false false) b a = true := by
    simp only [takeTrueFirst, decide_eq_true_eq]
    exact Or.inr ⟨colCell_at_b hba false false, colCell_false_has_no_true a b⟩
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have he := congrFun (congrFun (h (colCell a b true false) (colCell a b false false)
      (colCell_same_support a b true false false false)) b) a
    rw [h1, h2] at he
    exact absurd he (by simp)
  · rw [colCell_at_b hba]
    exact Option.some_ne_none _
  · rw [colCell_at_b hba]
    exact Option.some_ne_none _

theorem oneCell_ne_bot (a b : Pt X) (v : Bool) : (oneCell a b v : Pt X → Pt X → Option Bool)
    ≠ botC (Pt X) := by
  intro he
  have hc := congrFun (congrFun he a) b
  rw [oneCell_at] at hc
  exact Option.some_ne_none _ hc

theorem punctured_ne_bot {a b : Pt X} (hab : a ≠ b) :
    (punctured a b : Pt X → Pt X → Option Bool) ≠ botC (Pt X) := by
  intro he
  have hc := congrFun (congrFun he a) a
  rw [punctured_elsewhere a b (fun hq => hab (hq.1.symm.trans hq.2))] at hc
  exact Option.some_ne_none _ hc

/-- One configuration reached from everywhere and fixed there. -/
def SingleLimit (S : Policy X) : Prop :=
  ∃ d : Pt X → Pt X → Option Bool, step S d = d
    ∧ ∀ c : Pt X → Pt X → Option Bool, ∃ k : ℕ, runPolicy S c k = d

/-- A policy resting only where nothing is held goes to that one place from everywhere. Carrier-general. -/
theorem unique_rest_gives_a_single_limit {S : Policy X}
    (h : ∀ c : Pt X → Pt X → Option Bool, step S c = c → c = botC (Pt X)) : SingleLimit S := by
  refine ⟨botC (Pt X), step_bot S, fun c => ?_⟩
  obtain ⟨k, hk⟩ := every_policy_reaches_a_rest S c
  exact ⟨k, h _ hk⟩

/-- **A SINGLE LIMIT CAN ONLY BE THE WHOLLY UNCOMMITTED CONFIGURATION.** Every policy fixes that one, so a policy
reaching one place from everywhere reaches it from there too. Carrier-general. -/
theorem a_single_limit_is_empty {S : Policy X} (h : SingleLimit S) :
    ∃ d : Pt X → Pt X → Option Bool, (step S d = d
      ∧ ∀ c : Pt X → Pt X → Option Bool, ∃ k : ℕ, runPolicy S c k = d) ∧ d = botC (Pt X) := by
  obtain ⟨d, hd, hall⟩ := h
  obtain ⟨k, hk⟩ := hall (botC (Pt X))
  exact ⟨d, ⟨hd, hall⟩, by rw [← hk, runPolicy_bot]⟩

/-- **AND THE TWO SHARP NOTIONS EXCLUDE EACH OTHER.** A policy either has somewhere it rests while still holding
something, or it has one place it goes from everywhere and that place holds nothing. Not both. Carrier-general.
-/
theorem the_sharp_notions_are_exclusive (S : Policy X) : ¬ (StandingRest S ∧ SingleLimit S) := by
  rintro ⟨⟨c, hne, hf⟩, hs⟩
  obtain ⟨d, ⟨-, hall⟩, hbot⟩ := a_single_limit_is_empty hs
  obtain ⟨k, hk⟩ := hall c
  rw [runPolicy_fixed hf k, hbot] at hk
  exact hne hk

theorem takeIfHeld_rests_only_when_empty (c : Pt X → Pt X → Option Bool)
    (h : step (takeIfHeld : Policy X) c = c) : c = botC (Pt X) := by
  funext x y
  by_contra hv
  have := (step_fixed_iff _ c).mp h x y hv
  simp only [takeIfHeld, decide_eq_false_iff_not] at this
  exact this hv

/-- **THE CRUDE POSITIONAL RULE HAS NO STANDING REST, AND ACTS EXACTLY LIKE THE TOP POLE.** It reads only where
things are held, and what it does with that reading is empty everything. Carrier-general. -/
theorem takeIfHeld_has_no_standing_rest :
    ¬ StandingRest (takeIfHeld : Policy X)
      ∧ SingleLimit (takeIfHeld : Policy X)
      ∧ ∀ c : Pt X → Pt X → Option Bool,
          step (takeIfHeld : Policy X) c = step (takeAll : Policy X) c := by
  refine ⟨fun h => the_sharp_notions_are_exclusive _ ⟨h, ?_⟩,
    unique_rest_gives_a_single_limit takeIfHeld_rests_only_when_empty, fun c => ?_⟩
  · exact unique_rest_gives_a_single_limit takeIfHeld_rests_only_when_empty
  · funext x y
    by_cases hv : c x y = none
    · rw [step_preserves_absence hv, step_preserves_absence hv]
    · rw [show step (takeIfHeld : Policy X) c x y = none by
        simp [step, partialization, takeIfHeld, hv]]
      rw [show step (takeAll : Policy X) c x y = none by simp [step, partialization, takeAll]]

theorem cTrue_not_mobile : ¬ Mobile (cTrue : Pt X → Pt X → Option Bool) := by
  rintro ⟨-, ⟨p, hp⟩⟩
  rw [mem_fillableCells] at hp
  exact Option.some_ne_none _ hp

theorem cTrue_ne_bot (a : Pt X) : (cTrue : Pt X → Pt X → Option Bool) ≠ botC (Pt X) := by
  intro he
  have hc := congrFun (congrFun he a) a
  exact Option.some_ne_none _ hc

/-- **THE MOBILITY RULE HAS A STANDING REST, AND IT IS THE FULLEST CONFIGURATION THERE IS.** Where nothing can be
committed further the rule declines, so it holds everything and stops. Carrier-general, given a point. -/
theorem takeIfMobile_has_a_standing_rest (a : Pt X) : StandingRest (takeIfMobile : Policy X) := by
  refine ⟨cTrue, cTrue_ne_bot a, (step_fixed_iff _ _).mpr (fun x y _ => ?_)⟩
  simp only [takeIfMobile, decide_eq_false_iff_not]
  exact cTrue_not_mobile

/-- **A CONTENT READER HAS A STANDING REST TOO.** A configuration every pair of whose distinct rows is held
apart by present values is left alone, and it holds nearly everything. Carrier-general, given two distinct
points. -/
theorem keepSupported_has_a_standing_rest {a b : Pt X} (hab : a ≠ b) :
    StandingRest (keepSupported : Policy X) := by
  refine ⟨punctured a b, punctured_ne_bot hab, (step_fixed_iff _ _).mpr (fun x y _ => ?_)⟩
  by_cases hxy : x = y
  · simp [keepSupported, hxy]
  · exact keepSupported_declines (punctured_is_supported hab hxy)

/-- **AND ANOTHER CONTENT READER HAS NONE.** Wherever anything is held it takes at something held, so nothing but
the wholly uncommitted configuration is left alone. Carrier-general. -/
theorem takeTrueFirst_rests_only_when_empty (c : Pt X → Pt X → Option Bool)
    (h : step (takeTrueFirst : Policy X) c = c) : c = botC (Pt X) := by
  funext x y
  by_contra hv
  have hd := (step_fixed_iff _ c).mp h x y hv
  simp only [takeTrueFirst, decide_eq_false_iff_not] at hd
  rcases hb : c x y with - | b
  · exact hv hb
  · cases b with
    | true => exact hd (Or.inl hb)
    | false =>
      by_cases hex : ∃ p q : Pt X, c p q = some true
      · obtain ⟨p, q, hpq⟩ := hex
        have hd' := (step_fixed_iff _ c).mp h p q (by rw [hpq]; exact Option.some_ne_none _)
        simp only [takeTrueFirst, decide_eq_false_iff_not] at hd'
        exact hd' (Or.inl hpq)
      · refine hd (Or.inr ⟨hb, fun p q => ?_⟩)
        intro hpq
        exact hex ⟨p, q, hpq⟩

theorem takeTrueFirst_has_no_standing_rest :
    ¬ StandingRest (takeTrueFirst : Policy X) ∧ SingleLimit (takeTrueFirst : Policy X) := by
  refine ⟨fun h => the_sharp_notions_are_exclusive _ ⟨h, ?_⟩,
    unique_rest_gives_a_single_limit takeTrueFirst_rests_only_when_empty⟩
  exact unique_rest_gives_a_single_limit takeTrueFirst_rests_only_when_empty

/-- **READING ONLY STRUCTURE AND HAVING A STANDING REST ARE INDEPENDENT.** All four combinations occur. A
structure reader with a standing rest, a structure reader without one, a content reader with one, and a content
reader without one. So there is no line here to draw: resting while holding is not a matter of what a policy
reads.
Carrier-general, given two distinct points. -/
theorem they_are_independent {a b : Pt X} (hab : a ≠ b) :
    (ReadsOnlyStructure (takeIfMobile : Policy X) ∧ StandingRest (takeIfMobile : Policy X))
      ∧ (ReadsOnlyStructure (takeIfHeld : Policy X) ∧ ¬ StandingRest (takeIfHeld : Policy X))
      ∧ (¬ ReadsOnlyStructure (keepSupported : Policy X)
          ∧ StandingRest (keepSupported : Policy X))
      ∧ (¬ ReadsOnlyStructure (takeTrueFirst : Policy X)
          ∧ ¬ StandingRest (takeTrueFirst : Policy X)) :=
  ⟨⟨takeIfMobile_reads_structure, takeIfMobile_has_a_standing_rest a⟩,
   ⟨takeIfHeld_reads_structure, takeIfHeld_has_no_standing_rest.1⟩,
   ⟨keepSupported_is_not_a_structure_reader hab, keepSupported_has_a_standing_rest hab⟩,
   ⟨(takeTrueFirst_is_not_a_structure_reader hab).1, takeTrueFirst_has_no_standing_rest.1⟩⟩

end Content


#print axioms keepSupported_declines
#print axioms keepSupported_takes
#print axioms punctured_is_supported
#print axioms uniformExcept_hole
#print axioms uniformExcept_elsewhere
#print axioms the_two_hold_the_same_cells
#print axioms uniformExcept_is_unsupported
#print axioms keepSupported_reads_content
#print axioms keepSupported_is_neither_pole
#print axioms uniform_blocks_present_support
#print axioms dropUnsupported_le_keepSupported
#print axioms dropUniform_le_keepSupported
#print axioms the_two_act_identically
#print axioms the_recommendation_is_a_region
#print axioms keepSupported_fixed_iff
#print axioms punctured_mobile
#print axioms the_return_is_to_a_supported_position
#print axioms heldCells_eq_of_same_support
#print axioms fillableCells_eq_of_same_support
#print axioms takeIfHeld_reads_structure
#print axioms takeIfMobile_reads_structure
#print axioms colCell_at_a
#print axioms colCell_at_b
#print axioms colCell_off_column
#print axioms colCell_other_row
#print axioms colCell_same_support
#print axioms colCell_supported
#print axioms colCell_unsupported
#print axioms colCell_false_has_no_true
#print axioms keepSupported_is_not_a_structure_reader
#print axioms takeTrueFirst_is_not_a_structure_reader
#print axioms oneCell_ne_bot
#print axioms punctured_ne_bot
#print axioms unique_rest_gives_a_single_limit
#print axioms a_single_limit_is_empty
#print axioms the_sharp_notions_are_exclusive
#print axioms takeIfHeld_rests_only_when_empty
#print axioms takeIfHeld_has_no_standing_rest
#print axioms cTrue_not_mobile
#print axioms cTrue_ne_bot
#print axioms takeIfMobile_has_a_standing_rest
#print axioms keepSupported_has_a_standing_rest
#print axioms takeTrueFirst_rests_only_when_empty
#print axioms takeTrueFirst_has_no_standing_rest
#print axioms they_are_independent

end Chiralogy
