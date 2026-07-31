import Chiralogy.Experiments.archive.StanceCore

/-! ARCHIVED (fully graduated). The policies that read only where things are held.

GRADUATED to `Model/Stance` (the run and termination machinery, `StandingRest`, `the_criterion`) and
`Model/StanceContent` (`ReadsOnlyStructure`, the structure-reading family, the `colCell` witnesses,
`they_are_independent` and the four quadrant facts). Spec 4.a.19, 4.a.20.

`they_are_independent` graduated to the CONTENT module rather than the openness one, and the dependency graph
is why: it mentions `keepSupported`, so it uses both roots. That is the measured containment, not a choice.

Termination graduated as strict descent of a well-founded measure, NOT as a lattice fixed-point theorem: the
information order is not a lattice (`no_common_upper_bound`) and a policy need not be monotone, so
Knaster-Tarski does not apply here.

Typechecks standalone. -/

/-! # Experiment (LIVE): the policies that read only where things are held, and what resting means

The previous build surveyed the policies that read what is committed. This one surveys the policies that read
only WHERE things are committed, as a family of their own, then asks what resting can mean across the whole
space, and whether the two questions line up.

The survey does not assume an answer. Three candidate meanings of resting are defined and each is tested
against the family and against the content readers. Where a candidate turns out to hold of everything, that is
reported as the finding about the candidate.

Register-neutral throughout: no statement and no proof mentions any domain, and no name carries a register
term. The names used are policy, take, decline, held, structure, content, local and rest. All interpretive
readings are in the report only, and are flagged provisional.

Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy
open Chiralogy.StanceCore

set_option linter.unusedSectionVars false

namespace Chiralogy.AbstractStance

attribute [local instance] Classical.propDecidable

/-! ## The space, and the two things a policy can look at -/

section Space

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

/-! The object, the operator, the iterator, the two poles and the cell bookkeeping are `StanceCore`'s: this
file adds no copy of them. -/

/-- **A CONFIGURATION IS FIXED EXACTLY WHEN THE POLICY DECLINES EVERYWHERE IT HOLDS.** The general form of the
resting condition, for every policy at once. Carrier-general. -/
theorem step_fixed_iff (S : Policy X) (c : Pt X → Pt X → Option Bool) :
    step S c = c ↔ ∀ x y : Pt X, c x y ≠ none → S c x y = false := by
  constructor
  · intro h x y hv
    by_contra hs
    rw [Bool.not_eq_false] at hs
    have hc := congrFun (congrFun h x) y
    simp only [step, partialization, hs, if_true] at hc
    exact hv hc.symm
  · intro h
    funext x y
    by_cases hv : c x y = none
    · rw [step_preserves_absence hv, hv]
    · simp [step, partialization, h x y hv]

theorem runPolicy_succ (S : Policy X) (c : Pt X → Pt X → Option Bool) (k : ℕ) :
    runPolicy S c (k + 1) = step S (runPolicy S c k) := rfl

theorem runPolicy_shift (S : Policy X) (c : Pt X → Pt X → Option Bool) (k : ℕ) :
    runPolicy S c (k + 1) = runPolicy S (step S c) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [runPolicy_succ, ih, runPolicy_succ]

theorem runPolicy_fixed {S : Policy X} {c : Pt X → Pt X → Option Bool} (h : step S c = c) (k : ℕ) :
    runPolicy S c k = c := by
  induction k with
  | zero => rfl
  | succ k ih => rw [runPolicy_succ, ih, h]

theorem step_bot (S : Policy X) : step S (botC (Pt X)) = botC (Pt X) := by
  funext x y
  show step S (botC (Pt X)) x y = none
  exact step_preserves_absence rfl

theorem runPolicy_bot (S : Policy X) (k : ℕ) : runPolicy S (botC (Pt X)) k = botC (Pt X) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [runPolicy_succ, ih, step_bot]

/-- Wherever a policy does anything it holds strictly fewer cells afterwards. Carrier-general. -/
theorem strict_descent (S : Policy X) (c : Pt X → Pt X → Option Bool) (h : step S c ≠ c) :
    heldCells (step S c) ⊂ heldCells c := by
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

end Space

/-! ## Part 1: the structure-reading family

Four candidates come out of the arc's own positional quantities: mobility, the coordinate loads, the coupling
degree, and a named zone. A fifth, taking wherever anything is held, is the crudest positional rule and is kept
because it turns out to matter in Part 3. -/

section Family

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

/-- Take wherever anything is held. -/
def takeIfHeld : Policy X := fun c x y => decide (c x y ≠ none)

/-- Take everywhere exactly while both moves remain available. -/
noncomputable def takeIfMobile : Policy X := fun c _ _ => decide (Mobile c)

/-- How many held cells a coordinate is named in. -/
def load (c : Pt X → Pt X → Option Bool) (i : Fin n) : ℕ :=
  ((heldCells c).filter (fun p => i ∈ diffSet p.1 p.2)).card

/-- Take at a cell exactly when its separation names a coordinate of load at least `k`. -/
noncomputable def takeAtHighLoad (k : ℕ) : Policy X :=
  fun c x y => decide (∃ i : Fin n, i ∈ diffSet x y ∧ k ≤ load c i)

/-- How many other held cells a cell shares a coordinate with. -/
def degree (c : Pt X → Pt X → Option Bool) (p : Pt X × Pt X) : ℕ :=
  ((heldCells c).filter
    (fun q => q ≠ p ∧ (diffSet p.1 p.2 ∩ diffSet q.1 q.2).Nonempty)).card

/-- Take at a cell exactly when it couples to at least `k` others. -/
noncomputable def takeByCoupling (k : ℕ) : Policy X := fun c x y => decide (k ≤ degree c (x, y))

/-- Take exactly inside a named zone, wherever one is. -/
def takeInRegion (R : Finset (Pt X × Pt X)) : Policy X := fun _ x y => decide ((x, y) ∈ R)

/-! ### Each of them reads only where things are held -/

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

theorem takeAtHighLoad_reads_structure (k : ℕ) :
    ReadsOnlyStructure (takeAtHighLoad k : Policy X) := by
  intro c c' h
  funext x y
  simp only [takeAtHighLoad, load, heldCells_eq_of_same_support h]
  rfl

theorem takeByCoupling_reads_structure (k : ℕ) :
    ReadsOnlyStructure (takeByCoupling k : Policy X) := by
  intro c c' h
  funext x y
  simp only [takeByCoupling, degree, heldCells_eq_of_same_support h]

theorem takeInRegion_reads_structure (R : Finset (Pt X × Pt X)) :
    ReadsOnlyStructure (takeInRegion R : Policy X) := fun _ _ _ => rfl

/-- **AND THE TWO POLES ARE THE DEGENERATE MEMBERS.** They read the structure trivially, taking everything or
nothing whatever it is, so they belong to the family rather than standing outside it. Carrier-general. -/
theorem the_poles_are_degenerate_structure_readers :
    ReadsOnlyStructure (takeAll : Policy X) ∧ ReadsOnlyStructure (takeNone : Policy X) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-! ### Two configurations holding the same cells and holding different things -/

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

/-- **A STRUCTURE READER CANNOT SEE WHICH VERDICTS ARE HELD.** Every member of the family gives the same mask at
two configurations holding exactly the same cells with different verdicts in them. This is the defining
contrast with the content readers. Carrier-general. -/
theorem structure_readers_ignore_verdicts (a b : Pt X) (k : ℕ) (R : Finset (Pt X × Pt X)) :
    (takeIfHeld : Policy X) (colCell a b true false) = takeIfHeld (colCell a b true true)
      ∧ (takeIfMobile : Policy X) (colCell a b true false) = takeIfMobile (colCell a b true true)
      ∧ (takeAtHighLoad k : Policy X) (colCell a b true false)
          = takeAtHighLoad k (colCell a b true true)
      ∧ (takeByCoupling k : Policy X) (colCell a b true false)
          = takeByCoupling k (colCell a b true true)
      ∧ (takeInRegion R : Policy X) (colCell a b true false)
          = takeInRegion R (colCell a b true true) :=
  ⟨takeIfHeld_reads_structure _ _ (colCell_same_support a b true false true true),
   takeIfMobile_reads_structure _ _ (colCell_same_support a b true false true true),
   takeAtHighLoad_reads_structure k _ _ (colCell_same_support a b true false true true),
   takeByCoupling_reads_structure k _ _ (colCell_same_support a b true false true true),
   takeInRegion_reads_structure R _ _ (colCell_same_support a b true false true true)⟩

/-! ### The content readers, for the comparison -/

/-- Take the cells holding one verdict, and the others only once none of the first remain. -/
noncomputable def takeTrueFirst : Policy X :=
  fun c x y => decide (c x y = some true ∨ (c x y = some false ∧ ∀ p q : Pt X, c p q ≠ some true))

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

/-! ### The family is not the poles and its members are not each other -/

theorem heldCells_oneCell (a b : Pt X) (v : Bool) : heldCells (oneCell a b v) = {(a, b)} := by
  ext p
  rw [Finset.mem_singleton, mem_heldCells]
  by_cases h : p.1 = a ∧ p.2 = b
  · rw [show oneCell a b v p.1 p.2 = some v by simp [oneCell, h]]
    simp [Prod.ext_iff, h.1, h.2]
  · rw [oneCell_elsewhere a b v h]
    simp [Prod.ext_iff, h]

theorem oneCell_ne_bot (a b : Pt X) (v : Bool) : (oneCell a b v : Pt X → Pt X → Option Bool)
    ≠ botC (Pt X) := by
  intro he
  have hc := congrFun (congrFun he a) b
  rw [oneCell_at] at hc
  exact Option.some_ne_none _ hc

/-- **THE CRUDE POSITIONAL RULE IS BELOW THE TOP POLE AND ABOVE THE BOTTOM ONE, STRICTLY BOTH TIMES.** So the
family is a spectrum and not exhausted by its degenerate members. Carrier-general, given a cell. -/
theorem the_family_is_not_the_poles (a b : Pt X) (v : Bool) :
    (takeIfHeld : Policy X) (botC (Pt X)) a b ≠ (takeAll : Policy X) (botC (Pt X)) a b
      ∧ (takeIfHeld : Policy X) (oneCell a b v) a b
          ≠ (takeNone : Policy X) (oneCell a b v) a b := by
  refine ⟨?_, ?_⟩
  · simp [takeIfHeld, takeAll, botC]
  · rw [show (takeIfHeld : Policy X) (oneCell a b v) a b = true by
      simp [takeIfHeld, oneCell_at]]
    simp [takeNone]

theorem degree_oneCell (a b : Pt X) (v : Bool) : degree (oneCell a b v) (a, b) = 0 := by
  rw [degree, heldCells_oneCell, Finset.filter_singleton, if_neg (by simp)]
  exact Finset.card_empty

theorem load_oneCell_le_one (a b : Pt X) (v : Bool) (i : Fin n) : load (oneCell a b v) i ≤ 1 := by
  rw [load, heldCells_oneCell]
  calc ((({(a, b)} : Finset (Pt X × Pt X)).filter (fun p => i ∈ diffSet p.1 p.2)).card)
      ≤ ({(a, b)} : Finset (Pt X × Pt X)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = 1 := Finset.card_singleton _

/-- **AND THE MEMBERS ARE GENUINELY DIFFERENT RULES.** At a configuration holding one cell, the crude rule takes
there while the coupling rule and the load rule both decline, since one cell couples to nothing and loads
nothing twice. Carrier-general, given a cell. -/
theorem the_members_are_distinct (a b : Pt X) (v : Bool) :
    (takeIfHeld : Policy X) (oneCell a b v) a b = true
      ∧ (takeByCoupling 1 : Policy X) (oneCell a b v) a b = false
      ∧ (takeAtHighLoad 2 : Policy X) (oneCell a b v) a b = false := by
  refine ⟨by simp [takeIfHeld, oneCell_at], ?_, ?_⟩
  · simp only [takeByCoupling, decide_eq_false_iff_not, degree_oneCell]
    omega
  · simp only [takeAtHighLoad, decide_eq_false_iff_not]
    rintro ⟨i, -, hi⟩
    have := load_oneCell_le_one a b v i
    omega

end Family

/-! ## Part 2: what resting can mean, surveyed across the space

Three candidates: a fixed point, an invariant region avoiding the wholly uncommitted configuration, and
arriving at a rest from anywhere. The first and third turn out to hold of every policy whatever, so they
distinguish nothing; the second turns out to be the first sharpened, and collapses onto it. -/

section Rest

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

theorem rest_within (S : Policy X) : ∀ (m : ℕ) (c : Pt X → Pt X → Option Bool),
    (heldCells c).card ≤ m → ∃ k : ℕ, step S (runPolicy S c k) = runPolicy S c k := by
  intro m
  induction m with
  | zero =>
    intro c h
    refine ⟨0, ?_⟩
    have he : heldCells c = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp h)
    show step S c = c
    funext x y
    have hv : c x y = none := by
      by_contra hv
      have hmem : (x, y) ∈ heldCells c := mem_heldCells.mpr hv
      rw [he] at hmem
      exact absurd hmem (by simp)
    rw [step_preserves_absence hv, hv]
  | succ m ih =>
    intro c h
    by_cases hf : step S c = c
    · exact ⟨0, hf⟩
    · have hlt := Finset.card_lt_card (strict_descent S c hf)
      obtain ⟨k, hk⟩ := ih (step S c) (by omega)
      exact ⟨k + 1, by rw [runPolicy_shift]; exact hk⟩

/-- **EVERY POLICY ARRIVES AT A REST FROM EVERY CONFIGURATION.** Applying it only empties, and wherever it does
anything it holds strictly fewer cells, so on a finite carrier the iteration stops. Carrier-general. -/
theorem every_policy_reaches_a_rest (S : Policy X) (c : Pt X → Pt X → Option Bool) :
    ∃ k : ℕ, step S (runPolicy S c k) = runPolicy S c k :=
  rest_within S (heldCells c).card c le_rfl

/-- **AND EVERY POLICY FIXES THE WHOLLY UNCOMMITTED CONFIGURATION.** Carrier-general. -/
theorem every_policy_fixes_the_empty (S : Policy X) : step S (botC (Pt X)) = botC (Pt X) :=
  step_bot S

/-- **SO TWO OF THE THREE CANDIDATE MEANINGS OF RESTING ARE UNIVERSAL AND DISTINGUISH NOTHING.** Having a fixed
point holds of every policy, and arriving at a rest from anywhere holds of every policy. Neither can be the
notion the question was about. Carrier-general. -/
theorem the_plain_notions_are_universal (S : Policy X) :
    step S (botC (Pt X)) = botC (Pt X)
      ∧ ∀ c : Pt X → Pt X → Option Bool, ∃ k : ℕ,
          step S (runPolicy S c k) = runPolicy S c k :=
  ⟨step_bot S, every_policy_reaches_a_rest S⟩

/-- Resting somewhere while still holding something. -/
def StandingRest (S : Policy X) : Prop :=
  ∃ c : Pt X → Pt X → Option Bool, c ≠ botC (Pt X) ∧ step S c = c

/-- A region of configurations, none of them empty, that the policy maps into itself. -/
def InvariantHolding (S : Policy X) : Prop :=
  ∃ P : (Pt X → Pt X → Option Bool) → Prop,
    (∃ c, P c) ∧ (∀ c, P c → c ≠ botC (Pt X)) ∧ (∀ c, P c → P (step S c))

/-- One configuration reached from everywhere and fixed there. -/
def SingleLimit (S : Policy X) : Prop :=
  ∃ d : Pt X → Pt X → Option Bool, step S d = d
    ∧ ∀ c : Pt X → Pt X → Option Bool, ∃ k : ℕ, runPolicy S c k = d

/-- **THE REGION NOTION COLLAPSES ONTO THE POINT NOTION.** A region of non-empty configurations closed under the
policy must contain a fixed one, since the iteration inside it has to stop and cannot stop at the empty
configuration; and a single non-empty fixed configuration is such a region. So there is no resting without a
resting place. Carrier-general. -/
theorem the_region_notion_collapses (S : Policy X) : InvariantHolding S ↔ StandingRest S := by
  constructor
  · rintro ⟨P, ⟨c, hc⟩, hne, hcl⟩
    obtain ⟨k, hk⟩ := every_policy_reaches_a_rest S c
    have hP : ∀ j : ℕ, P (runPolicy S c j) := by
      intro j
      induction j with
      | zero => exact hc
      | succ j ih => rw [runPolicy_succ]; exact hcl _ ih
    exact ⟨runPolicy S c k, hne _ (hP k), hk⟩
  · rintro ⟨c, hne, hf⟩
    exact ⟨fun d => d = c, ⟨c, rfl⟩, fun d hd => hd ▸ hne, fun d hd => by rw [hd, hf]⟩

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

/-- A policy resting only where nothing is held goes to that one place from everywhere. Carrier-general. -/
theorem unique_rest_gives_a_single_limit {S : Policy X}
    (h : ∀ c : Pt X → Pt X → Option Bool, step S c = c → c = botC (Pt X)) : SingleLimit S := by
  refine ⟨botC (Pt X), step_bot S, fun c => ?_⟩
  obtain ⟨k, hk⟩ := every_policy_reaches_a_rest S c
  exact ⟨k, h _ hk⟩

/-! ### Which policies have a standing rest -/

theorem takeNone_has_a_standing_rest (a b : Pt X) (v : Bool) :
    StandingRest (takeNone : Policy X) :=
  ⟨oneCell a b v, oneCell_ne_bot a b v, by funext x y; simp [step, takeNone, partialization]⟩

theorem takeAll_rests_only_when_empty (c : Pt X → Pt X → Option Bool)
    (h : step (takeAll : Policy X) c = c) : c = botC (Pt X) := by
  funext x y
  by_contra hv
  exact absurd ((step_fixed_iff _ c).mp h x y hv) (by simp [takeAll])

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

/-- **THE COUPLING RULE HAS A STANDING REST.** A configuration holding one cell couples that cell to nothing, so
the rule declines there. Carrier-general, given a cell. -/
theorem takeByCoupling_has_a_standing_rest (a b : Pt X) (v : Bool) :
    StandingRest (takeByCoupling 1 : Policy X) := by
  refine ⟨oneCell a b v, oneCell_ne_bot a b v, (step_fixed_iff _ _).mpr (fun x y hv => ?_)⟩
  have hxy : x = a ∧ y = b := by
    by_contra hq
    exact hv (oneCell_elsewhere a b v hq)
  obtain ⟨hx, hy⟩ := hxy
  rw [hx, hy]
  simp only [takeByCoupling, decide_eq_false_iff_not, degree_oneCell]
  omega

/-- **AND SO DOES THE LOAD RULE.** One held cell loads no coordinate twice. Carrier-general, given a cell. -/
theorem takeAtHighLoad_has_a_standing_rest (a b : Pt X) (v : Bool) :
    StandingRest (takeAtHighLoad 2 : Policy X) := by
  refine ⟨oneCell a b v, oneCell_ne_bot a b v, (step_fixed_iff _ _).mpr (fun x y _ => ?_)⟩
  simp only [takeAtHighLoad, decide_eq_false_iff_not]
  rintro ⟨i, -, hi⟩
  have := load_oneCell_le_one a b v i
  omega

/-- **AND SO DOES A NAMED ZONE, PROVIDED THERE IS ANYWHERE OUTSIDE IT.** Carrier-general. -/
theorem takeInRegion_has_a_standing_rest {R : Finset (Pt X × Pt X)} {a b : Pt X} (v : Bool)
    (h : (a, b) ∉ R) : StandingRest (takeInRegion R : Policy X) := by
  refine ⟨oneCell a b v, oneCell_ne_bot a b v, (step_fixed_iff _ _).mpr (fun x y hv => ?_)⟩
  have hxy : x = a ∧ y = b := by
    by_contra hq
    exact hv (oneCell_elsewhere a b v hq)
  obtain ⟨hx, hy⟩ := hxy
  rw [hx, hy]
  simp only [takeInRegion, decide_eq_false_iff_not]
  exact h

/-! ### And which content readers do -/

theorem punctured_ne_bot {a b : Pt X} (hab : a ≠ b) :
    (punctured a b : Pt X → Pt X → Option Bool) ≠ botC (Pt X) := by
  intro he
  have hc := congrFun (congrFun he a) a
  rw [punctured_elsewhere a b (fun hq => hab (hq.1.symm.trans hq.2))] at hc
  exact Option.some_ne_none _ hc

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

end Rest

/-! ## Part 3: whether the two questions line up, and where the difference actually sits -/

section Alignment

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

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

/-- **AND NEITHER DIRECTION OF THE CONJECTURE SURVIVES.** Not every structure reader rests while holding
something, and not every content reader fails to. Carrier-general, given two distinct points. -/
theorem neither_direction_holds {a b : Pt X} (hab : a ≠ b) :
    ¬ (∀ S : Policy X, ReadsOnlyStructure S → StandingRest S)
      ∧ ¬ (∀ S : Policy X, StandingRest S → ReadsOnlyStructure S) := by
  refine ⟨fun h => takeIfHeld_has_no_standing_rest.1 (h _ takeIfHeld_reads_structure),
    fun h => keepSupported_is_not_a_structure_reader hab
      (h _ (keepSupported_has_a_standing_rest hab))⟩

/-! ### The candidate mechanism: local against global -/

/-- A cell property read off that cell alone. -/
def Local (Q : (Pt X → Pt X → Option Bool) → Pt X → Pt X → Prop) : Prop :=
  ∀ (c c' : Pt X → Pt X → Option Bool) (x y : Pt X), c x y = c' x y → (Q c x y ↔ Q c' x y)

/-- A policy whose mask at a cell is read off that cell alone. -/
def MaskLocal (S : Policy X) : Prop :=
  ∀ (c c' : Pt X → Pt X → Option Bool) (x y : Pt X), c x y = c' x y → S c x y = S c' x y

/-- **WHETHER A CELL IS OPEN IS A LOCAL FACT.** Carrier-general. -/
theorem openness_is_local : Local (fun (c : Pt X → Pt X → Option Bool) x y => c x y = none) := by
  intro c c' x y h
  dsimp only
  rw [h]

/-- **WHETHER A SEPARATION IS SUPPORTED IS NOT.** Two configurations agreeing at a cell can disagree about
whether the rows that cell joins are held apart by present values, because the witness is elsewhere.
Carrier-general, given two distinct points. -/
theorem support_is_not_local {a b : Pt X} (hab : a ≠ b) :
    ¬ Local (fun (c : Pt X → Pt X → Option Bool) x y => presentCarried c x y) := by
  intro h
  have hcell : colCell a b true false a b = colCell a b true true a b := by
    rw [colCell_off_column a b true false (Ne.symm hab),
      colCell_off_column a b true true (Ne.symm hab)]
  exact colCell_unsupported (Ne.symm hab)
    ((h _ _ a b hcell).mp (colCell_supported (Ne.symm hab)))

/-- **BUT LOCALITY DOES NOT TRACK RESTING EITHER.** The crude positional rule is read off each cell alone and has
no standing rest; the supported-keeping rule is not, and has one. So the local against global difference is
real and is not what the resting difference is made of. Carrier-general, given two distinct points. -/
theorem locality_does_not_track_resting {a b : Pt X} (hab : a ≠ b) :
    (MaskLocal (takeIfHeld : Policy X) ∧ ¬ StandingRest (takeIfHeld : Policy X))
      ∧ (¬ MaskLocal (keepSupported : Policy X) ∧ StandingRest (keepSupported : Policy X)) := by
  refine ⟨⟨fun c c' x y h => by simp only [takeIfHeld, h], takeIfHeld_has_no_standing_rest.1⟩,
    ⟨fun h => ?_, keepSupported_has_a_standing_rest hab⟩⟩
  have hcell : colCell a b true false a b = colCell a b true true a b := by
    rw [colCell_off_column a b true false (Ne.symm hab),
      colCell_off_column a b true true (Ne.symm hab)]
  have he := h _ _ a b hcell
  rw [keepSupported_declines (colCell_supported (Ne.symm hab)),
    keepSupported_takes hab (colCell_unsupported (Ne.symm hab))] at he
  exact absurd he (by simp)

/-- **WHAT RESTING WHILE HOLDING SOMETHING ACTUALLY REQUIRES.** A policy has a standing rest exactly when some
non-empty configuration is one it declines at wholly: everything that configuration holds, the policy leaves.
The criterion is about the fit between a policy and a configuration and mentions neither structure nor content.
Carrier-general. -/
theorem the_criterion (S : Policy X) :
    StandingRest S ↔ ∃ c : Pt X → Pt X → Option Bool, c ≠ botC (Pt X)
      ∧ ∀ x y : Pt X, c x y ≠ none → S c x y = false := by
  constructor
  · rintro ⟨c, hne, hf⟩
    exact ⟨c, hne, (step_fixed_iff S c).mp hf⟩
  · rintro ⟨c, hne, hd⟩
    exact ⟨c, hne, (step_fixed_iff S c).mpr hd⟩

/-- **AND THE THREE NOTIONS, ASSEMBLED.** Having a fixed point and arriving at a rest hold of every policy. The
region notion is the standing rest in other words. And a standing rest and a single limit are exclusive, so
every policy either keeps somewhere or empties everywhere. Carrier-general. -/
theorem the_survey_of_resting (S : Policy X) :
    (step S (botC (Pt X)) = botC (Pt X)
        ∧ ∀ c : Pt X → Pt X → Option Bool, ∃ k : ℕ,
            step S (runPolicy S c k) = runPolicy S c k)
      ∧ (InvariantHolding S ↔ StandingRest S)
      ∧ ¬ (StandingRest S ∧ SingleLimit S) :=
  ⟨the_plain_notions_are_universal S, the_region_notion_collapses S,
   the_sharp_notions_are_exclusive S⟩

end Alignment

/-! ## THE VERDICTS

A CORRECTION TO THE BRIEF, FIRST, BECAUSE THE SURVEY TURNS ON IT. The brief records as its motivating evidence
that the supported-keeping policy has NO fixed point. That is not what the previous build proved. It proved the
opposite: `keepSupported_fixed_iff` characterized its resting places exactly, `a_rich_configuration_rests`
exhibited one holding nearly every cell, and `the_resting_places_are_many` showed there are several. The
conjecture's premise is therefore false as stated before the survey begins, and the survey below confirms this
independently: `keepSupported_has_a_standing_rest`.

PART 1: THE STRUCTURE-READING FAMILY IS DEFINABLE, AND IT IS A FAMILY.

`ReadsOnlyStructure` is the condition: the same mask at any two configurations holding the same cells, whatever
those cells hold. Five members are derived from the arc's own positional quantities. `takeIfHeld` takes wherever
anything is held. `takeIfMobile` takes everywhere exactly while both moves remain available. `takeAtHighLoad k`
takes at a cell whose separation names a coordinate carried by at least `k` held cells. `takeByCoupling k`
takes at a cell sharing a coordinate with at least `k` others. `takeInRegion R` takes exactly inside a named
zone.

Each is proved to read only structure, and the proofs go through one lemma:
`heldCells_eq_of_same_support`. Everything positional the arc built is a function of the held set, and the held
set is a function of the support, so ANY quantity the earlier builds defined yields a structure reader
automatically. That is why the family is large and easy to populate.

`structure_readers_ignore_verdicts` states the defining contrast directly. At two configurations holding exactly
the same two cells, one in agreement and one not, every member gives the SAME mask.
`keepSupported_is_not_a_structure_reader` and `takeTrueFirst_is_not_a_structure_reader` give the other side, and
the second is sharper than needed: its mask differs at a cell IT HOLDS, so the content it reads is content that
bears on what it does, not content read idly where nothing is held.

`the_poles_are_degenerate_structure_readers` places the poles INSIDE the family rather than outside it: they read
the structure trivially. `the_family_is_not_the_poles` and `the_members_are_distinct` confirm the family is a
spectrum with genuinely different rules in it.

PART 2: TWO OF THE THREE CANDIDATE MEANINGS OF RESTING ARE VACUOUS, AND THE THIRD IS THE FIRST SHARPENED.

This is the surprise of the build and it reshapes the question.

`every_policy_fixes_the_empty`: the wholly uncommitted configuration is fixed by EVERY policy, because taking a
withdrawal where nothing is held does nothing. So HAVING A FIXED POINT IS UNIVERSAL.

`every_policy_reaches_a_rest`: every policy only empties, and wherever it does anything it holds strictly fewer
cells, so on a finite carrier every run stops. So ARRIVING AT A REST FROM ANYWHERE IS UNIVERSAL TOO.
`the_plain_notions_are_universal` states both together. Neither candidate distinguishes anything, so neither can
be what the question was about.

What survives is the sharpened notion: `StandingRest`, resting somewhere WHILE STILL HOLDING SOMETHING.

`the_region_notion_collapses` disposes of the third candidate. A region of non-empty configurations closed under
the policy must contain a fixed one, since the iteration inside it has to stop and cannot stop where nothing is
held. So an invariant region is a standing rest in other words: THERE IS NO RESTING WITHOUT A RESTING PLACE.

`a_single_limit_is_empty` and `the_sharp_notions_are_exclusive` give the resulting dichotomy, and it is clean.
Any single limit must be the wholly uncommitted configuration, because every policy fixes that one and so
reaches it from there. Hence a policy CANNOT both keep something somewhere and go to one place from everywhere.
EVERY POLICY EITHER KEEPS SOMEWHERE OR EMPTIES EVERYWHERE.

The survey by policy: `takeNone`, `takeIfMobile`, `takeByCoupling 1`, `takeAtHighLoad 2`, `takeInRegion R` with
anything outside `R`, and `keepSupported` all have a standing rest. `takeAll`, `takeIfHeld` and `takeTrueFirst`
have none and go to the empty configuration from everywhere.

`takeIfMobile_has_a_standing_rest` is worth naming: its resting place is the FULLEST configuration there is.
Where nothing further can be committed the rule declines, so it stops holding everything.

PART 3: THE LINE IS NOT DRAWN, AND THE PROPOSED MECHANISM IS NOT THE MECHANISM.

`they_are_independent` is the answer and it is independence, not coincidence and not partial coincidence. ALL
FOUR COMBINATIONS OCCUR:

  reads structure, rests holding something: `takeIfMobile`
  reads structure, does not: `takeIfHeld`
  reads content, rests holding something: `keepSupported`
  reads content, does not: `takeTrueFirst`

`neither_direction_holds` states it as the two failed implications. Not every structure reader rests while
holding something; not everything that rests reads only structure. So the conjecture fails in both directions,
and SUSTAINABILITY IS NOT A MATTER OF WHAT A POLICY READS.

The proposed mechanism is then tested on its own and it half survives. `openness_is_local` and
`support_is_not_local` confirm the real asymmetry: whether a cell is open is read off that cell, while whether
the rows a cell joins are held apart by present values depends on cells elsewhere, so two configurations
agreeing at a cell can disagree about it. THE LOCAL AGAINST GLOBAL DIFFERENCE IS REAL.

`locality_does_not_track_resting` shows it is not what the resting difference is made of. `takeIfHeld` is read
off each cell alone and has no standing rest. `keepSupported` is not, and has one. So the mechanism is elsewhere.

`the_criterion` says where. A policy has a standing rest exactly when SOME NON-EMPTY CONFIGURATION IS ONE IT
DECLINES AT WHOLLY: everything that configuration holds, the policy leaves. That criterion is a fit between a
policy and a configuration, and it mentions neither structure nor content. It is why the four combinations are
all available: a positional rule can be built to decline on a full configuration or to take on every held one,
and so can a content-reading rule.

`the_survey_of_resting` assembles the three notions for any policy at once.

PART 4: ASSEMBLED.

The structure-reading policies are a family, easily populated, because every positional quantity the arc built is
a function of the held set alone. The content readers are the complement and two of them are exhibited.

Resting has exactly one non-vacuous meaning on this arm: resting somewhere while still holding something. Having
a fixed point and arriving at a rest are universal, the region notion collapses onto the point notion, and a
standing rest and a single limit exclude each other.

Reading only structure and having a standing rest are INDEPENDENT. The conjecture that abstraction buys
sustainability is false in both directions. The local against global asymmetry between openness and support is
real but does not track resting. What does is whether the policy declines wholly at some non-empty
configuration, which is a fit between the rule and a position and is available to positional and content-reading
rules alike.

ONE ARM. Every policy here only empties, `step_descends`, so a standing rest is a place a policy stops taking
and never a place it rebuilds anything. A rule aiming to MAINTAIN a positional quantity, for instance to keep
mobility away from both extremes, would have to commit as well as withdraw, and cannot be written in this space
at all. That is a limitation of the object and not a finding about structure or content.

REGISTER READINGS. Report only, PROVISIONAL, and to be read as projections that this exploration refines rather
than as what the results mean. They are supplied by the register and not derived.

  ON THE CONJECTURE, PROVISIONALLY. The thought was that a commitment to HOW one holds things could be kept
  steady where a commitment to WHAT one holds could not. On this object that is not so. A commitment about how
  can be one that dismantles everything, and a commitment about what can be one that settles and keeps a great
  deal. The distinction between procedure and substance does not by itself decide whether a commitment can be
  lived with.

  ON WHAT REPLACES IT, PROVISIONALLY. What decides is whether there is any position the rule would leave
  entirely alone. A rule with no such position takes something wherever it finds anything, and ends holding
  nothing, however abstractly or concretely it is stated. A rule with one has somewhere to stand. That is a
  question about the fit between a rule and the situations it might be in, not about the vocabulary the rule is
  written in.

  COGNITION, PROVISIONALLY. Committing to a manner of holding rather than to a content does not on its own
  protect one from ending up holding nothing. The manner can be corrosive. What matters is whether some way one
  could actually be is one the commitment would not object to anywhere.

  POLITICS, PROVISIONALLY. A procedural commitment is not automatically more livable than a substantive one. A
  procedure that finds something to reopen in every arrangement whatever settles nothing, and a substantive
  commitment can rest. The question to ask of either is whether there is an arrangement it would leave standing
  in full.

  ON THE LOCAL AND THE GLOBAL, PROVISIONALLY. The asymmetry is real and worth keeping for its own sake: where a
  thing stands is a fact about it, while whether it is held up by what is actually said is a fact about it
  together with everything else. That much is proved. It is simply not the reason some commitments settle.

AXIOM PROFILE AND GRADUATION. Every result is at baseline or below. Graduation is NOT proposed: the objects are
defined here and none has been placed. Four are flagged as substantive and carrier-general:
`the_plain_notions_are_universal`, which empties two of the three candidate notions;
`the_region_notion_collapses`, which reduces the third to the first; `they_are_independent`, which refutes the
conjecture in both directions; and `the_criterion`, which says what resting while holding something actually
requires.

WHAT REMAINS OPEN

1. The four family members are derived from mobility, load, coupling and a zone. Whether every structure
   reader is a function of the held set through one of these, or whether the family has a normal form, is not
   asked.
2. `the_criterion` characterizes having a standing rest. WHICH configurations are standing rests of a given
   policy, and how that set varies along the policy order, is not studied.
3. The exclusivity of standing rest and single limit is proved. Whether a policy with a standing rest can also
   have several unrelated ones, and how the reached one depends on the start, is not settled here.
4. Every policy only empties. A space of policies that both take and land is not constructed, and the question
   of maintaining a positional quantity cannot be posed until it is.
5. Nothing here is graduated. -/

#print axioms step_fixed_iff
#print axioms runPolicy_succ
#print axioms runPolicy_shift
#print axioms runPolicy_fixed
#print axioms step_bot
#print axioms runPolicy_bot
#print axioms strict_descent
#print axioms heldCells_eq_of_same_support
#print axioms fillableCells_eq_of_same_support
#print axioms takeIfHeld_reads_structure
#print axioms takeIfMobile_reads_structure
#print axioms takeAtHighLoad_reads_structure
#print axioms takeByCoupling_reads_structure
#print axioms takeInRegion_reads_structure
#print axioms the_poles_are_degenerate_structure_readers
#print axioms colCell_at_a
#print axioms colCell_at_b
#print axioms colCell_off_column
#print axioms colCell_other_row
#print axioms colCell_same_support
#print axioms structure_readers_ignore_verdicts
#print axioms colCell_false_has_no_true
#print axioms colCell_supported
#print axioms colCell_unsupported
#print axioms keepSupported_is_not_a_structure_reader
#print axioms takeTrueFirst_is_not_a_structure_reader
#print axioms heldCells_oneCell
#print axioms oneCell_ne_bot
#print axioms the_family_is_not_the_poles
#print axioms degree_oneCell
#print axioms load_oneCell_le_one
#print axioms the_members_are_distinct
#print axioms rest_within
#print axioms every_policy_reaches_a_rest
#print axioms every_policy_fixes_the_empty
#print axioms the_plain_notions_are_universal
#print axioms the_region_notion_collapses
#print axioms a_single_limit_is_empty
#print axioms the_sharp_notions_are_exclusive
#print axioms unique_rest_gives_a_single_limit
#print axioms takeNone_has_a_standing_rest
#print axioms takeAll_rests_only_when_empty
#print axioms takeIfHeld_rests_only_when_empty
#print axioms takeIfHeld_has_no_standing_rest
#print axioms cTrue_not_mobile
#print axioms cTrue_ne_bot
#print axioms takeIfMobile_has_a_standing_rest
#print axioms takeByCoupling_has_a_standing_rest
#print axioms takeAtHighLoad_has_a_standing_rest
#print axioms takeInRegion_has_a_standing_rest
#print axioms punctured_ne_bot
#print axioms keepSupported_has_a_standing_rest
#print axioms takeTrueFirst_rests_only_when_empty
#print axioms takeTrueFirst_has_no_standing_rest
#print axioms they_are_independent
#print axioms neither_direction_holds
#print axioms openness_is_local
#print axioms support_is_not_local
#print axioms locality_does_not_track_resting
#print axioms the_criterion
#print axioms the_survey_of_resting

end Chiralogy.AbstractStance
