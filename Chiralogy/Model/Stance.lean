import Chiralogy.Model.NaryAssemblage
import Mathlib.Data.Fintype.Prod

/-! # The stance: rules that act on a classification

A classification is a partial map, ordered by the information (refinement) order of `Model/InformationOrder`.
This module adds the rules that ACT on one. A rule with one direction is a POLICY: at each classification it
names a mask of cells to withdraw, and applying it is `partialization` at that mask, so every policy is
DEFLATIONARY (decreasing) for the information order. A rule with both directions is a STANCE: it names a mask
to withdraw and an instruction of what to form, and one application withdraws first and then forms into
whatever is open, forming being powerless where anything is already held.

The two are one object: `applyStance_ofMask_eq_step` shows a policy step is the stance application at a stance
that forms nothing, so the module carries one operator and not two.

Standard vocabulary throughout, and canonical facts are cited rather than re-derived: deflationary is `f x ≤ x`
for `cLE` and comes from `partialization_le_c`; a resting classification is a `Function.IsFixedPt`; the two
poles are a CONSTANT map and the IDENTITY map; a two-element invariant set with no fixed point is a period-two
PERIODIC ORBIT. Nothing here is an attractor in the technical sense (no minimal invariant set with a dense orbit
and a basin is claimed), and the Knaster-Tarski route is unavailable by the framework's own
`no_common_upper_bound`: the information order is not a lattice and a policy need not be monotone, so the
fixed-point facts are proved by well-founded descent on a finite carrier instead.

Depends on the moves and the information order (`partialization`, `cLE`, `botC`, `isTotal`) and on the n-ary
carrier `Pt` for the classifications it acts on. The content-reading half, which additionally needs
present-support, is `Model/StanceContent`. -/

namespace Chiralogy

set_option linter.unusedSectionVars false

/-! ## The two objects

A rule with one direction is a policy: at each configuration it names a mask of cells to release. A rule with
both directions is a stance: it names a mask to release and an instruction of what to form. -/

/-- A rule for which withdrawals are taken, at every configuration. -/
abbrev Policy {n : ℕ} (X : Fin n → Type) : Type :=
  (Pt X → Pt X → Option Bool) → Pt X → Pt X → Bool

/-- A rule with both directions: what to release at each configuration, and what to form. -/
structure Stance {n : ℕ} (X : Fin n → Type) where
  drop : (Pt X → Pt X → Option Bool) → Pt X → Pt X → Bool
  form : (Pt X → Pt X → Option Bool) → Pt X → Pt X → Option Bool

section Operators

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- Applying a policy once. The move is the derived open, `partialization` at the mask the policy names. -/
def step (S : Policy X) (c : Pt X → Pt X → Option Bool) : Pt X → Pt X → Option Bool :=
  partialization (S c) c

/-- Applying a policy repeatedly. -/
def runPolicy (S : Policy X) (c : Pt X → Pt X → Option Bool) : ℕ → Pt X → Pt X → Option Bool
  | 0 => c
  | k + 1 => step S (runPolicy S c k)

/-- What the stance has let go of, before it forms anything. -/
def release (T : Stance X) (c : Pt X → Pt X → Option Bool) : Pt X → Pt X → Option Bool :=
  partialization (T.drop c) c

/-- One application of a stance: release, then form into whatever is open. -/
def applyStance (T : Stance X) (c : Pt X → Pt X → Option Bool) : Pt X → Pt X → Option Bool :=
  fun x y => if release T c x y = none then T.form c x y else release T c x y

/-- Applying a stance repeatedly. -/
def runStance (T : Stance X) (c : Pt X → Pt X → Option Bool) : ℕ → Pt X → Pt X → Option Bool
  | 0 => c
  | k + 1 => applyStance T (runStance T c k)

/-- One policy takes wherever another does. -/
def PolicyLE (S T : Policy X) : Prop :=
  ∀ (c : Pt X → Pt X → Option Bool) (x y : Pt X), S c x y = true → T c x y = true

/-- The policy that takes every withdrawal. -/
def takeAll : Policy X := fun _ _ _ => true

/-- The policy that takes none. -/
def takeNone : Policy X := fun _ _ _ => false

/-- The policy that takes only at one named cell. -/
def takeAt (a b : Pt X) : Policy X := fun _ x y => decide (x = a ∧ y = b)

/-- A stance that never forms: its forming component is empty everywhere. -/
def FormsNothing (T : Stance X) : Prop := ∀ c x y, T.form c x y = none

/-- A self map of the classifications is DEFLATIONARY (decreasing) when it lands at or below its input in the
information order: the standard `f x ≤ x` condition, written for `cLE`. -/
def Deflationary (f : (Pt X → Pt X → Option Bool) → Pt X → Pt X → Option Bool) : Prop :=
  ∀ c, cLE (f c) c

/-- A self map has a NON-BOTTOM FIXED POINT when some classification other than the order-bottom is fixed.
Stated with Mathlib's `Function.IsFixedPt`. -/
def HasNonBottomFixedPoint (f : (Pt X → Pt X → Option Bool) → Pt X → Pt X → Option Bool) : Prop :=
  ∃ c, c ≠ botC (Pt X) ∧ Function.IsFixedPt f c

/-- Every mask, read as a stance that only releases. -/
def ofMask (S : Policy X) : Stance X := ⟨S, fun _ _ _ => none⟩

/-! ### The policy operator is the stance operator at a stance that forms nothing -/

theorem release_of_dropped {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : T.drop c x y = true) : release T c x y = none := by simp [release, partialization, h]

theorem release_of_kept {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : T.drop c x y = false) : release T c x y = c x y := by simp [release, partialization, h]

theorem applyStance_of_dropped {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : T.drop c x y = true) : applyStance T c x y = T.form c x y := by
  simp [applyStance, release_of_dropped h]

theorem applyStance_of_kept_open {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (hd : T.drop c x y = false) (hv : c x y = none) : applyStance T c x y = T.form c x y := by
  simp [applyStance, release_of_kept hd, hv]

/-- **FORMING IS POWERLESS AT A CELL THE STANCE DOES NOT RELEASE.** Whatever the stance would form there, a cell
it keeps holds what it held. To change a holding, a stance must let go of it first: there is no overwriting,
only releasing and forming again. Carrier-general. -/
theorem forming_is_powerless_at_a_held_cell {T : Stance X} {c : Pt X → Pt X → Option Bool}
    {x y : Pt X} {v : Bool} (hd : T.drop c x y = false) (hv : c x y = some v) :
    applyStance T c x y = some v := by
  rw [applyStance, release_of_kept hd, hv, if_neg (Option.some_ne_none v)]

/-- **AND THAT IS THE ONLY WAY A CELL CAN CHANGE.** If a cell holds something before and something different
after, the stance released it. Carrier-general. -/
theorem a_change_requires_a_release {T : Stance X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    {v : Bool} (hv : c x y = some v) (hne : applyStance T c x y ≠ some v) : T.drop c x y = true := by
  by_contra hd
  rw [Bool.not_eq_true] at hd
  exact hne (forming_is_powerless_at_a_held_cell hd hv)

theorem ofMask_formsNothing (S : Policy X) : FormsNothing (ofMask S) := fun _ _ _ => rfl

/-- **THE DEFLATIONARY STANCES ARE EXACTLY THE POLICIES.** One application of a stance that forms nothing is the
opening its mask names, so the one-directional space embeds in the two-directional one. Carrier-general. -/
theorem the_deflationary_stances_embed (S : Policy X) (c : Pt X → Pt X → Option Bool) :
    applyStance (ofMask S) c = partialization (S c) c := by
  funext x y
  by_cases h : S c x y = true
  · rw [applyStance_of_dropped (T := ofMask S) h]
    simp [ofMask, partialization, h]
  · rw [Bool.not_eq_true] at h
    rw [applyStance, release_of_kept (T := ofMask S) h]
    by_cases hv : c x y = none
    · simp [ofMask, partialization, h, hv]
    · simp [partialization, h, hv]

/-- **SO THE TWO OPERATORS ARE ONE OPERATOR.** The policy step is the stance application at the policy's own
stance that forms nothing, so nothing in the layer needs a second notion of applying a rule. Carrier-general. -/
theorem applyStance_ofMask_eq_step (S : Policy X) (c : Pt X → Pt X → Option Bool) :
    applyStance (ofMask S) c = step S c := the_deflationary_stances_embed S c

theorem step_preserves_absence {S : Policy X} {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : c x y = none) : step S c x y = none := by
  simp only [step, partialization]
  by_cases hw : S c x y <;> simp [hw, h]

/-- **EVERY POLICY IS DEFLATIONARY.** One application lands at or below its input in the information order. This
is canonical `partialization_le_c` at the mask the policy names, not a new fact: a policy step IS a
partialization. Carrier-general. -/
theorem step_deflationary (S : Policy X) : Deflationary (step S) :=
  fun c => partialization_le_c (S c) c

/-- **AND A STANCE THAT FORMS NOTHING IS DEFLATIONARY.** Carrier-general. -/
theorem formsNothing_deflationary {T : Stance X} (h : FormsNothing T) : Deflationary (applyStance T) := by
  intro c x y
  by_cases hd : T.drop c x y = true
  · exact Or.inl (by rw [applyStance_of_dropped hd, h])
  · rw [Bool.not_eq_true] at hd
    by_cases hv : c x y = none
    · exact Or.inl (by rw [applyStance_of_kept_open hd hv, h])
    · rcases hb : c x y with - | v
      · exact absurd hb hv
      · exact Or.inr (by rw [forming_is_powerless_at_a_held_cell hd hb])

/-- **SO A DEFLATIONARY STANCE CANNOT OPEN A CELL AND THEN CLOSE IT.** What it lets go of stays gone.
Carrier-general. -/
theorem formsNothing_preserves_absence {T : Stance X} (h : FormsNothing T)
    {c : Pt X → Pt X → Option Bool} {x y : Pt X} (hv : c x y = none) : applyStance T c x y = none := by
  rcases formsNothing_deflationary h c x y with hn | he
  · exact hn
  · rw [he, hv]

end Operators

/-! ## The cell bookkeeping -/

section Bookkeeping

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

def heldCells (c : Pt X → Pt X → Option Bool) : Finset (Pt X × Pt X) :=
  Finset.univ.filter (fun p => c p.1 p.2 ≠ none)

def fillableCells (c : Pt X → Pt X → Option Bool) : Finset (Pt X × Pt X) :=
  Finset.univ.filter (fun p => c p.1 p.2 = none)

/-- Both directions are available: something is held and something is open. -/
def Mobile (c : Pt X → Pt X → Option Bool) : Prop :=
  (heldCells c).Nonempty ∧ (fillableCells c).Nonempty

theorem mem_heldCells {c : Pt X → Pt X → Option Bool} {p : Pt X × Pt X} :
    p ∈ heldCells c ↔ c p.1 p.2 ≠ none := by simp [heldCells]

theorem mem_fillableCells {c : Pt X → Pt X → Option Bool} {p : Pt X × Pt X} :
    p ∈ fillableCells c ↔ c p.1 p.2 = none := by simp [fillableCells]

end Bookkeeping

/-! ## The witness constructions -/

section Witnesses

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- Commit one named cell and nothing else. -/
def oneCell (a b : Pt X) (v : Bool) : Pt X → Pt X → Option Bool :=
  fun x y => if x = a ∧ y = b then some v else none

theorem oneCell_at (a b : Pt X) (v : Bool) : oneCell a b v a b = some v := by simp [oneCell]

theorem oneCell_elsewhere (a b : Pt X) (v : Bool) {x y : Pt X} (h : ¬ (x = a ∧ y = b)) :
    oneCell a b v x y = none := by simp [oneCell, h]

/-- Hold the whole diagonal-agreement classification except at one named cell. -/
def punctured (a b : Pt X) : Pt X → Pt X → Option Bool :=
  fun x y => if x = a ∧ y = b then none else some (decide (x = y))

theorem punctured_hole (a b : Pt X) : punctured a b a b = none := by simp [punctured]

theorem punctured_elsewhere (a b : Pt X) {x y : Pt X} (h : ¬ (x = a ∧ y = b)) :
    punctured a b x y = some (decide (x = y)) := by simp [punctured, h]

end Witnesses


/-! ## Fixed points, runs, and termination

A resting classification is a `Function.IsFixedPt` of the operator. The Knaster-Tarski route is unavailable:
the information order is not a lattice (`no_common_upper_bound`) and a policy need not be monotone. Termination
is proved instead by strict descent of the held-cell count on a finite carrier, a well-founded measure. -/

section Dynamics

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

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

/-- Resting somewhere while still holding something. -/
def StandingRest (S : Policy X) : Prop :=
  ∃ c : Pt X → Pt X → Option Bool, c ≠ botC (Pt X) ∧ step S c = c

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

end Dynamics

/-! ## The two poles: a constant map and the identity map -/

section Poles

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

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

/-- **A RUN IS PARAMETRIZED BY ONE POLICY THROUGHOUT.** Every step of a trajectory applies the same rule, and
nothing along the trajectory enters it. Carrier-general. -/
theorem the_run_carries_one_policy (S : Policy X) (c : Pt X → Pt X → Option Bool) (k : ℕ) :
    runPolicy S c (k + 1) = step S (runPolicy S c k) := rfl

/-- **THE BOTTOM POLE FIXES EVERY CONFIGURATION.** Every configuration whatever is invariant under it, so it
has no distinguished fixed point at all. Carrier-general. -/
theorem the_bottom_pole_fixes_everything (c : Pt X → Pt X → Option Bool) (k : ℕ) :
    runPolicy (takeNone : Policy X) c k = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [the_run_carries_one_policy, ih]
    exact step_takeNone c

/-- **AND SO A DEPARTURE IS NEVER UNDONE BY THE IDENTITY MAP.** Whatever configuration a perturbation leaves
it at, it stays there, so the invariance is preservation of wherever it happens to be and not restoration of
anything. Carrier-general. -/
theorem the_bottom_pole_never_restores {c d : Pt X → Pt X → Option Bool} (hne : d ≠ c) (k : ℕ) :
    runPolicy (takeNone : Policy X) d k ≠ c := by
  rw [the_bottom_pole_fixes_everything d k]
  exact hne

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

end Poles

/-! ## The mobile band, its two exits, and a period-two periodic orbit -/

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

theorem oneCell_mobile {a b : Pt X} (hab : a ≠ b) (v : Bool) :
    Mobile (oneCell a b v : Pt X → Pt X → Option Bool) :=
  mobile_iff.mpr ⟨⟨a, b, by rw [oneCell_at]; exact Option.some_ne_none _⟩,
    ⟨a, a, oneCell_elsewhere a b v (fun hq => hab hq.2)⟩⟩

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

/-- **THERE IS A TWO-STEP CYCLE.** The stance moves between two configurations and back, so the enlarged space
has orbits. Carrier-general, given two distinct points. -/
theorem there_is_a_cycle {a b : Pt X} (hab : a ≠ b) :
    applyStance (swapBetween a b) (oneCell a b true) = oneCell b a true
      ∧ applyStance (swapBetween a b) (oneCell b a true) = oneCell a b true := by
  refine ⟨applyStance_swapBetween_of_held ?_, applyStance_swapBetween_of_open ?_⟩
  · rw [oneCell_at]
    exact Option.some_ne_none _
  · exact oneCell_elsewhere b a true (fun hq => hab hq.1)

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

end Band


#print axioms release_of_dropped
#print axioms release_of_kept
#print axioms applyStance_of_dropped
#print axioms applyStance_of_kept_open
#print axioms forming_is_powerless_at_a_held_cell
#print axioms a_change_requires_a_release
#print axioms ofMask_formsNothing
#print axioms the_deflationary_stances_embed
#print axioms applyStance_ofMask_eq_step
#print axioms step_preserves_absence
#print axioms step_deflationary
#print axioms formsNothing_deflationary
#print axioms formsNothing_preserves_absence
#print axioms mem_heldCells
#print axioms mem_fillableCells
#print axioms oneCell_at
#print axioms oneCell_elsewhere
#print axioms punctured_hole
#print axioms punctured_elsewhere
#print axioms step_fixed_iff
#print axioms runPolicy_succ
#print axioms runPolicy_shift
#print axioms runPolicy_fixed
#print axioms step_bot
#print axioms runPolicy_bot
#print axioms strict_descent
#print axioms rest_within
#print axioms every_policy_reaches_a_rest
#print axioms the_criterion
#print axioms step_takeAll
#print axioms step_takeNone
#print axioms step_takeAt_at
#print axioms step_takeAt_elsewhere
#print axioms the_run_carries_one_policy
#print axioms the_bottom_pole_fixes_everything
#print axioms the_bottom_pole_never_restores
#print axioms the_stability_asymmetry
#print axioms heldCells_nonempty_iff
#print axioms fillableCells_nonempty_iff
#print axioms mobile_iff
#print axioms the_band_has_two_exits
#print axioms applyStance_dropAll
#print axioms applyStance_holdAll
#print axioms applyStance_formAll
#print axioms formAll_saturates
#print axioms formAll_fixes_the_saturated
#print axioms oneCell_mobile
#print axioms applyStance_swapBetween_of_held
#print axioms applyStance_swapBetween_of_open
#print axioms there_is_a_cycle
#print axioms an_invariant_band_without_a_resting_place
#print axioms the_two_extremes_are_distinct_failures
#print axioms restoreTo_returns_from_anywhere

end Chiralogy
