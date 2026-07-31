import Chiralogy.Model.AssemblageRelations
import Chiralogy.Model.Apophatic

/-! ARCHIVED (fully graduated). The stance layer's unified core.

GRADUATED to `Model/Stance` (the objects, the operators, the bookkeeping, the witnesses) and `Model/StanceContent`
(`keepSupported` and its two lemmas, `punctured_is_supported`). Spec 4.a.19, 4.a.20.

This file was itself the deduplication step: the arc had grown as five files re-deriving the same vocabulary,
21 names in more than one file, 52 declaration instances, no edge between any two. Collapsing them to one
definition per concept is what made graduation possible, and it caught two re-derivations of canonical:
`Saturated` was `isTotal` and `step_descends` was `partialization_le_c`. Both are now cited, not re-proved.

Typechecks standalone. -/

/-! # Experiment (LIVE): the stance layer's unified core

The stance arc grew as five separate files, each re-deriving the vocabulary it needed. The dependency map
measured the result: twenty one names defined in more than one file, fifty two declaration instances, and no
edge between any two of the five. This module is the deduplication: ONE definition per concept, which the five
now import.

The unification that makes it possible was already proved. A stance has two parts, what it releases and what it
forms; a policy is the special case that forms nothing. `applyStance_ofMask_eq_step` states the identity, and
`the_deflationary_stances_embed` is the same fact against the canonical move. So `step` is not a second operator,
it is `applyStance` at a stance that forms nothing.

Register-neutral throughout: no statement and no proof mentions any domain, and no name carries a register
term. The names used are policy, stance, release, form, take, held, fillable, mobile, deflationary and fixed.

The moves are the canonical ones. Releasing is `partialization` at the mask the rule names, and forming has the
shape of the derived fill: it writes only where nothing is held. Neither is a new primitive.

Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.StanceCore

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

end Witnesses

/-! ## The content-reading policy

The one policy in the layer that looks at what is committed rather than only at where. It is the single
definition the two content files share. -/

section Content

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- Decline wherever the two rows are held apart by present values, and on the diagonal; take elsewhere. -/
noncomputable def keepSupported : Policy X :=
  fun c x y => decide (x ≠ y ∧ ¬ presentCarried c x y)

theorem keepSupported_declines {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : presentCarried c x y) : keepSupported c x y = false := by
  simp [keepSupported, h]

theorem keepSupported_takes {c : Pt X → Pt X → Option Bool} {x y : Pt X} (hxy : x ≠ y)
    (h : ¬ presentCarried c x y) : keepSupported c x y = true := by
  simp [keepSupported, hxy, h]

end Content

#print axioms step_preserves_absence
#print axioms step_deflationary
#print axioms release_of_dropped
#print axioms release_of_kept
#print axioms applyStance_of_dropped
#print axioms applyStance_of_kept_open
#print axioms forming_is_powerless_at_a_held_cell
#print axioms a_change_requires_a_release
#print axioms ofMask_formsNothing
#print axioms the_deflationary_stances_embed
#print axioms applyStance_ofMask_eq_step
#print axioms formsNothing_deflationary
#print axioms formsNothing_preserves_absence
#print axioms mem_heldCells
#print axioms mem_fillableCells
#print axioms oneCell_at
#print axioms oneCell_elsewhere
#print axioms punctured_hole
#print axioms punctured_elsewhere
#print axioms punctured_is_supported
#print axioms keepSupported_declines
#print axioms keepSupported_takes

end Chiralogy.StanceCore
