import Chiralogy.Model.StanceContent

/-! ARCHIVED (partly graduated). Layers, what a surface reading reaches, and what keeping an unsupported cell
costs.

GRADUATED to `Model/Stance`: `a_fixed_release_forces_a_conflict`, the fully general lemma that fixing a
classification while releasing a held cell forces a conflict there (no support notion, no named construction).
To `Model/StanceContent`: `FullySupported`, `the_rule_opens_every_unsupported_cell`,
`ReleasesWhatTheRuleReleases`, `a_self_examining_maintainer_must_conflict`,
`a_self_examining_maintainer_is_order_detectable`, `the_trade_off_is_general`,
`the_supported_ground_never_lapses`, `the_inert_stance_is_not_a_third_arrangement`,
`the_supported_case_faces_neither_horn`. Spec 4.a.22.

The dichotomy closed. It was exhibited here on the `groundedBy` witness and flagged as not proved exhaustive;
the general statement is now canonical, for an arbitrary classification, an arbitrary unsupported held cell and
an arbitrary maintainer. THERE IS NO THIRD ARRANGEMENT. The granularity the exhibition left open turned out to
be the whole content: the trade-off is between keeping the cell standing through the maintainer's OWN
examination and staying conflict-free, and `the_inert_stance_is_not_a_third_arrangement` shows why the
self-examining hypothesis cannot be dropped rather than being decorative.

NOT GRADUATED, retained here as the record: the witness constructions and the projection they were built for.
`blockAB` and the concealment results (`the_resting_verdict_does_not_see_the_absence_layer`,
`the_absence_layer_survives`), `groundedBy` and the dismantling results
(`the_unsupported_ground_does_not_survive`), `maintain`, `pureForm` and the witness-level trade-off. These are
carrier-general and they verify, but they are instances of the graduated dichotomy plus the concealment scope,
and the concealment half is a short consequence of `keepSupported_fixed_iff` and `step_preserves_absence`
rather than a structure of its own.

Typechecks standalone. -/

/-! # Experiment (LIVE): layers, and what a surface reading can and cannot see

The stance layer is canonical. This build projects its dynamics one step further and asks whether the framework
structurally predicts LAYERED structure, whether a surface reading can fail to reach it, and whether a
presented ordering can rest on something that reading does not vindicate.

Nothing here aims at a register conclusion. The three questions are settled by derivation from the canonical
notions, and where the derivation refutes the expected shape that is reported as the finding.

Stances are exogenous: no operation takes a rule to a rule, and none is used. Every notion of a layer below is
a property of the CLASSIFICATION, built from the canonical support notions, which is what makes the derivation
possible without a new primitive.

Register-neutral throughout: no statement and no proof mentions any domain, and no name carries a register
term. The names used are layer, surface, ground, supported, absence-carried and released. All readings are in
the report only, and are flagged provisional.

Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.LayeredPathology

section Layers

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

/-! ## Part 1: what a layer can be

A rule cannot act on a rule, so a layer cannot be a rule under a rule. What IS available is a region of the
carrier: a set of rows, with the canonical support notions read on it. That needs no new primitive. -/

/-- Every distinct pair of rows in the region is held apart by present values. -/
def SupportedOn (S : Pt X → Prop) (c : Pt X → Pt X → Option Bool) : Prop :=
  ∀ x x' : Pt X, S x → S x' → x ≠ x' → presentCarried c x x'

/-- Some pair reaching into the region is distinguished only by what is absent. -/
def AbsenceCarriedInto (S : Pt X → Prop) (c : Pt X → Pt X → Option Bool) : Prop :=
  ∃ x x' : Pt X, S x' ∧ absenceCarried c x x'

/-- Hold every cell between two named rows, and nothing else. -/
def blockAB (a b : Pt X) : Pt X → Pt X → Option Bool :=
  fun x y => if (x = a ∨ x = b) ∧ (y = a ∨ y = b) then some (decide (x = y)) else none

theorem blockAB_inside (a b : Pt X) {x y : Pt X} (hx : x = a ∨ x = b) (hy : y = a ∨ y = b) :
    blockAB a b x y = some (decide (x = y)) := by simp [blockAB, hx, hy]

theorem blockAB_outside_row (a b : Pt X) {x : Pt X} (hx : ¬ (x = a ∨ x = b)) (y : Pt X) :
    blockAB a b x y = none := by simp [blockAB, hx]

theorem blockAB_outside_col (a b : Pt X) (x : Pt X) {y : Pt X} (hy : ¬ (y = a ∨ y = b)) :
    blockAB a b x y = none := by simp [blockAB, hy]

/-- The two rows of the block are held apart by present values, witnessed in the block's own column.
Carrier-general, given two distinct points. -/
theorem blockAB_supported {a b : Pt X} (hab : a ≠ b) :
    presentCarried (blockAB a b) a b := by
  refine ⟨a, true, false, ?_, ?_, by simp⟩
  · rw [blockAB_inside a b (Or.inl rfl) (Or.inl rfl)]; simp
  · rw [blockAB_inside a b (Or.inr rfl) (Or.inl rfl)]; simp [Ne.symm hab]

theorem blockAB_supported_symm {a b : Pt X} (hab : a ≠ b) :
    presentCarried (blockAB a b) b a := by
  refine ⟨a, false, true, ?_, ?_, by simp⟩
  · rw [blockAB_inside a b (Or.inr rfl) (Or.inl rfl)]; simp [Ne.symm hab]
  · rw [blockAB_inside a b (Or.inl rfl) (Or.inl rfl)]; simp

/-- **THE BLOCK IS A SUPPORTED SURFACE.** Carrier-general, given two distinct points. -/
theorem blockAB_surface_is_supported {a b : Pt X} (hab : a ≠ b) :
    SupportedOn (fun x => x = a ∨ x = b) (blockAB a b) := by
  rintro x x' (rfl | rfl) (rfl | rfl) hne
  · exact absurd rfl hne
  · exact blockAB_supported hab
  · exact blockAB_supported_symm hab
  · exact absurd rfl hne

/-- A row outside the block is never present anywhere. Carrier-general. -/
theorem blockAB_deep_row_is_empty {a b d : Pt X} (hd : ¬ (d = a ∨ d = b)) (y : Pt X) :
    blockAB a b d y = none := blockAB_outside_row a b hd y

/-- **AND A ROW OUTSIDE IT IS DISTINGUISHED FROM THE SURFACE ONLY BY WHAT IS ABSENT.** The two rows differ, and
no column holds them apart by present values, because the outside row holds nothing at all. Carrier-general,
given a point outside the block. -/
theorem blockAB_deep_is_absence_carried {a b d : Pt X}
    (hd : ¬ (d = a ∨ d = b)) : absenceCarried (blockAB a b) a d := by
  constructor
  · intro he
    have hc := congrFun he a
    rw [blockAB_inside a b (Or.inl rfl) (Or.inl rfl), blockAB_deep_row_is_empty hd] at hc
    exact Option.some_ne_none _ hc
  · rintro ⟨y, b1, b2, -, h2, -⟩
    rw [blockAB_deep_row_is_empty hd] at h2
    exact Option.some_ne_none _ h2.symm

/-- **SO A LAYER IS A REGION OF THE CARRIER, AND IT NEEDS NO NEW OBJECT.** One classification carries a
present-supported surface and, reaching out of it, a distinction held only by absence. Both notions are read
off the classification with the canonical support predicates; no rule acts on a rule anywhere.
Carrier-general, given two distinct points and a third outside them. -/
theorem layering_is_a_region_of_the_carrier {a b d : Pt X} (hab : a ≠ b)
    (hd : ¬ (d = a ∨ d = b)) :
    SupportedOn (fun x => x = a ∨ x = b) (blockAB a b)
      ∧ AbsenceCarriedInto (fun x => ¬ (x = a ∨ x = b)) (blockAB a b) :=
  ⟨blockAB_surface_is_supported hab, ⟨a, d, hd, blockAB_deep_is_absence_carried hd⟩⟩

/-! ## Part 2: what the surface reading can see -/

/-- **THE SUPPORT-READING RULE READS NOTHING BUT PRESENT SUPPORT.** Two classifications with the same present-support
relation receive the same mask, whatever else differs between them. Carrier-general. -/
theorem keepSupported_reads_only_presentCarried {c d : Pt X → Pt X → Option Bool}
    (h : ∀ x y : Pt X, presentCarried c x y ↔ presentCarried d x y) :
    (keepSupported : Policy X) c = keepSupported d := by
  funext x y
  simp only [keepSupported]
  exact decide_eq_decide.mpr (and_congr Iff.rfl (not_congr (h x y)))

/-- **AND IT NEVER TOUCHES A CELL THAT HOLDS NOTHING.** Canonical `step_preserves_absence`, recorded here
because it is half of what follows. Carrier-general. -/
theorem the_rule_does_not_touch_an_unheld_cell {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (h : c x y = none) : step (keepSupported : Policy X) c x y = none :=
  step_preserves_absence h

/-- The block rests: every cell it holds off the diagonal is held apart by present values. Carrier-general,
given two distinct points. -/
theorem blockAB_rests {a b : Pt X} (hab : a ≠ b) :
    step (keepSupported : Policy X) (blockAB a b) = blockAB a b := by
  refine (keepSupported_fixed_iff _).mpr (fun x y hxy hv => ?_)
  by_cases hx : x = a ∨ x = b
  · by_cases hy : y = a ∨ y = b
    · rcases hx with rfl | rfl
      · rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · exact blockAB_supported hab
      · rcases hy with rfl | rfl
        · exact blockAB_supported_symm hab
        · exact absurd rfl hxy
    · exact absurd (blockAB_outside_col a b x hy) hv
  · exact absurd (blockAB_outside_row a b hx y) hv

/-- The punctured classification rests and carries no absence-held distinction at all: every pair of distinct
rows is held apart by present values. Carrier-general, given two distinct points. -/
theorem punctured_has_no_absence_layer {a b : Pt X} (hab : a ≠ b) (x x' : Pt X) :
    ¬ absenceCarried (punctured a b) x x' := by
  intro h
  by_cases hxx : x = x'
  · exact h.1 (by rw [hxx])
  · exact h.2 (punctured_is_supported hab hxx)

theorem punctured_rests {a b : Pt X} (hab : a ≠ b) :
    step (keepSupported : Policy X) (punctured a b) = punctured a b :=
  (keepSupported_fixed_iff _).mpr (fun _ _ hxy _ => punctured_is_supported hab hxy)

/-- **THE SURFACE VERDICT DOES NOT SEE THE ABSENCE LAYER.** Two classifications at both of which the rule
comes to rest, one carrying a distinction held only by absence and one carrying none. Resting is the rule's own
verdict, and it is identical in the two cases, so the verdict does not distinguish them. Carrier-general, given
two distinct points and a third outside them. -/
theorem the_resting_verdict_does_not_see_the_absence_layer {a b d : Pt X} (hab : a ≠ b)
    (hd : ¬ (d = a ∨ d = b)) :
    step (keepSupported : Policy X) (blockAB a b) = blockAB a b
      ∧ absenceCarried (blockAB a b) a d
      ∧ step (keepSupported : Policy X) (punctured a b) = punctured a b
      ∧ ∀ x x' : Pt X, ¬ absenceCarried (punctured a b) x x' :=
  ⟨blockAB_rests hab, blockAB_deep_is_absence_carried hd,
   punctured_rests hab, punctured_has_no_absence_layer hab⟩

/-- **AND THE ABSENCE LAYER IS NOT ONLY UNSEEN, IT IS UNTOUCHED.** The classification is a fixed point, so the
distinction held only by absence survives every application of the rule. Carrier-general, given two distinct
points and a third outside them. -/
theorem the_absence_layer_survives {a b d : Pt X} (hab : a ≠ b) (hd : ¬ (d = a ∨ d = b)) (k : ℕ) :
    absenceCarried (runPolicy (keepSupported : Policy X) (blockAB a b) k) a d := by
  rw [runPolicy_fixed (blockAB_rests hab) k]
  exact blockAB_deep_is_absence_carried hd

/-! ## Part 3: a surface whose ground lies outside it -/

/-- Hold exactly two cells, both in one column outside the pair they separate. -/
def groundedBy (a b d : Pt X) : Pt X → Pt X → Option Bool :=
  fun x y => if y = d then (if x = a then some true else if x = b then some false else none) else none

theorem groundedBy_at_a {a b d : Pt X} : groundedBy a b d a d = some true := by simp [groundedBy]

theorem groundedBy_at_b {a b d : Pt X} (hab : a ≠ b) : groundedBy a b d b d = some false := by
  simp [groundedBy, Ne.symm hab]

theorem groundedBy_off_column {a b d : Pt X} (x : Pt X) {y : Pt X} (hy : y ≠ d) :
    groundedBy a b d x y = none := by simp [groundedBy, hy]

theorem groundedBy_other_row {a b d : Pt X} {x : Pt X} (hxa : x ≠ a) (hxb : x ≠ b) (y : Pt X) :
    groundedBy a b d x y = none := by
  by_cases hy : y = d
  · simp [groundedBy, hy, hxa, hxb]
  · simp [groundedBy, hy]

/-- **THE SURFACE PAIR IS GENUINELY HELD APART BY PRESENT VALUES.** Carrier-general, given two distinct points.
-/
theorem groundedBy_surface_is_supported {a b d : Pt X} (hab : a ≠ b) :
    presentCarried (groundedBy a b d) a b :=
  ⟨d, true, false, groundedBy_at_a, groundedBy_at_b hab, by simp⟩

/-- **BUT THE COLUMN THAT HOLDS IT APART IS NOT ITSELF HELD APART FROM IT.** The witnessing row holds nothing,
so no column separates it from the surface by present values. Carrier-general, given a witnessing point
distinct from the pair. -/
theorem groundedBy_ground_is_not_supported {a b d : Pt X} (hda : d ≠ a) (hdb : d ≠ b) :
    ¬ presentCarried (groundedBy a b d) a d := by
  rintro ⟨y, b1, b2, -, h2, -⟩
  rw [groundedBy_other_row hda hdb] at h2
  exact Option.some_ne_none _ h2.symm

/-- **SO THE RULE RELEASES EXACTLY THE CELLS THAT CARRY THE GROUND.** A held cell between rows that are
not held apart by present values is precisely what the rule takes. Carrier-general, given the three points
distinct. -/
theorem the_rule_releases_the_ground {a b d : Pt X} (hda : d ≠ a) (hdb : d ≠ b) :
    (keepSupported : Policy X) (groundedBy a b d) a d = true
      ∧ (groundedBy a b d) a d ≠ none :=
  ⟨keepSupported_takes (Ne.symm hda) (groundedBy_ground_is_not_supported hda hdb),
   by rw [groundedBy_at_a]; exact Option.some_ne_none _⟩

/-- **AND ONE APPLICATION EMPTIES THE WHOLE CLASSIFICATION.** Both held cells are ground cells and both are
released, so nothing at all is left. Carrier-general, given the three points distinct. -/
theorem groundedBy_is_emptied {a b d : Pt X} (hda : d ≠ a) (hdb : d ≠ b) :
    step (keepSupported : Policy X) (groundedBy a b d) = botC (Pt X) := by
  funext x y
  show step (keepSupported : Policy X) (groundedBy a b d) x y = none
  have hrow : ∀ z : Pt X, groundedBy a b d d z = none := groundedBy_other_row hda hdb
  have hnsd : ∀ z : Pt X, ¬ presentCarried (groundedBy a b d) z d := by
    intro z
    rintro ⟨w, b1, b2, -, h2, -⟩
    rw [hrow] at h2
    exact Option.some_ne_none _ h2.symm
  by_cases hy : y = d
  · by_cases hx : x = a
    · have hxy : x ≠ y := by rw [hx, hy]; exact Ne.symm hda
      have hns : ¬ presentCarried (groundedBy a b d) x y := by rw [hy]; exact hnsd x
      rw [step, partialization, if_pos (keepSupported_takes hxy hns)]
    · by_cases hx' : x = b
      · have hxy : x ≠ y := by rw [hx', hy]; exact Ne.symm hdb
        have hns : ¬ presentCarried (groundedBy a b d) x y := by rw [hy]; exact hnsd x
        rw [step, partialization, if_pos (keepSupported_takes hxy hns)]
      · exact step_preserves_absence (by rw [hy]; exact groundedBy_other_row hx hx' d)
  · exact step_preserves_absence (groundedBy_off_column x hy)

/-- **SO THE SURFACE DISTINCTION DOES NOT SURVIVE THE RULE.** Its ground was held and unsupported, the rule
takes exactly such cells, and once they are gone nothing holds the pair apart. A surface resting on an
unsupported ground is NOT stable: it is dismantled in one application, and dismantled from below.
Carrier-general, given the three points distinct. -/
theorem the_unsupported_ground_does_not_survive {a b d : Pt X} (hab : a ≠ b) (hda : d ≠ a)
    (hdb : d ≠ b) :
    presentCarried (groundedBy a b d) a b
      ∧ ¬ presentCarried (step (keepSupported : Policy X) (groundedBy a b d)) a b := by
  refine ⟨groundedBy_surface_is_supported hab, ?_⟩
  rw [groundedBy_is_emptied hda hdb]
  rintro ⟨y, b1, b2, h1, -, -⟩
  exact Option.some_ne_none _ h1.symm

/-- **AND IT IS NOT A RESTING PLACE.** Carrier-general, given the three points distinct. -/
theorem the_unsupported_ground_is_not_fixed {a b d : Pt X} (hda : d ≠ a) (hdb : d ≠ b) :
    step (keepSupported : Policy X) (groundedBy a b d) ≠ groundedBy a b d := by
  intro he
  have hc := congrFun (congrFun he a) d
  rw [groundedBy_is_emptied hda hdb, groundedBy_at_a] at hc
  exact Option.some_ne_none _ hc.symm

/-- **THE TWO CASES SIDE BY SIDE, AND THEY COME APART.** A distinction held only by absence at cells that hold
nothing is invisible to the rule AND untouched by it. A surface whose ground is held but unsupported is visible
to the rule in the only way that matters, and is dismantled. What survives unexamined is exactly what carries no
weight; what carries weight without support is exactly what does not survive. Carrier-general, given two
distinct points and a third outside them. -/
theorem what_survives_is_what_carries_nothing {a b d : Pt X} (hab : a ≠ b) (hda : d ≠ a)
    (hdb : d ≠ b) (hd : ¬ (d = a ∨ d = b)) :
    (step (keepSupported : Policy X) (blockAB a b) = blockAB a b
        ∧ absenceCarried (blockAB a b) a d)
      ∧ (presentCarried (groundedBy a b d) a b
        ∧ step (keepSupported : Policy X) (groundedBy a b d) = botC (Pt X)) :=
  ⟨⟨blockAB_rests hab, blockAB_deep_is_absence_carried hd⟩,
   ⟨groundedBy_surface_is_supported hab, groundedBy_is_emptied hda hdb⟩⟩

/-! ## Part 4: the forming arm, and whether the ground can be maintained

Everything above uses the emptying arm. The open it leaves is whether a two-directional stance can RE-LAY a
ground the examining rule strips, and so sustain the appearance by action rather than by concealment. -/

/-- Release wherever the examining rule would, and form a named classification back. -/
noncomputable def maintain (t : Pt X → Pt X → Option Bool) : Stance X :=
  ⟨keepSupported, fun _ x y => t x y⟩

/-- **A MAINTAINER FIXES WHATEVER IT TARGETS.** Wherever it releases it re-forms the target, and wherever it
does not release the cell already holds what the target holds. Carrier-general. -/
theorem maintain_fixes_its_target (t : Pt X → Pt X → Option Bool) :
    applyStance (maintain t) t = t := by
  funext x y
  by_cases hd : (keepSupported : Policy X) t x y = true
  · rw [applyStance_of_dropped (T := maintain t) hd]
    rfl
  · rw [Bool.not_eq_true] at hd
    by_cases hv : t x y = none
    · rw [applyStance_of_kept_open (T := maintain t) hd hv]
      rfl
    · rcases hb : t x y with - | v
      · exact absurd hb hv
      · rw [forming_is_powerless_at_a_held_cell (T := maintain t) hd hb]

/-- **SO THE UNSUPPORTED GROUND CAN BE RE-LAID, AND WHAT IS RE-LAID IS THE SAME UNSUPPORTED GROUND.** The
maintainer returns the classification unchanged, and the witnessing row is still held apart from the surface by
nothing. Forming does not convert a ground into a supported one; it reproduces exactly what it was given.
Carrier-general, given a witnessing point distinct from the pair. -/
theorem the_reformed_ground_is_still_unsupported {a b d : Pt X} (hda : d ≠ a) (hdb : d ≠ b) :
    applyStance (maintain (groundedBy a b d)) (groundedBy a b d) = groundedBy a b d
      ∧ ¬ presentCarried (groundedBy a b d) a d :=
  ⟨maintain_fixes_its_target _, groundedBy_ground_is_not_supported hda hdb⟩

/-- **AND THE ALTERNATION IS A TWO-STEP CYCLE.** Examination empties the ground, a restoring stance lays it
again, and the classification is back where it began. Carrier-general, given the three points distinct. -/
theorem the_alternation_is_a_two_cycle {a b d : Pt X} (hda : d ≠ a) (hdb : d ≠ b) :
    step (keepSupported : Policy X) (groundedBy a b d) = botC (Pt X)
      ∧ applyStance (restoreTo (groundedBy a b d)) (botC (Pt X)) = groundedBy a b d :=
  ⟨groundedBy_is_emptied hda hdb, restoreTo_returns_from_anywhere _ _⟩

/-! ### What the rest costs: inaction against action -/

/-- A classification every one of whose held cells is held apart by present values. -/
def FullySupported (c : Pt X → Pt X → Option Bool) : Prop :=
  ∀ x y : Pt X, x ≠ y → c x y ≠ none → presentCarried c x y

/-- **AT A FULLY SUPPORTED CLASSIFICATION THE EXAMINING RULE DECLINES EVERYWHERE IT HOLDS.** Its rest is rest by
INACTION: there is no cell the rule would take. Carrier-general. -/
theorem the_supported_ground_is_declined {c : Pt X → Pt X → Option Bool} (h : FullySupported c)
    {x y : Pt X} (hv : c x y ≠ none) : (keepSupported : Policy X) c x y = false := by
  by_cases hxy : x = y
  · simp [keepSupported, hxy]
  · exact keepSupported_declines (h x y hxy hv)

/-- **SO MAINTAINING A SUPPORTED GROUND IS CONFLICT-FREE.** The maintainer never both releases and forms the
same cell there, because it never releases a held cell at all. Carrier-general. -/
theorem maintaining_a_supported_ground_is_conflict_free {c : Pt X → Pt X → Option Bool}
    (h : FullySupported c) (x y : Pt X) : ¬ Conflicted (maintain c) c x y := by
  rintro ⟨hd, hf⟩
  have hd' : (keepSupported : Policy X) c x y = true := hd
  rw [the_supported_ground_is_declined h hf] at hd'
  exact absurd hd' (by simp)

/-- **WHILE MAINTAINING THE UNSUPPORTED GROUND IS CONFLICTED AT EXACTLY THE GROUND CELL.** The maintainer
releases there and forms there, in the same application, every application. Its rest is rest by ACTION.
Carrier-general, given the three points distinct. -/
theorem maintaining_the_false_ground_is_conflicted {a b d : Pt X} (hda : d ≠ a) (hdb : d ≠ b) :
    Conflicted (maintain (groundedBy a b d)) (groundedBy a b d) a d := by
  refine ⟨(the_rule_releases_the_ground hda hdb).1, ?_⟩
  show groundedBy a b d a d ≠ none
  rw [groundedBy_at_a]
  exact Option.some_ne_none _

/-- **THE ASYMMETRY, STATED.** A fully supported classification is fixed by the examining rule itself, with no
maintainer and no action anywhere. An unsupported ground is emptied by that same rule, and is fixed only by a
maintainer that acts at the unsupported cell in every application. Carrier-general, given a fully supported
classification and the three points distinct. -/
theorem the_supported_rests_the_unsupported_is_worked {c : Pt X → Pt X → Option Bool}
    (h : FullySupported c) {a b d : Pt X} (hda : d ≠ a) (hdb : d ≠ b) :
    step (keepSupported : Policy X) c = c
      ∧ (∀ x y : Pt X, c x y ≠ none → (keepSupported : Policy X) c x y = false)
      ∧ step (keepSupported : Policy X) (groundedBy a b d) = botC (Pt X)
      ∧ Conflicted (maintain (groundedBy a b d)) (groundedBy a b d) a d :=
  ⟨(keepSupported_fixed_iff c).mpr h, fun _ _ hv => the_supported_ground_is_declined h hv,
   groundedBy_is_emptied hda hdb, maintaining_the_false_ground_is_conflicted hda hdb⟩

/-! ### What the maintenance costs, and what it shows -/

/-- **THE MOMENT THE FORMING LAPSES THE GROUND IS GONE.** The maintainer with its forming removed is the
examining rule read as a stance, and one application of it empties the classification. Carrier-general, given
the three points distinct. -/
theorem the_maintenance_cannot_lapse {a b d : Pt X} (hda : d ≠ a) (hdb : d ≠ b) :
    applyStance (ofMask (keepSupported : Policy X)) (groundedBy a b d) = botC (Pt X) := by
  rw [applyStance_ofMask_eq_step]
  exact groundedBy_is_emptied hda hdb

/-- **AND THE MAINTENANCE LEAVES A SIGNATURE THAT DOES NOT DEPEND ON CATCHING IT MID-CYCLE.** Maintaining a
supported classification gives the same result under either within-application order, because it is
conflict-free there. Maintaining the unsupported ground does not: the two orders disagree at the ground cell.
So a maintained ground is order-dependent and a supported one is not, which is visible from one application and
not from a phase. Carrier-general, given a fully supported classification and the three points distinct. -/
theorem the_maintenance_is_order_dependent {c : Pt X → Pt X → Option Bool} (h : FullySupported c)
    {a b d : Pt X} (hda : d ≠ a) (hdb : d ≠ b) :
    applyStance (maintain c) c = applyStanceRev (maintain c) c
      ∧ applyStance (maintain (groundedBy a b d)) (groundedBy a b d) a d
          ≠ applyStanceRev (maintain (groundedBy a b d)) (groundedBy a b d) a d := by
  refine ⟨(the_orders_agree_iff_no_conflict (maintain c) c).mpr (fun x y hd => ?_), ?_⟩
  · by_contra hf
    exact maintaining_a_supported_ground_is_conflict_free h x y ⟨hd, hf⟩
  · exact the_conflict_admits_no_neutral_value (maintaining_the_false_ground_is_conflicted hda hdb)

/-! ## Part 5: is the self-collision avoidable

The maintainer above is conflicted because its release IS the examining rule. The release is a free parameter,
so the question is whether some other release holds the ground steady while forming nothing where it releases,
and thereby escapes the order-dependence signature. -/

/-- **A MAINTAINER THAT KEEPS THE GROUND MUST SUPPLY ITS VALUE BY FORMING, IF IT RELEASES THERE.** Once a stance
releases a cell, what stands there afterwards is whatever it forms, so fixing the classification forces the
form to carry the ground's own value. Carrier-general. -/
theorem a_releasing_maintainer_must_form_the_ground {T : Stance X}
    {a b d : Pt X} (hfix : applyStance T (groundedBy a b d) = groundedBy a b d)
    (hd : T.drop (groundedBy a b d) a d = true) :
    T.form (groundedBy a b d) a d = some true := by
  have hc := congrFun (congrFun hfix a) d
  rw [applyStance_of_dropped hd, groundedBy_at_a] at hc
  exact hc

/-- **SO ANY MAINTAINER THAT RELEASES THE GROUND IS SELF-CONFLICTED THERE.** It releases the cell and forms it
back in the same application, which is exactly the collision the two within-application orders disagree about.
The signature is unavoidable for a stance that both strips and keeps. Carrier-general. -/
theorem a_maintainer_that_releases_the_ground_must_conflict {T : Stance X}
    {a b d : Pt X} (hfix : applyStance T (groundedBy a b d) = groundedBy a b d)
    (hd : T.drop (groundedBy a b d) a d = true) :
    Conflicted T (groundedBy a b d) a d := by
  refine ⟨hd, ?_⟩
  rw [a_releasing_maintainer_must_form_the_ground hfix hd]
  exact Option.some_ne_none _

/-! ### But a stance that forms without releasing is conflict-free -/

/-- Form a named classification into whatever is open, and release nothing at all. -/
def pureForm (t : Pt X → Pt X → Option Bool) : Stance X :=
  ⟨fun _ _ _ => false, fun _ x y => t x y⟩

/-- **IT IS CONFLICT-FREE, AND GLOBALLY SO.** It releases nothing anywhere, so it forms nothing where it
releases, vacuously. Carrier-general. -/
theorem pureForm_is_conflict_free (t : Pt X → Pt X → Option Bool) :
    ConflictFree (pureForm t) := by
  intro c x y h
  exact absurd h (by simp [pureForm])

/-- **AND IT LAYS ITS TARGET INTO AN EMPTY CLASSIFICATION IN ONE APPLICATION.** Every cell is open there, so
forming needs no release. Carrier-general. -/
theorem pureForm_relays_from_the_empty (t : Pt X → Pt X → Option Bool) :
    applyStance (pureForm t) (botC (Pt X)) = t := by
  funext x y
  rw [applyStance_of_kept_open (T := pureForm t) rfl rfl]
  rfl

theorem pureForm_fixes_its_target (t : Pt X → Pt X → Option Bool) :
    applyStance (pureForm t) t = t := by
  funext x y
  by_cases hv : t x y = none
  · rw [applyStance_of_kept_open (T := pureForm t) rfl hv]
    rfl
  · rcases hb : t x y with - | v
    · exact absurd hb hv
    · rw [forming_is_powerless_at_a_held_cell (T := pureForm t) rfl hb]

/-- **SO IT IS ORDER-INVARIANT, AND THE SIGNATURE DOES NOT SEE IT.** Canonical
`conflictFree_is_order_invariant`. Carrier-general. -/
theorem the_conflict_free_maintainer_is_order_invariant (t c : Pt X → Pt X → Option Bool) :
    applyStance (pureForm t) c = applyStanceRev (pureForm t) c :=
  conflictFree_is_order_invariant (pureForm_is_conflict_free t) c

/-- **AND THE COMPOSITE SUSTAINS THE UNSUPPORTED GROUND.** Examination empties it, the conflict-free stance
lays it back, and the round trip returns exactly where it began. So a conflict-free maintainer of an
unsupported ground EXISTS: the collision is avoided by splitting the stripping and the re-laying into two
applications, and the re-laying half releases nothing. Carrier-general, given the three points distinct. -/
theorem the_composite_sustains_the_unsupported_ground {a b d : Pt X} (hda : d ≠ a) (hdb : d ≠ b) :
    applyStance (pureForm (groundedBy a b d)) (step (keepSupported : Policy X) (groundedBy a b d))
      = groundedBy a b d := by
  rw [groundedBy_is_emptied hda hdb]
  exact pureForm_relays_from_the_empty _

/-! ### What the split costs, and what still shows -/

/-- **BUT THE COMPOSITE PASSES THROUGH THE EMPTY CLASSIFICATION.** The ground is genuinely absent between the
two applications: the split buys order-invisibility at the price of the ground not being there at every step.
Carrier-general, given the three points distinct. -/
theorem the_composite_passes_through_the_empty {a b d : Pt X} (hda : d ≠ a) (hdb : d ≠ b) :
    step (keepSupported : Policy X) (groundedBy a b d) = botC (Pt X)
      ∧ (botC (Pt X) : Pt X → Pt X → Option Bool) ≠ groundedBy a b d := by
  refine ⟨groundedBy_is_emptied hda hdb, fun he => ?_⟩
  have hc := congrFun (congrFun he a) d
  rw [groundedBy_at_a] at hc
  exact Option.some_ne_none _ hc.symm

/-- **WHERE A SUPPORTED CLASSIFICATION NEVER LAPSES.** Examination with the forming removed leaves it exactly
where it was, so it is present at every step without anything laying it back. Carrier-general. -/
theorem the_supported_ground_never_lapses {c : Pt X → Pt X → Option Bool} (h : FullySupported c) :
    applyStance (ofMask (keepSupported : Policy X)) c = c := by
  rw [applyStance_ofMask_eq_step]
  exact (keepSupported_fixed_iff c).mpr h

/-- **THE TRADE-OFF, STATED.** A maintainer that releases the ground is self-conflicted there, and the two
within-application orders disagree at that cell. A maintainer that avoids the collision avoids it by releasing
nothing, and then something else must do the stripping, so the ground is absent in between. Either the ground
stands at every step and the collision shows, or the collision is avoided and the ground does not stand at
every step. A supported classification does neither: it is fixed by examination itself, with no maintainer and
no lapse. Carrier-general, given a fully supported classification and the three points distinct. -/
theorem the_trade_off {c : Pt X → Pt X → Option Bool} (h : FullySupported c)
    {a b d : Pt X} (hda : d ≠ a) (hdb : d ≠ b) :
    (∀ T : Stance X, applyStance T (groundedBy a b d) = groundedBy a b d →
        T.drop (groundedBy a b d) a d = true → Conflicted T (groundedBy a b d) a d)
      ∧ ConflictFree (pureForm (groundedBy a b d))
      ∧ step (keepSupported : Policy X) (groundedBy a b d) = botC (Pt X)
      ∧ applyStance (ofMask (keepSupported : Policy X)) c = c :=
  ⟨fun _ hfix hd => a_maintainer_that_releases_the_ground_must_conflict hfix hd,
   pureForm_is_conflict_free _, groundedBy_is_emptied hda hdb,
   the_supported_ground_never_lapses h⟩

/-! ## Part 6: the trade-off, off the witness

Part 5 exhibited the dichotomy on one construction. This part states it for an arbitrary classification, an
arbitrary unsupported held cell and an arbitrary maintainer, and pins the granularity the exhibition left
open. -/

/-- **FIXING A CLASSIFICATION WHILE RELEASING A HELD CELL FORCES A CONFLICT THERE.** Fully general: no support
notion, no named construction. Once a stance releases a cell, what stands there afterwards is whatever it
forms, so if the classification is unchanged the form must carry the cell's own value, and a stance that
releases and forms the same cell is conflicted at it. Carrier-general. -/
theorem a_fixed_release_forces_a_conflict {T : Stance X} {c : Pt X → Pt X → Option Bool}
    {x y : Pt X} (hfix : applyStance T c = c) (hv : c x y ≠ none) (hd : T.drop c x y = true) :
    Conflicted T c x y := by
  refine ⟨hd, ?_⟩
  have hc := congrFun (congrFun hfix x) y
  rw [applyStance_of_dropped hd] at hc
  rw [hc]
  exact hv

/-- **AND THE EXAMINING RULE LEAVES NO UNSUPPORTED CELL HELD.** The held hypothesis turns out to be
unnecessary: off the diagonal, an unsupported cell is open after one application whether or not it was held
before. Carrier-general. -/
theorem the_rule_opens_every_unsupported_cell {c : Pt X → Pt X → Option Bool} {x y : Pt X}
    (hxy : x ≠ y) (hns : ¬ presentCarried c x y) :
    step (keepSupported : Policy X) c x y = none := by
  rw [step, partialization, if_pos (keepSupported_takes hxy hns)]

/-- A maintainer that does its own examining: it releases at least wherever the examining rule would. -/
def ReleasesWhatTheRuleReleases (S : Stance X) (c : Pt X → Pt X → Option Bool) : Prop :=
  ∀ x y : Pt X, (keepSupported : Policy X) c x y = true → S.drop c x y = true

/-- **SO A MAINTAINER THAT DOES ITS OWN EXAMINING MUST COLLIDE AT EVERY UNSUPPORTED HELD CELL.** This is the
seal, carrier-general: not for one construction but for ANY stance that both fixes the classification and
strips what the examining rule strips. Carrier-general. -/
theorem a_self_examining_maintainer_must_conflict {S : Stance X} {c : Pt X → Pt X → Option Bool}
    (hstrip : ReleasesWhatTheRuleReleases S c) (hfix : applyStance S c = c)
    {x y : Pt X} (hxy : x ≠ y) (hv : c x y ≠ none) (hns : ¬ presentCarried c x y) :
    Conflicted S c x y :=
  a_fixed_release_forces_a_conflict hfix hv (hstrip x y (keepSupported_takes hxy hns))

/-- **AND THEN THE TWO WITHIN-APPLICATION ORDERS DISAGREE THERE.** Canonical
`the_conflict_admits_no_neutral_value`, so a self-examining maintainer of an unsupported cell is
order-detectable at that cell. Carrier-general. -/
theorem a_self_examining_maintainer_is_order_detectable {S : Stance X}
    {c : Pt X → Pt X → Option Bool} (hstrip : ReleasesWhatTheRuleReleases S c)
    (hfix : applyStance S c = c) {x y : Pt X} (hxy : x ≠ y) (hv : c x y ≠ none)
    (hns : ¬ presentCarried c x y) :
    applyStance S c x y ≠ applyStanceRev S c x y :=
  the_conflict_admits_no_neutral_value
    (a_self_examining_maintainer_must_conflict hstrip hfix hxy hv hns)

/-- **THE DICHOTOMY, CARRIER-GENERAL.** At any unsupported held cell of any classification, any maintainer that
fixes it either collides there, and is order-detectable there, or does not release there, and then it is not
the thing doing the examining, since the examining rule opens that very cell. There is no third arrangement
that keeps such a cell standing through its own examination without colliding. Carrier-general. -/
theorem the_trade_off_is_general {S : Stance X} {c : Pt X → Pt X → Option Bool}
    (hfix : applyStance S c = c) {x y : Pt X} (hxy : x ≠ y) (hv : c x y ≠ none)
    (hns : ¬ presentCarried c x y) :
    (Conflicted S c x y ∧ applyStance S c x y ≠ applyStanceRev S c x y)
      ∨ (S.drop c x y = false ∧ step (keepSupported : Policy X) c x y = none) := by
  by_cases hd : S.drop c x y = true
  · have hcf := a_fixed_release_forces_a_conflict hfix hv hd
    exact Or.inl ⟨hcf, the_conflict_admits_no_neutral_value hcf⟩
  · rw [Bool.not_eq_true] at hd
    exact Or.inr ⟨hd, the_rule_opens_every_unsupported_cell hxy hns⟩

/-- **THE SELF-EXAMINING HYPOTHESIS CANNOT BE DROPPED, AND WHAT DROPPING IT MEANS.** The stance that keeps
whatever it is handed fixes every classification and is conflict-free everywhere, so it does keep an
unsupported cell standing without colliding. It is not a counterexample: at such a cell the examining rule
would release and this stance does not, so it examines nothing. A stance that examines nothing maintains
nothing. Carrier-general. -/
theorem the_inert_stance_is_not_a_third_arrangement {c : Pt X → Pt X → Option Bool}
    {x y : Pt X} (hxy : x ≠ y) (hns : ¬ presentCarried c x y) :
    applyStance (holdAll : Stance X) c = c
      ∧ ConflictFree (holdAll : Stance X)
      ∧ ¬ ReleasesWhatTheRuleReleases (holdAll : Stance X) c := by
  refine ⟨applyStance_holdAll c, fun _ _ _ h => absurd h (by simp [holdAll]), fun hstrip => ?_⟩
  exact absurd (hstrip x y (keepSupported_takes hxy hns)) (by simp [holdAll])

/-- **AND THE SUPPORTED CASE FACES NEITHER HORN.** A fully supported classification is fixed by the examining
rule read as a stance, which releases nothing and forms nothing, so it neither collides nor lapses.
Carrier-general. -/
theorem the_supported_case_faces_neither_horn {c : Pt X → Pt X → Option Bool}
    (h : FullySupported c) :
    applyStance (ofMask (keepSupported : Policy X)) c = c
      ∧ ConflictFree (ofMask (keepSupported : Policy X)) :=
  ⟨the_supported_ground_never_lapses h, fun _ _ _ _ => rfl⟩

end Layers

/-! ## THE VERDICTS

PART 1: A LAYER IS A REGION OF THE CARRIER, AND IT NEEDS NO NEW OBJECT.

The brief offered three readings of layering and the constraint settles two of them immediately. A rule cannot
act on a rule, so a layer is not a rule under a rule; that reading is unavailable and no attempt is made at it.
What IS available is the third thing the brief did not separate out: a layer is a REGION OF THE CARRIER, a set
of rows, with the canonical support notions read on it.

`layering_is_a_region_of_the_carrier` exhibits one classification carrying both at once: a surface region whose
every distinct pair is held apart by PRESENT values (`blockAB_surface_is_supported`), and reaching out of that
region a pair distinguished only by what is ABSENT (`blockAB_deep_is_absence_carried`). Both are read off the
classification with `presentCarried` and `absenceCarried`, which were already canonical. NO NEW PRIMITIVE, and
nothing anywhere takes a rule to a rule.

So layering is SPATIAL, in the precise sense that the layers are regions of the carrier and not levels of rule.

PART 2: THE SURFACE VERDICT IS BLIND TO THE ABSENCE LAYER, AND DOES NOT DISTURB IT.

`keepSupported_reads_only_presentCarried` is the mechanism, and it is immediate once stated: the health rule's
mask is a function of the present-support relation alone. Anything two classifications share in present-support
they share in the rule's response, whatever else differs.

`the_resting_verdict_does_not_see_the_absence_layer` is the test and it comes out positive. Two classifications
at both of which the rule COMES TO REST, one carrying a distinction held only by absence and one carrying none
at all. Resting is the rule's own verdict of health, and it is the same verdict in both cases. THE VERDICT DOES
NOT DISTINGUISH THEM.

`the_absence_layer_survives` sharpens it from unseen to untouched: the classification is a fixed point, so the
absence-held distinction survives every application, without limit. The rule does not merely fail to report it,
it never acts on it. Half of that is canonical and worth naming: the rule never touches a cell that holds
nothing (`the_rule_does_not_touch_an_unheld_cell`, which is `step_preserves_absence`).

SO CONCEALMENT IS A STRUCTURAL PREDICTION, with a precise scope: what is concealed is structure held only by
absence AT CELLS THAT HOLD NOTHING.

PART 3: AND THAT SCOPE IS EXACTLY WHAT REFUTES THE EXPECTED SHAPE.

The brief expected a presented ordering that looks grounded on the surface, is actually held by what is not
said underneath, and is STABLE, maintained by the same stability that makes failure keep damage. The derivation
refutes the last part, and refutes it from the framework's own dynamics.

`groundedBy` is the construction the brief describes. A pair genuinely held apart by present values
(`groundedBy_surface_is_supported`), whose only witness lies in a column OUTSIDE the pair, and whose witnessing
row is itself held apart from the surface by nothing at all (`groundedBy_ground_is_not_supported`). That is a
surface that presents as grounded, resting on something the surface reading does not vindicate.

It is not stable. `the_rule_releases_the_ground`: a held cell between rows not held apart by present values is
PRECISELY what the health rule takes, and the ground cells are exactly of that kind. `groundedBy_is_emptied`:
one application removes every held cell. `the_unsupported_ground_does_not_survive`: the surface distinction,
real before the application, is GONE after it, because what held it apart has been released.
`the_unsupported_ground_is_not_fixed` records the same thing as the failure of rest.

So the framework does NOT predict a stable false ordering. It predicts the opposite: A SURFACE WHOSE GROUND IS
LOAD-BEARING AND UNSUPPORTED IS DISMANTLED, AND DISMANTLED FROM BELOW, IN ONE APPLICATION.

`what_survives_is_what_carries_nothing` puts the two cases together and states the line the derivation actually
draws. Structure held only by absence at cells holding nothing is invisible and permanent. A ground that is
held but unsupported is not concealed at all in the way that matters: the rule reaches it, because reaching
held-and-unsupported cells is the whole of what the rule does. WHAT SURVIVES UNEXAMINED IS EXACTLY WHAT CARRIES
NO WEIGHT, AND WHAT CARRIES WEIGHT WITHOUT SUPPORT IS EXACTLY WHAT DOES NOT SURVIVE.

PART 4: THE FORMING ARM, AND THE CORRECTION IT FORCES.

The previous parts used the emptying arm only. With the forming arm the three readings the brief posed come
apart, and the one that survives is not the one the brief expected.

READING (iii) IS REFUTED FIRST. `the_reformed_ground_is_still_unsupported`: the ground can be re-laid, and what
is re-laid is the SAME classification, whose witnessing row is still held apart from the surface by nothing.
Forming does not convert a ground into a supported one. It reproduces exactly what it is given, because
`maintain` forms its target and nothing else.

READING (i) IS AVAILABLE. `the_alternation_is_a_two_cycle`: examination empties the ground, a restoring stance
lays it again, and the classification is back where it began. So a false grounding CAN be carried as a cycle.

BUT READING (ii) IS REFUTED IN THE FORM THE BRIEF STATED IT, AND THIS IS THE FINDING. The brief expected the
false ground to have NO resting place, to be perpetual work with no fixed point. It has one.
`maintain_fixes_its_target` shows a maintainer fixes WHATEVER it targets, the unsupported ground included. So
"the false ground never rests" is simply false, and any reading resting on it is unsupported.

WHAT IS TRUE IS A DIFFERENT ASYMMETRY, AND IT IS SHARPER. `the_supported_rests_the_unsupported_is_worked` puts
the two side by side. A fully supported classification is fixed BY THE EXAMINING RULE ITSELF, with no maintainer
at all, and `the_supported_ground_is_declined` says why: at such a classification the rule DECLINES at every
cell it holds. Its rest is rest by INACTION, and there is nothing for a maintainer to do. The unsupported
ground is emptied by that same rule, and is fixed only by a maintainer that is CONFLICTED at the ground cell
(`maintaining_the_false_ground_is_conflicted`), releasing and re-forming there in every single application. Its
rest is rest by ACTION.

SO THE DISTINCTION IS NOT FIXED-POINT AGAINST NO-FIXED-POINT. BOTH REST. THE DISTINCTION IS WHETHER THE REST
COSTS ANYTHING: a supported ground is left alone, an unsupported one is continuously released and re-laid, and
the two are fixed points of different things.

`the_maintenance_cannot_lapse` prices it exactly. The maintainer with its forming removed is the examining rule
read as a stance, and one application of it empties the classification. There is no partial lapse and no decay:
the ground is gone in one step.

PART 5: WHETHER THE MAINTENANCE CAN HIDE, AND IT CANNOT.

`maintaining_a_supported_ground_is_conflict_free` and `maintaining_the_false_ground_is_conflicted` give the
signature, and `the_maintenance_is_order_dependent` draws it out. Maintaining a supported classification gives
the same result under EITHER within-application order, because it never releases and forms the same cell.
Maintaining the unsupported ground does not: the two orders disagree at exactly the ground cell.

So the maintenance is detectable, and NOT in the way the brief's phase question anticipated. One does not have
to catch the cycle at the stripped phase. The maintained ground and the supported one differ in a single
application, by whether the order of the two directions matters at all. A ground that has to be re-laid is a
ground at which the two directions collide, and collision is exactly what the order-invariance test sees.

This also separates the two concealments cleanly. Inert absence hides because nothing acts on it (Part 2). A
maintained false ground does not hide at all in that sense: it is acted on twice per application, and the
acting is what shows.

PART 7: IS THE SELF-COLLISION AVOIDABLE. THE ANSWER IS CONDITIONAL, AND THE CONDITION IS THE INTERESTING PART.

The maintainer of Part 4 was conflicted because its release WAS the examining rule. The release is a free
parameter, so the seal-or-break question is whether some other release keeps the ground while forming nothing
where it releases.

THE SEAL HALF HOLDS, AND IT IS FORCED. `a_releasing_maintainer_must_form_the_ground`: once a stance releases a
cell, what stands there afterwards is whatever it forms, so fixing the classification forces the form to carry
the ground's own value. `a_maintainer_that_releases_the_ground_must_conflict` draws the consequence for ANY
stance whatever, not for the one construction of Part 4: a stance that fixes the unsupported ground AND
releases it is self-conflicted at that cell. There is no clever release that both strips and keeps without
colliding with itself.

THE BREAK HALF ALSO HOLDS, AND IT IS THE HONEST ANSWER TO THE QUESTION AS ASKED. `pureForm` releases nothing at
all and forms a named classification into whatever is open. It is CONFLICT-FREE globally
(`pureForm_is_conflict_free`), hence ORDER-INVARIANT (`the_conflict_free_maintainer_is_order_invariant`), so
the signature of Part 5 does not see it. And it works: `the_composite_sustains_the_unsupported_ground` shows
examination empties the ground and this conflict-free stance lays it straight back, the round trip returning
exactly where it began.

SO A CONFLICT-FREE MAINTAINER OF AN UNSUPPORTED GROUND EXISTS, and the order-dependence signature is EVADABLE.
The tidier answer, that keeping a false ground is always self-contradictory and therefore always legible by
that test, is refuted.

HOW THE TWO HALVES FIT. They are not in tension: they partition by whether one stance does both jobs. A stance
that strips and keeps in ONE application must collide, because it must release the cell and put the value back
in the same act. Split the two jobs across TWO applications and the keeping half releases nothing, so it cannot
collide. The collision is a property of doing both at once, not of keeping a false ground as such.

PART 8: WHAT THE SPLIT COSTS, AND THE SIGNATURE THAT SURVIVES.

`the_composite_passes_through_the_empty` is the price. Between the two applications the ground is GENUINELY
ABSENT: the intermediate classification is the empty one, and it is not the ground. The split buys
order-invisibility by giving up the ground standing at every step.

`the_supported_ground_never_lapses` is the contrast, and it is the signature that survives every evasion.
Examination with the forming removed leaves a fully supported classification exactly where it was. It is
present at every step, with no maintainer and no lapse.

`the_trade_off` states the whole thing. EITHER the ground stands at every step, and then the maintainer
released and re-formed it in one act and the collision shows; OR the collision is avoided by splitting, and
then the ground does not stand at every step. A supported classification does neither, because it is fixed by
examination itself.

So the fingerprint is not the collision. The collision is evadable. What is not evadable is that an unsupported
ground is not fixed by examination, and everything that follows from that: either something acts at it in the
same breath as the stripping, or it is gone in between. The invariant signature is the one the earlier build
already had, `the_maintenance_cannot_lapse`, now seen to be the robust one: remove the forming and the ground
is gone in a single application, whereas removing it changes nothing at a supported classification.

PART 9: ASSEMBLED.

LAYERING: yes, and it is spatial. Regions of the carrier, canonical support notions read on them, no new object,
no rule acting on a rule.

CONCEALMENT: yes, with a scope the derivation fixes rather than the register. Absence-held structure at unheld
cells is invisible to the surface verdict and untouched by the surface action, permanently.

A FALSE GROUNDING SUSTAINED BY CONCEALMENT: NO. The construction is definable and the examining rule destroys
it in one application. The very property that makes the rule blind to the absence layer, that it reads present
support, is what makes it destroy an unsupported ground: it releases held cells that are not present-supported,
and an unsupported ground is made of exactly those.

A FALSE GROUNDING SUSTAINED BY MAINTENANCE: YES, AND AT A PRICE THAT IS ITSELF STRUCTURAL. It can be re-laid,
it can be carried as a cycle, and it can even be a fixed point. What it cannot be is left alone. A supported
ground is fixed by the examining rule with the rule declining everywhere it holds; an unsupported one is fixed
only under continuous release-and-re-forming at the very cells that are unsupported. The rest is real in both
cases and identical in neither: one is rest by inaction, the other rest by action.

AND THE MAINTENANCE HIDES FROM THE ORDER TEST IF IT IS WILLING TO PAY FOR IT. A stance that strips and keeps in
one act is conflicted and the orders disagree there. A conflict-free maintainer exists and evades that test
entirely, but only by splitting the jobs, and then the ground is absent between the two applications. The
signature that survives both is simpler and blunter: an unsupported ground is not fixed by examination, so
remove the forming and it is gone in one application, where a supported classification is unchanged.

WHAT THE STABILITY INVERSION DOES AND DOES NOT GIVE. The inversion says a rule that keeps everything keeps
whatever it is handed including damage. That is a fact about the KEEPING rule. It does not transfer to the
examining rule, and the projection that a concealed layer would be maintained by the same stability does not go
through: under the examining rule the concealed layer is maintained only where it is inert, and destroyed where
it bears weight.

REGISTER READINGS. Report only, provisional, and the OUTPUT of the derivation rather than its input. They are
supplied by the register and are defeasible.

  ON WHAT HIDES. What survives unexamined is what nothing rests on. A commitment that is doing no work can sit
  indefinitely below a surface that reads only what is actually asserted, because the reading is of what is
  asserted and the commitment asserts nothing. That much the framework does predict, and it predicts it is
  permanent, not merely likely.

  ON WHAT DOES NOT HIDE. An arrangement that presents as grounded while its ground is unexamined does NOT
  persist by concealment. The moment the ground is load-bearing it is held, and being held and unvindicated is
  exactly the condition the examining rule acts on. Such an arrangement comes apart from below, in one move.

  ON WHAT IT TAKES TO KEEP ONE ANYWAY, WHICH IS THE CORRECTED RESULT. It can nonetheless be kept, and the
  framework says precisely what keeping it costs. It must be re-laid at every examination, at exactly the places
  that are unvindicated, and the re-laying cannot lapse for one step without the whole thing going. A grounded
  arrangement is not kept at all: it is simply left alone, because there is nothing at it for examination to
  take. The difference between the two is not that one settles and the other cannot. Both settle. The difference
  is that one settles by being let be and the other only while something keeps putting it back.

  ON WHY IT SHOWS, AND ON THE LIMIT OF THAT. If the keeping is done in one act, it is a collision at a single
  place, the same cells released and re-laid together, and that is exactly what an order-invariance test
  detects. But the collision can be avoided by doing the two things separately, and then nothing about the
  keeping act itself gives it away. What cannot be avoided is cruder: the arrangement is not self-standing, so
  either something is acting at it in the same breath as the examination, or there is a moment when it is not
  there. It cannot both stand unexamined at every moment and leave no trace in the act that keeps it.

  ON THE HONEST SHAPE OF THIS. The tidy version, that holding up an ungrounded arrangement is necessarily
  self-contradictory at the ungrounded place and therefore always exposable by that one test, is FALSE. It is
  exposable by that test only when the same act both examines and repairs. Split the roles and the repair looks
  entirely ordinary. The thing that does not go away is not a contradiction in the repairer; it is that the
  arrangement needs a repairer at all.

  COGNITION. A view whose surface distinctions are drawn by things one can actually exhibit, but whose reason
  for drawing them is something one has never said, is not a stable self-deception on this account. It is
  unstable. What is stable is the unexamined material that supports nothing: that can be carried forever and no
  amount of the kind of self-examination modelled here will surface it, because there is nothing there for the
  examination to catch hold of.

  ON THE ASYMMETRY. The two findings are one fact seen twice. The surface reading acts on held-and-unsupported
  cells and on nothing else. So it cannot see inert absence, and it cannot fail to demolish load-bearing
  absence. A reading that could catch the first would have to be a different reading, and the framework does
  not supply one.

AXIOM PROFILE AND GRADUATION. Every result is at baseline or below. Graduation is NOT proposed: the positive
results are short consequences of `keepSupported_fixed_iff`, `step_preserves_absence` and the canonical Orders
section, and the rest are refutations rather than structures. Four are flagged as substantive and
carrier-general: `the_resting_verdict_does_not_see_the_absence_layer`, the concealment;
`the_unsupported_ground_does_not_survive`, the refutation of concealed stability;
`the_supported_rests_the_unsupported_is_worked`, the corrected asymmetry between rest by inaction and rest by
action; `the_maintenance_is_order_dependent`, the signature that makes a one-act maintenance legible; and
`the_trade_off`, which shows that signature is evadable and says what is paid for evading it.

WHAT REMAINS OPEN

1. Concealment is shown for absence-held structure at unheld cells. Whether any rule definable in the canonical
   space detects it is not asked, and the answer is presumably no for the same reason the health rule fails.
2. The ground here is a single column and the surface a single pair. Whether a deeper chain, a ground whose own
   ground is supported, behaves differently is not derived.
3. Whether a conflict-free maintainer exists is now settled: one does (`pureForm`), at the cost of the ground
   lapsing between applications. What is NOT settled is whether some third arrangement keeps the ground present
   at every step AND avoids the collision; the trade-off is exhibited on this construction and is not proved
   exhaustive.
4. Costs are compared per application, not summed over a run. There is no measure of how much maintenance a
   given false ground takes, only that it takes some at every step.
5. Nothing here is graduated. -/

#print axioms blockAB_inside
#print axioms blockAB_outside_row
#print axioms blockAB_outside_col
#print axioms blockAB_supported
#print axioms blockAB_supported_symm
#print axioms blockAB_surface_is_supported
#print axioms blockAB_deep_row_is_empty
#print axioms blockAB_deep_is_absence_carried
#print axioms layering_is_a_region_of_the_carrier
#print axioms keepSupported_reads_only_presentCarried
#print axioms the_rule_does_not_touch_an_unheld_cell
#print axioms blockAB_rests
#print axioms punctured_has_no_absence_layer
#print axioms punctured_rests
#print axioms the_resting_verdict_does_not_see_the_absence_layer
#print axioms the_absence_layer_survives
#print axioms groundedBy_at_a
#print axioms groundedBy_at_b
#print axioms groundedBy_off_column
#print axioms groundedBy_other_row
#print axioms groundedBy_surface_is_supported
#print axioms groundedBy_ground_is_not_supported
#print axioms the_rule_releases_the_ground
#print axioms groundedBy_is_emptied
#print axioms the_unsupported_ground_does_not_survive
#print axioms the_unsupported_ground_is_not_fixed
#print axioms what_survives_is_what_carries_nothing

#print axioms maintain_fixes_its_target
#print axioms the_reformed_ground_is_still_unsupported
#print axioms the_alternation_is_a_two_cycle
#print axioms the_supported_ground_is_declined
#print axioms maintaining_a_supported_ground_is_conflict_free
#print axioms maintaining_the_false_ground_is_conflicted
#print axioms the_supported_rests_the_unsupported_is_worked
#print axioms the_maintenance_cannot_lapse
#print axioms the_maintenance_is_order_dependent

#print axioms a_releasing_maintainer_must_form_the_ground
#print axioms a_maintainer_that_releases_the_ground_must_conflict
#print axioms pureForm_is_conflict_free
#print axioms pureForm_relays_from_the_empty
#print axioms pureForm_fixes_its_target
#print axioms the_conflict_free_maintainer_is_order_invariant
#print axioms the_composite_sustains_the_unsupported_ground
#print axioms the_composite_passes_through_the_empty
#print axioms the_supported_ground_never_lapses
#print axioms the_trade_off

#print axioms a_fixed_release_forces_a_conflict
#print axioms the_rule_opens_every_unsupported_cell
#print axioms a_self_examining_maintainer_must_conflict
#print axioms a_self_examining_maintainer_is_order_detectable
#print axioms the_trade_off_is_general
#print axioms the_inert_stance_is_not_a_third_arrangement
#print axioms the_supported_case_faces_neither_horn

end Chiralogy.LayeredPathology
