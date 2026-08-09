import Chiralogy.Model.NaryAssemblage
import Chiralogy.Model.InformationOrder

/-! # Experiment (LIVE): what controls the import's fine structure

Two registers have been read and they disagreed about almost everything below the import's bare existence: on
one the floor cut the imports down, on the other it did not cut at all; on one the maxima were total, on the
other nothing in the family was. The two differed in coordinate count and in points per coordinate at once, so
neither axis was isolated, and the standing guess was that carrier poverty drove it.

This file does not run a table of witnesses and read a pattern off it. It asks for the condition directly, and
the condition turns out to be statable and provable in general, which makes the sweep a check on a law rather
than the source of one.

The answer moves the question. Two of the four features are governed by a property of the FACTORS, not of the
carrier; the carrier enters only as a ceiling, deciding which factor behaviours are available at all. So the
axes the sweep was asked to separate turn out to collapse into a single carrier invariant, and that invariant
does not decide the features by itself.

Register-neutral throughout: carriers, coordinates, cells, rules.

ARCHIVED. FULLY GRADUATED: every declaration of this file is now canonical in Model/NaryAssemblage.

Pass 1, spec 4.a.23: FactorsSeparate, separating_factors_defeat_every_import.
Pass 5, spec 4.a.27: lvl, levelling, levelled_rows_agree,
  unseparating_factors_admit_a_levelling_import, the_floor_is_vacuous_iff_the_factors_separate, Thin,
  thin_carriers_admit_no_separating_factors, the_floor_bites_at_every_factor_choice_on_a_thin_carrier,
  sepFactors, a_carrier_that_is_not_thin_admits_separating_factors,
  the_carrier_forces_the_floor_iff_it_is_thin,
  the_whole_can_be_total_iff_the_factors_are_present_on_the_region.
Pass 5, spec 4.a.28: MaximalAdmissible, a_total_admissible_import_is_a_maximum, spike as canonical spikeAt,
  a_vacuous_floor_has_at_least_three_maxima, the_two_maxima_shape_requires_a_biting_floor.

One declaration did not graduate and was not lost: the_whole_reads_the_import_only_at_cross_cells is the same
proposition as fillings_agreeing_on_the_cross_give_the_same_whole, which Pass 1 had already graduated under
that name. The statement-comparison filter found it; proof-line counting had not.

The seven live files that referenced this one were repointed to canonical. Kept for the record; nothing
imports it.
-/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.ImportFineStructureSweep

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-! ## The two conditions

Everything below turns on two properties. One is about the factors: whether any point has two neighbours the
factors send to different values. The other is about the carrier alone: whether any point has two distinct
neighbours at all. -/

/-- The factors SEPARATE when some point has two single-move neighbours whose factor verdicts differ. -/
def FactorsSeparate (c : ∀ i, X i → X i → Option Bool) : Prop :=
  ∃ (a b q : Pt X) (i j : Fin n), differsInOne a q i ∧ differsInOne b q j ∧
    c i (a i) (q i) ≠ c j (b j) (q j)

/-- A carrier is THIN when no point has two distinct single-move neighbours. This is the only carrier property
the file needs, and it is what the coordinate count and the points-per-coordinate count collapse into. -/
abbrev Thin (X : Fin n → Type) : Prop :=
  ∀ (a b q : Pt X) (i j : Fin n), differsInOne a q i → differsInOne b q j → a = b

/-! ## Feature 1: does the floor bite

The floor bites when some import collapses the whole. The characterisation is exact and carrier-general in
both directions. -/

/-- **SEPARATING FACTORS DEFEAT EVERY IMPORT.** The two rows are told apart at a single-move cell, which no
import can reach, so no choice of import collapses the whole. -/
theorem separating_factors_defeat_every_import (c : ∀ i, X i → X i → Option Bool)
    (h : FactorsSeparate c) (imp : Pt X → Pt X → Option Bool) : NonDegenerate (nary c imp) := by
  obtain ⟨a, b, q, i, j, ha, hb, hne⟩ := h
  refine ⟨a, b, fun hEq => hne ?_⟩
  have hq := congrFun hEq q
  rwa [nary_apply_differ c imp ha, nary_apply_differ c imp hb] at hq

open scoped Classical in
/-- The value the factors agree on around a point, when they agree on anything there. -/
noncomputable def lvl (c : ∀ i, X i → X i → Option Bool) (q : Pt X) : Option Bool :=
  if h : ∃ p : Pt X × Fin n, differsInOne p.1 q p.2
    then c h.choose.2 (h.choose.1 h.choose.2) (q h.choose.2) else none

/-- The import that levels every cross cell to that value. -/
noncomputable def levelling (c : ∀ i, X i → X i → Option Bool) : Pt X → Pt X → Option Bool :=
  fun _ q => lvl c q

/-- Under the levelling import, every row takes the same value at every point. -/
theorem levelled_rows_agree (c : ∀ i, X i → X i → Option Bool) (h : ¬ FactorsSeparate c)
    (a q : Pt X) : nary c (levelling c) a q = lvl c q := by
  by_cases hex : ∃ i, differsInOne a q i
  · obtain ⟨i, hi⟩ := hex
    rw [nary_apply_differ c _ hi]
    have hp : ∃ p : Pt X × Fin n, differsInOne p.1 q p.2 := ⟨(a, i), hi⟩
    rw [lvl, dif_pos hp]
    by_contra hne
    exact h ⟨a, hp.choose.1, q, i, hp.choose.2, hi, hp.choose_spec, hne⟩
  · rw [nary_apply_imp c _ hex]; rfl

/-- **NON-SEPARATING FACTORS ADMIT AN IMPORT THAT COLLAPSES THE WHOLE.** So the floor bites whenever the
factors fail to separate, and the levelling import is the explicit witness. -/
theorem unseparating_factors_admit_a_levelling_import (c : ∀ i, X i → X i → Option Bool)
    (h : ¬ FactorsSeparate c) : ¬ NonDegenerate (nary c (levelling c)) := by
  rintro ⟨a, b, hne⟩
  exact hne (funext fun q => by
    rw [levelled_rows_agree c h a q, levelled_rows_agree c h b q])

/-- **THE FLOOR IS VACUOUS EXACTLY WHEN THE FACTORS SEPARATE.** Carrier-general, both directions. The first
feature of the fine structure is decided by the FACTORS, and the carrier appears nowhere in the condition. -/
theorem the_floor_is_vacuous_iff_the_factors_separate (c : ∀ i, X i → X i → Option Bool) :
    (∀ imp, NonDegenerate (nary c imp)) ↔ FactorsSeparate c := by
  refine ⟨fun hall => ?_, fun h imp => separating_factors_defeat_every_import c h imp⟩
  by_contra h
  exact unseparating_factors_admit_a_levelling_import c h (hall _)

/-! ## Where the carrier enters: as a ceiling

The carrier does not decide the feature, but it decides which factor behaviours are reachable. A thin carrier
admits no separating factors at all, so on a thin carrier the floor bites whatever the factors are. -/

/-- On a thin carrier no factors separate: the two neighbours are the same point and the same coordinate. -/
theorem thin_carriers_admit_no_separating_factors (hT : Thin X)
    (c : ∀ i, X i → X i → Option Bool) : ¬ FactorsSeparate c := by
  rintro ⟨a, b, q, i, j, ha, hb, hne⟩
  have hab : a = b := hT a b q i j ha hb
  subst hab
  have hij : i = j := differsInOne_unique ha hb
  subst hij
  exact hne rfl

/-- **ON A THIN CARRIER THE FLOOR BITES FOR EVERY CHOICE OF FACTORS.** No factors on such a carrier can protect
the whole from every import. -/
theorem the_floor_bites_at_every_factor_choice_on_a_thin_carrier (hT : Thin X)
    (c : ∀ i, X i → X i → Option Bool) : ∃ imp, ¬ NonDegenerate (nary c imp) :=
  ⟨levelling c, unseparating_factors_admit_a_levelling_import c
    (thin_carriers_admit_no_separating_factors hT c)⟩

/-- Factors built to answer one way on one named neighbour and the other way everywhere else. -/
def sepFactors (i : Fin n) (u : X i) : ∀ k, X k → X k → Option Bool :=
  fun k x _ => if h : k = i then some (decide (h ▸ x = u)) else some false

/-- **A CARRIER THAT IS NOT THIN ADMITS SEPARATING FACTORS.** So the ceiling is exact: above thinness, the
vacuous floor is always reachable. -/
theorem a_carrier_that_is_not_thin_admits_separating_factors (hT : ¬ Thin X) :
    ∃ c : ∀ i, X i → X i → Option Bool, FactorsSeparate c := by
  simp only [Thin, not_forall] at hT
  obtain ⟨a, b, q, i, j, ha, hb, hab⟩ := hT
  refine ⟨sepFactors i (a i), a, b, q, i, j, ha, hb, ?_⟩
  have hleft : sepFactors i (a i) i (a i) (q i) = some true := by simp [sepFactors]
  have hright : sepFactors i (a i) j (b j) (q j) = some false := by
    by_cases hji : j = i
    · subst hji
      have hne : b j ≠ a j := by
        intro hEq
        exact hab (funext fun k => by
          by_cases hk : k = j
          · subst hk; exact hEq.symm
          · rw [ha.2 k hk, ← hb.2 k hk])
      simp [sepFactors, hne]
    · simp [sepFactors, hji]
  rw [hleft, hright]
  simp

/-- **THE CARRIER FORCES THE FLOOR TO BITE EXACTLY WHEN IT IS THIN.** Carrier-general, both directions. This is
the whole of the carrier's contribution: it does not decide the feature, it decides whether the feature is
still free to vary once the factors are chosen. -/
theorem the_carrier_forces_the_floor_iff_it_is_thin :
    (∀ c : ∀ i, X i → X i → Option Bool, ∃ imp, ¬ NonDegenerate (nary c imp)) ↔ Thin X := by
  refine ⟨fun hall => ?_, fun hT c => the_floor_bites_at_every_factor_choice_on_a_thin_carrier hT c⟩
  by_contra hT
  obtain ⟨c, hc⟩ := a_carrier_that_is_not_thin_admits_separating_factors hT
  obtain ⟨imp, himp⟩ := hall c
  exact himp (separating_factors_defeat_every_import c hc imp)

/-! ## Feature 3: can the maxima be total

The second feature that admits an exact condition, and it is again a condition on the factors alone. -/

/-- **THE WHOLE CAN BE MADE TOTAL EXACTLY WHEN THE FACTORS LEAVE NO ABSENCE ON THE REGION.** The import can
fill every cross cell and no region cell, so the region's absences are beyond every import's reach. -/
theorem the_whole_can_be_total_iff_the_factors_are_present_on_the_region
    (c : ∀ i, X i → X i → Option Bool) :
    (∃ imp, isTotal (nary c imp)) ↔
      ∀ (a b : Pt X) (i : Fin n), differsInOne a b i → c i (a i) (b i) ≠ none := by
  constructor
  · rintro ⟨imp, hT⟩ a b i hi
    have := hT a b
    rwa [nary_apply_differ c imp hi] at this
  · intro hpres
    refine ⟨fun _ _ => some true, fun a b => ?_⟩
    by_cases hex : ∃ i, differsInOne a b i
    · obtain ⟨i, hi⟩ := hex
      rw [nary_apply_differ c _ hi]; exact hpres a b i hi
    · rw [nary_apply_imp c _ hex]; simp

/-! ## What the form does guarantee about the admissible space

Downward closure of the admissible set was observed on both registers read so far, and was a candidate for a
form-level guarantee. It is not one: it fails, and it fails on the very carrier where it was first seen. The
form-level fact in this area is weaker and is stated here on its own. -/

/-- **THE WHOLE READS THE IMPORT ONLY AT CROSS CELLS.** Form-level, carrier-general: imports agreeing on the
cross region give the same whole, so admissibility never depends on an import's region values. -/
theorem the_whole_reads_the_import_only_at_cross_cells (c : ∀ i, X i → X i → Option Bool)
    (imp imp' : Pt X → Pt X → Option Bool) (h : ∀ a b, IsCross a b → imp a b = imp' a b) :
    nary c imp = nary c imp' := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · obtain ⟨i, hi⟩ := hex
    rw [nary_apply_differ c imp hi, nary_apply_differ c imp' hi]
  · rw [nary_apply_imp c imp hex, nary_apply_imp c imp' hex]; exact h a b hex

/-! ## Features 2 and 4: how many maxima, and whether the residue collapses

The remaining two features are about the top of the admissible space. They also admit a general treatment, and
it ties them back to the first feature: the shape that was read off the first register, two maxima related by a
relabelling, is only available where the floor bites. -/

/-- An import is a maximum of the admissible space when it is admissible and nothing admissible sits strictly
above it. -/
def MaximalAdmissible (c : ∀ i, X i → X i → Option Bool) (imp : Pt X → Pt X → Option Bool) : Prop :=
  NonDegenerate (nary c imp) ∧
    ∀ imp', cLE imp imp' → NonDegenerate (nary c imp') → cLE imp' imp

/-- A total import is maximal in the information order, so an admissible total import is a maximum. -/
theorem a_total_admissible_import_is_a_maximum (c : ∀ i, X i → X i → Option Bool)
    (imp : Pt X → Pt X → Option Bool) (ht : isTotal imp)
    (ha : NonDegenerate (nary c imp)) : MaximalAdmissible c imp :=
  ⟨ha, fun imp' h _ => (maximal_iff_total imp).2 ht imp' h⟩

open scoped Classical in
/-- The import that answers one way at a single named cell and the other way everywhere else. -/
noncomputable def spike (a b : Pt X) : Pt X → Pt X → Option Bool :=
  fun x y => if x = a ∧ y = b then some true else some false

/-- **WHEN THE FLOOR IS VACUOUS AND THE CARRIER HAS TWO POINTS, THERE ARE AT LEAST THREE MAXIMA.** Every total
import is admissible, and three pairwise distinct total imports are available as soon as two cells are. -/
theorem a_vacuous_floor_has_at_least_three_maxima (c : ∀ i, X i → X i → Option Bool)
    (hsep : FactorsSeparate c) {a b : Pt X} (hab : a ≠ b) :
    ∃ i1 i2 i3 : Pt X → Pt X → Option Bool,
      MaximalAdmissible c i1 ∧ MaximalAdmissible c i2 ∧ MaximalAdmissible c i3 ∧
        i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 := by
  classical
  refine ⟨fun _ _ => some true, fun _ _ => some false, spike a a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact a_total_admissible_import_is_a_maximum c _ (fun _ _ => by simp)
      (separating_factors_defeat_every_import c hsep _)
  · exact a_total_admissible_import_is_a_maximum c _ (fun _ _ => by simp)
      (separating_factors_defeat_every_import c hsep _)
  · refine a_total_admissible_import_is_a_maximum c _ (fun x y => ?_)
      (separating_factors_defeat_every_import c hsep _)
    by_cases h : x = a ∧ y = a <;> simp [spike, h]
  · intro h; have := congrFun (congrFun h a) a; simp at this
  · intro h; have := congrFun (congrFun h b) b; simp [spike, hab.symm] at this
  · intro h; have := congrFun (congrFun h a) a; simp [spike] at this

/-- **SO THE TWO-MAXIMA SHAPE REQUIRES A BITING FLOOR.** Two maxima related by a relabelling, the residue read
off the first register, cannot occur where the factors separate: there the maxima are at least three. The
fourth feature is therefore governed by the first, and through it by the factors. -/
theorem the_two_maxima_shape_requires_a_biting_floor (c : ∀ i, X i → X i → Option Bool)
    {a b : Pt X} (hab : a ≠ b)
    (htwo : ∀ i1 i2 i3 : Pt X → Pt X → Option Bool, MaximalAdmissible c i1 →
      MaximalAdmissible c i2 → MaximalAdmissible c i3 → i1 = i2 ∨ i1 = i3 ∨ i2 = i3) :
    ∃ imp, ¬ NonDegenerate (nary c imp) := by
  by_cases hsep : FactorsSeparate c
  · obtain ⟨i1, i2, i3, h1, h2, h3, h12, h13, h23⟩ :=
      a_vacuous_floor_has_at_least_three_maxima c hsep hab
    rcases htwo i1 i2 i3 h1 h2 h3 with h | h | h
    · exact absurd h h12
    · exact absurd h h13
    · exact absurd h h23
  · exact ⟨levelling c, unseparating_factors_admit_a_levelling_import c hsep⟩

end Chiralogy.ImportFineStructureSweep
