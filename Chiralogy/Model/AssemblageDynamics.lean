import Chiralogy.Model.Assemblage
import Chiralogy.Model.InformationOrder

/-! # The binary assemblage against the moves and the order

The ordered binary `assembleClassify` (Model/Assemblage) tested against the information order and the two moves.
It is genuinely independent of the n-ary `nary`: `assembleClassify` is the ORDERED construction (`a.2` tested
first) and differs from `nary` even at `n = 2`. It is jointly monotone in its factors; totalization and
partialization commute with assembly under region-coherence conditions that are tight (needed only where the move
acts, absences for totalization, presences for partialization) and realizable; the assemblage form has an
intrinsic positive characterization (`isAssemblage2_iff`); and the form-preserving grain is a region, not a cell.

Depends on `Model/Assemblage` (the construction) and `Model/InformationOrder` (the order and the moves). -/

namespace Chiralogy

/-! ## Monotonicity -/

/-- **Assemblage is jointly monotone.** Raising all three factors in the information order raises the composite.
The region partition depends only on the pair, identical on both sides, so each region reduces to its factor's
order. The `a.2`-first asymmetry is invisible to the order. -/
theorem assembleClassify_mono {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    {c1 c1' : X1 → X1 → Option Bool} {c2 c2' : X2 → X2 → Option Bool}
    {imp imp' : (X1 × X2) → (X1 × X2) → Option Bool}
    (h1 : cLE c1 c1') (h2 : cLE c2 c2') (hi : cLE imp imp') :
    cLE (assembleClassify c1 c2 imp) (assembleClassify c1' c2' imp') := by
  intro a b
  simp only [assembleClassify]
  by_cases hab2 : a.2 = b.2
  · rw [if_pos hab2, if_pos hab2]; exact h1 a.1 b.1
  · rw [if_neg hab2, if_neg hab2]
    by_cases hab1 : a.1 = b.1
    · rw [if_pos hab1, if_pos hab1]; exact h2 a.2 b.2
    · rw [if_neg hab1, if_neg hab1]; exact hi a b

/-- Monotone in the first factor alone. -/
theorem assembleClassify_mono_c1 {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    {c1 c1' : X1 → X1 → Option Bool} (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (h1 : cLE c1 c1') :
    cLE (assembleClassify c1 c2 imp) (assembleClassify c1' c2 imp) :=
  assembleClassify_mono h1 (cLE_refl c2) (cLE_refl imp)

/-- Monotone in the second factor alone. -/
theorem assembleClassify_mono_c2 {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) {c2 c2' : X2 → X2 → Option Bool}
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (h2 : cLE c2 c2') :
    cLE (assembleClassify c1 c2 imp) (assembleClassify c1 c2' imp) :=
  assembleClassify_mono (cLE_refl c1) h2 (cLE_refl imp)

/-- Monotone in the import alone. -/
theorem assembleClassify_mono_imp {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    {imp imp' : (X1 × X2) → (X1 × X2) → Option Bool} (hi : cLE imp imp') :
    cLE (assembleClassify c1 c2 imp) (assembleClassify c1 c2 imp') :=
  assembleClassify_mono (cLE_refl c1) (cLE_refl c2) hi

/-- Assembling total factors gives a total composite. -/
theorem assemble_total_isTotal {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    {c1 : X1 → X1 → Option Bool} {c2 : X2 → X2 → Option Bool}
    {imp : (X1 × X2) → (X1 × X2) → Option Bool}
    (h1 : isTotal c1) (h2 : isTotal c2) (hi : isTotal imp) :
    isTotal (assembleClassify c1 c2 imp) := by
  intro a b
  simp only [assembleClassify]
  by_cases hab2 : a.2 = b.2
  · rw [if_pos hab2]; exact h1 a.1 b.1
  · rw [if_neg hab2]
    by_cases hab1 : a.1 = b.1
    · rw [if_pos hab1]; exact h2 a.2 b.2
    · rw [if_neg hab1]; exact hi a b

/-! ## Commutation with the moves -/

/-- **Totalization commutes with assembly under a scale-compatibility condition.** If the product scale `s`
restricts to `s1` on each `a.2 = b.2` region and to `s2` on each `a.1 = b.1` region (import totalized by `s`),
totalizing the composite equals assembling the totalized factors. -/
theorem totalization_commutes {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (s : X1 × X2 → Nat) (s1 : X1 → Nat) (s2 : X2 → Nat)
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool)
    (hs1 : ∀ a b : X1 × X2, a.2 = b.2 → decide (s b ≤ s a) = decide (s1 b.1 ≤ s1 a.1))
    (hs2 : ∀ a b : X1 × X2, a.2 ≠ b.2 → a.1 = b.1 → decide (s b ≤ s a) = decide (s2 b.2 ≤ s2 a.2)) :
    totalization s (assembleClassify c1 c2 imp)
      = assembleClassify (totalization s1 c1) (totalization s2 c2) (totalization s imp) := by
  funext a b
  by_cases h2 : a.2 = b.2
  · simp only [totalization, assembleClassify, if_pos h2, hs1 a b h2]
  · by_cases h1 : a.1 = b.1
    · simp only [totalization, assembleClassify, if_neg h2, if_pos h1, hs2 a b h2 h1]
    · simp only [totalization, assembleClassify, if_neg h2, if_neg h1]

/-- The scale condition is realizable (witness): a lexicographic product scale satisfies it. -/
theorem totalization_commutes_realizable :
    ∃ (s : Fin 2 × Fin 2 → Nat) (s1 s2 : Fin 2 → Nat),
      (∀ a b : Fin 2 × Fin 2, a.2 = b.2 → decide (s b ≤ s a) = decide (s1 b.1 ≤ s1 a.1))
        ∧ (∀ a b : Fin 2 × Fin 2, a.2 ≠ b.2 → a.1 = b.1 → decide (s b ≤ s a) = decide (s2 b.2 ≤ s2 a.2)) := by
  refine ⟨fun a => 2 * a.1.val + a.2.val, (fun i => i.val), (fun i => i.val), ?_, ?_⟩ <;> decide

/-- **Off the condition the two totalized composites are incomparable maxima** (witness). Both are total, so
maximal; they can differ; there is no inequality to recover, only two different ceilings. -/
theorem totalization_no_relation_off_compat :
    ∃ (s : Fin 2 × Fin 2 → Nat) (s1 s2 : Fin 2 → Nat)
      (c1 c2 : Fin 2 → Fin 2 → Option Bool) (imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool),
      ¬ cLE (totalization s (assembleClassify c1 c2 imp))
            (assembleClassify (totalization s1 c1) (totalization s2 c2) (totalization s imp))
        ∧ ¬ cLE (assembleClassify (totalization s1 c1) (totalization s2 c2) (totalization s imp))
              (totalization s (assembleClassify c1 c2 imp)) := by
  refine ⟨fun a => a.1.val * a.2.val, (fun _ => 0), (fun _ => 0),
          (fun _ _ => none), (fun _ _ => none), (fun _ _ => none), ?_, ?_⟩
  · intro h; have hh := h (0, 1) (1, 1); simp [optLE, totalization, assembleClassify] at hh
  · intro h; have hh := h (0, 1) (1, 1); simp [optLE, totalization, assembleClassify] at hh

/-- **Partialization commutes structurally.** Assembling partialized factors is always below the composite. -/
theorem assembled_partialization_is_below {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (w1 : X1 → X1 → Bool) (w2 : X2 → X2 → Bool) (w3 : (X1 × X2) → (X1 × X2) → Bool)
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) :
    cLE (assembleClassify (partialization w1 c1) (partialization w2 c2) (partialization w3 imp))
        (assembleClassify c1 c2 imp) :=
  assembleClassify_mono (partialization_le_c w1 c1) (partialization_le_c w2 c2) (partialization_le_c w3 imp)

/-- **Assembling partialized factors is always a partialization of the composite** (no side condition). -/
theorem assembled_partialization_is_a_partialization {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (w1 : X1 → X1 → Bool) (w2 : X2 → X2 → Bool) (w3 : (X1 × X2) → (X1 × X2) → Bool)
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) :
    ∃ W, assembleClassify (partialization w1 c1) (partialization w2 c2) (partialization w3 imp)
        = partialization W (assembleClassify c1 c2 imp) :=
  (below_iff_partialization _ _).1 (assembled_partialization_is_below w1 w2 w3 c1 c2 imp)

/-- The explicit per-region partialization law: a region-coherent mask commutes to an equality. -/
theorem partialization_commutes {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (w : (X1 × X2) → (X1 × X2) → Bool) (w1 : X1 → X1 → Bool) (w2 : X2 → X2 → Bool)
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool)
    (hw1 : ∀ a b : X1 × X2, a.2 = b.2 → w a b = w1 a.1 b.1)
    (hw2 : ∀ a b : X1 × X2, a.2 ≠ b.2 → a.1 = b.1 → w a b = w2 a.2 b.2) :
    partialization w (assembleClassify c1 c2 imp)
      = assembleClassify (partialization w1 c1) (partialization w2 c2) (partialization w imp) := by
  funext a b
  by_cases h2 : a.2 = b.2
  · simp only [partialization, assembleClassify, if_pos h2, hw1 a b h2]
  · by_cases h1 : a.1 = b.1
    · simp only [partialization, assembleClassify, if_neg h2, if_pos h1, hw2 a b h2 h1]
    · simp only [partialization, assembleClassify, if_neg h2, if_neg h1]

/-! ## Region-coherence: tightness and non-necessity -/

/-- **Totalization commutes under coherence on the absence cells only** (strictly weaker than region-coherence). -/
theorem totalization_commutes_on_absences {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (s : X1 × X2 → Nat) (s1 : X1 → Nat) (s2 : X2 → Nat)
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool)
    (hs1 : ∀ a b : X1 × X2, a.2 = b.2 → c1 a.1 b.1 = none → decide (s b ≤ s a) = decide (s1 b.1 ≤ s1 a.1))
    (hs2 : ∀ a b : X1 × X2, a.2 ≠ b.2 → a.1 = b.1 → c2 a.2 b.2 = none →
      decide (s b ≤ s a) = decide (s2 b.2 ≤ s2 a.2)) :
    totalization s (assembleClassify c1 c2 imp)
      = assembleClassify (totalization s1 c1) (totalization s2 c2) (totalization s imp) := by
  funext a b
  by_cases h2 : a.2 = b.2
  · rcases hc : c1 a.1 b.1 with _ | v
    · simp only [totalization, assembleClassify, if_pos h2, hc, Option.getD_none, hs1 a b h2 hc]
    · simp only [totalization, assembleClassify, if_pos h2, hc, Option.getD_some]
  · by_cases h1 : a.1 = b.1
    · rcases hc : c2 a.2 b.2 with _ | v
      · simp only [totalization, assembleClassify, if_neg h2, if_pos h1, hc, Option.getD_none,
          hs2 a b h2 h1 hc]
      · simp only [totalization, assembleClassify, if_neg h2, if_pos h1, hc, Option.getD_some]
    · simp only [totalization, assembleClassify, if_neg h2, if_neg h1]

/-- **Absence-coherence is necessary too**: commutation forces the scales to agree at each absent region-1 cell.
So commutation is EQUIVALENT to absence-coherence; full region-coherence is sufficient-only. -/
theorem totalization_commutation_forces_absence_coherence {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (s : X1 × X2 → Nat) (s1 : X1 → Nat) (s2 : X2 → Nat)
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool)
    (h : totalization s (assembleClassify c1 c2 imp)
        = assembleClassify (totalization s1 c1) (totalization s2 c2) (totalization s imp))
    (a b : X1 × X2) (h2 : a.2 = b.2) (hc : c1 a.1 b.1 = none) :
    decide (s b ≤ s a) = decide (s1 b.1 ≤ s1 a.1) := by
  have hcong := congrFun (congrFun h a) b
  simp only [totalization, assembleClassify, if_pos h2, hc, Option.getD_none] at hcong
  exact Option.some_inj.mp hcong

/-- Any scale commutes on total factors: the absences that would witness incoherence are absent. -/
theorem totalization_commutes_of_total {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (s : X1 × X2 → Nat) (s1 : X1 → Nat) (s2 : X2 → Nat)
    {c1 : X1 → X1 → Option Bool} {c2 : X2 → X2 → Option Bool}
    {imp : (X1 × X2) → (X1 × X2) → Option Bool}
    (h1 : isTotal c1) (h2 : isTotal c2) (hi : isTotal imp) :
    totalization s (assembleClassify c1 c2 imp)
      = assembleClassify (totalization s1 c1) (totalization s2 c2) (totalization s imp) := by
  rw [(totalization_fixed_iff_total s _).2 (assemble_total_isTotal h1 h2 hi),
    (totalization_fixed_iff_total s1 c1).2 h1, (totalization_fixed_iff_total s2 c2).2 h2,
    (totalization_fixed_iff_total s imp).2 hi]

/-- **Full region-coherence is NOT necessary for totalization commutation** (witness): on total factors an
incoherent scale still commutes. -/
theorem totalization_commutation_not_necessary :
    ∃ (s : Fin 2 × Fin 2 → Nat) (s1 s2 : Fin 2 → Nat)
      (c1 c2 : Fin 2 → Fin 2 → Option Bool) (imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool),
      (∃ a b : Fin 2 × Fin 2, a.2 = b.2 ∧ decide (s b ≤ s a) ≠ decide (s1 b.1 ≤ s1 a.1))
        ∧ totalization s (assembleClassify c1 c2 imp)
            = assembleClassify (totalization s1 c1) (totalization s2 c2) (totalization s imp) := by
  refine ⟨fun a => a.1.val * a.2.val, (fun _ => 0), (fun _ => 0),
    (fun _ _ => some true), (fun _ _ => some true), (fun _ _ => some true), ⟨(0, 1), (1, 1), rfl, by decide⟩,
    totalization_commutes_of_total _ _ _ (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)⟩

/-- Masking an absent classification changes nothing. -/
theorem partialization_bot {X : Type} (w : X → X → Bool) : partialization w (botC X) = botC X := by
  funext x y; simp only [partialization, botC]; split_ifs <;> rfl

/-- **Partialization commutes under coherence on the presence cells only** (dual to totalization). -/
theorem partialization_commutes_on_presences {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (w : (X1 × X2) → (X1 × X2) → Bool) (w1 : X1 → X1 → Bool) (w2 : X2 → X2 → Bool)
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool)
    (hw1 : ∀ a b : X1 × X2, a.2 = b.2 → c1 a.1 b.1 ≠ none → w a b = w1 a.1 b.1)
    (hw2 : ∀ a b : X1 × X2, a.2 ≠ b.2 → a.1 = b.1 → c2 a.2 b.2 ≠ none → w a b = w2 a.2 b.2) :
    partialization w (assembleClassify c1 c2 imp)
      = assembleClassify (partialization w1 c1) (partialization w2 c2) (partialization w imp) := by
  funext a b
  by_cases h2 : a.2 = b.2
  · rcases hc : c1 a.1 b.1 with _ | v
    · simp [partialization, assembleClassify, h2, hc]
    · simp [partialization, assembleClassify, h2, hc, hw1 a b h2 (by rw [hc]; exact Option.some_ne_none v)]
  · by_cases h1 : a.1 = b.1
    · rcases hc : c2 a.2 b.2 with _ | v
      · simp [partialization, assembleClassify, h2, h1, hc]
      · simp [partialization, assembleClassify, h2, h1, hc,
          hw2 a b h2 h1 (by rw [hc]; exact Option.some_ne_none v)]
    · simp [partialization, assembleClassify, h2, h1]

/-- **Presence-coherence is necessary for partialization commutation** (the dual of the absence extraction). -/
theorem partialization_commutation_forces_presence_coherence {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (w : (X1 × X2) → (X1 × X2) → Bool) (w1 : X1 → X1 → Bool) (w2 : X2 → X2 → Bool)
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool)
    (h : partialization w (assembleClassify c1 c2 imp)
        = assembleClassify (partialization w1 c1) (partialization w2 c2) (partialization w imp))
    (a b : X1 × X2) (h2 : a.2 = b.2) (v : Bool) (hc : c1 a.1 b.1 = some v) :
    w a b = w1 a.1 b.1 := by
  have hcong := congrFun (congrFun h a) b
  simp only [partialization, assembleClassify, if_pos h2, hc] at hcong
  by_cases hw : w a b = true
  · by_cases hw1 : w1 a.1 b.1 = true
    · rw [hw, hw1]
    · rw [if_pos hw, if_neg hw1] at hcong; exact absurd hcong (by simp)
  · by_cases hw1 : w1 a.1 b.1 = true
    · rw [if_neg hw, if_pos hw1] at hcong; exact absurd hcong (by simp)
    · rw [Bool.not_eq_true] at hw hw1; rw [hw, hw1]

/-- **Full region-coherence is NOT necessary for partialization commutation** (witness): on all-absent factors an
incoherent mask still commutes. -/
theorem partialization_commutation_not_necessary :
    ∃ (w : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Bool) (w1 w2 : Fin 2 → Fin 2 → Bool)
      (c1 c2 : Fin 2 → Fin 2 → Option Bool) (imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool),
      (∃ a b : Fin 2 × Fin 2, a.2 = b.2 ∧ w a b ≠ w1 a.1 b.1)
        ∧ partialization w (assembleClassify c1 c2 imp)
            = assembleClassify (partialization w1 c1) (partialization w2 c2) (partialization w imp) := by
  refine ⟨fun a _ => decide (a.2 = 0), (fun _ _ => false), (fun _ _ => false),
    (fun _ _ => none), (fun _ _ => none), (fun _ _ => none), ⟨(0, 0), (1, 0), rfl, by decide⟩, ?_⟩
  funext a b; simp [partialization, assembleClassify]

/-! ## Form: the intrinsic positive characterization and its breaks -/

/-- **The signature of assemblage form.** In any assemblage, cells over a shared second coordinate are constant
in it: `A (x1, z) (y1, z)` does not depend on `z`. -/
theorem assemblage_region1_independent {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (x1 y1 : X1) (z z' : X2) :
    assembleClassify c1 c2 imp (x1, z) (y1, z) = assembleClassify c1 c2 imp (x1, z') (y1, z') :=
  ((factors_determine_the_shared_region c1 c2 imp (x1, z) (y1, z)).1 rfl).trans
    ((factors_determine_the_shared_region c1 c2 imp (x1, z') (y1, z')).1 rfl).symm

/-- Region-2 independence: a region-c2 cell depends only on coordinate 2. -/
theorem assemblage_region2_independent {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (x1 x1' : X1) (z2 w2 : X2) (h : z2 ≠ w2) :
    assembleClassify c1 c2 imp (x1, z2) (x1, w2) = assembleClassify c1 c2 imp (x1', z2) (x1', w2) :=
  ((factors_determine_the_shared_region c1 c2 imp (x1, z2) (x1, w2)).2 rfl h).trans
    ((factors_determine_the_shared_region c1 c2 imp (x1', z2) (x1', w2)).2 rfl h).symm

/-- The intrinsic predicate: region-1 and region-2 cells each depend only on their own coordinate. No
factorization. -/
def isAssemblage2 {X1 X2 : Type} (A : (X1 × X2) → (X1 × X2) → Option Bool) : Prop :=
  (∀ x1 y1 : X1, ∀ z z' : X2, A (x1, z) (y1, z) = A (x1, z') (y1, z'))
    ∧ (∀ x1 x1' : X1, ∀ z2 w2 : X2, z2 ≠ w2 → A (x1, z2) (x1, w2) = A (x1', z2) (x1', w2))

/-- **The positive characterization.** A classification is a binary assemblage IFF it satisfies the two
region-independence conditions; sufficiency reconstructs the factors from basepoints. -/
theorem isAssemblage2_iff {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2] [Inhabited X1] [Inhabited X2]
    (A : (X1 × X2) → (X1 × X2) → Option Bool) :
    (∃ c1 c2 imp, A = assembleClassify c1 c2 imp) ↔ isAssemblage2 A := by
  constructor
  · rintro ⟨c1, c2, imp, rfl⟩
    exact ⟨fun x1 y1 z z' => assemblage_region1_independent c1 c2 imp x1 y1 z z',
      fun x1 x1' z2 w2 h => assemblage_region2_independent c1 c2 imp x1 x1' z2 w2 h⟩
  · rintro ⟨hR1, hR2⟩
    refine ⟨fun x1 y1 => A (x1, default) (y1, default), fun z2 w2 => A (default, z2) (default, w2), A, ?_⟩
    funext a b
    obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
    simp only [assembleClassify]
    by_cases h2 : a2 = b2
    · subst h2; rw [if_pos rfl]; exact hR1 a1 b1 a2 default
    · rw [if_neg h2]
      by_cases h1 : a1 = b1
      · subst h1; rw [if_pos rfl]; exact hR2 a1 default a2 b2 h2
      · rw [if_neg h1]

/-- **A region-incoherent partialization destroys the assemblage form** (witness): a mask reading the shared
coordinate opens a present region-1 cell at one shared value but not another. -/
theorem partialization_breaks_form :
    ∃ (w : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Bool)
      (c1 c2 : Fin 2 → Fin 2 → Option Bool) (imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool),
      ¬ ∃ (d1 d2 : Fin 2 → Fin 2 → Option Bool) (dimp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool),
        partialization w (assembleClassify c1 c2 imp) = assembleClassify d1 d2 dimp := by
  refine ⟨fun a _ => decide (a.2 = 0), (fun _ _ => some true), (fun _ _ => none),
    (fun _ _ => none), ?_⟩
  rintro ⟨d1, d2, dimp, h⟩
  have key := assemblage_region1_independent d1 d2 dimp 0 1 0 1
  have e0 := congrFun (congrFun h (0, 0)) (1, 0)
  have e1 := congrFun (congrFun h (0, 1)) (1, 1)
  rw [← e0, ← e1] at key
  revert key; decide

/-- **A region-incoherent totalization also destroys the assemblage form** (witness). -/
theorem totalization_breaks_form :
    ∃ (s : (Fin 2 × Fin 2) → Nat)
      (c1 c2 : Fin 2 → Fin 2 → Option Bool) (imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool),
      ¬ ∃ (d1 d2 : Fin 2 → Fin 2 → Option Bool) (dimp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool),
        totalization s (assembleClassify c1 c2 imp) = assembleClassify d1 d2 dimp := by
  refine ⟨fun a => a.1.val * a.2.val, (fun _ _ => none), (fun _ _ => none),
    (fun _ _ => none), ?_⟩
  rintro ⟨d1, d2, dimp, h⟩
  have key := assemblage_region1_independent d1 d2 dimp 0 1 0 1
  have e0 := congrFun (congrFun h (0, 0)) (1, 0)
  have e1 := congrFun (congrFun h (0, 1)) (1, 1)
  rw [← e0, ← e1] at key
  revert key; decide

/-- **Form-preservation is a factor-parameter interaction, not a mask property** (witness): the same incoherent
mask destroys the form on present factors yet preserves it on absent factors. -/
theorem form_preservation_not_necessary :
    ∃ w : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Bool,
      (∃ (c1 c2 : Fin 2 → Fin 2 → Option Bool) (imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool),
        ¬ ∃ (d1 d2 : Fin 2 → Fin 2 → Option Bool) (dimp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool),
          partialization w (assembleClassify c1 c2 imp) = assembleClassify d1 d2 dimp)
        ∧ (∃ (c1 c2 : Fin 2 → Fin 2 → Option Bool) (imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool)
            (d1 d2 : Fin 2 → Fin 2 → Option Bool) (dimp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool),
          partialization w (assembleClassify c1 c2 imp) = assembleClassify d1 d2 dimp) := by
  refine ⟨fun a _ => decide (a.2 = 0), ?_, ?_⟩
  · refine ⟨(fun _ _ => some true), (fun _ _ => none), (fun _ _ => none), ?_⟩
    rintro ⟨d1, d2, dimp, h⟩
    have key := assemblage_region1_independent d1 d2 dimp 0 1 0 1
    have e0 := congrFun (congrFun h (0, 0)) (1, 0)
    have e1 := congrFun (congrFun h (0, 1)) (1, 1)
    rw [← e0, ← e1] at key
    revert key; decide
  · refine ⟨(fun _ _ => none), (fun _ _ => none), (fun _ _ => none),
      (fun _ _ => none), (fun _ _ => none), (fun _ _ => none), ?_⟩
    funext a b; simp [partialization, assembleClassify]

/-! ## Endpoints and form-preserving paths -/

/-- **The assemblage floor comes apart from the order-bottom** (witness): the all-false composite is an
assemblage, satisfies the floor predicate, sits above the order-bottom, and is not it. -/
theorem assemblage_floor_comes_apart :
    assembleClassify (cFalse : Fin 1 → Fin 1 → Option Bool) cFalse cFalse
        = (cFalse : (Fin 1 × Fin 1) → (Fin 1 × Fin 1) → Option Bool)
      ∧ (∀ a b, (cFalse : (Fin 1 × Fin 1) → (Fin 1 × Fin 1) → Option Bool) a b ≠ some true)
      ∧ cLE (botC (Fin 1 × Fin 1)) cFalse
      ∧ botC (Fin 1 × Fin 1) ≠ cFalse := by
  refine ⟨?_, fun a b => by simp [cFalse], botC_le _, ?_⟩
  · funext a b; simp [assembleClassify, cFalse]
  · intro h; have := congrFun (congrFun h 0) 0; simp [botC, cFalse] at this

/-- **The assemblage ceiling is an order-maximum.** Assembling total factors yields a total composite, maximal by
`maximal_iff_total`. -/
theorem assemblage_ceiling_is_maximal {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    {c1 : X1 → X1 → Option Bool} {c2 : X2 → X2 → Option Bool}
    {imp : (X1 × X2) → (X1 × X2) → Option Bool}
    (h1 : isTotal c1) (h2 : isTotal c2) (hi : isTotal imp) :
    ∀ d, cLE (assembleClassify c1 c2 imp) d → cLE d (assembleClassify c1 c2 imp) :=
  (maximal_iff_total _).2 (assemble_total_isTotal h1 h2 hi)

/-- **Descent to the order-bottom stays within the assemblage form.** The all-absent composite is the assemblage
of all-absent factors. -/
theorem bottom_stays_in_form {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2] :
    botC (X1 × X2) = assembleClassify (botC X1) (botC X2) (botC (X1 × X2)) := by
  funext a b
  simp only [botC, assembleClassify]
  by_cases h2 : a.2 = b.2
  · rw [if_pos h2]
  · rw [if_neg h2]; by_cases h1 : a.1 = b.1
    · rw [if_pos h1]
    · rw [if_neg h1]

/-- **A single-cell step leaves the form** (witness): opening one region-1 cell breaks its constancy across the
shared coordinate. The minimal form-preserving step cannot be a single cell. -/
theorem single_cell_partialization_leaves_form :
    ∃ (A : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool) (w : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Bool),
      isAssemblage2 A ∧ ¬ isAssemblage2 (partialization w A) := by
  refine ⟨(fun _ _ => some true), (fun a b => decide (a = (0, 0) ∧ b = (1, 0))),
    ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩, ?_⟩
  rintro ⟨hR1, _⟩
  have := hR1 0 1 0 1
  revert this; decide

/-- **A region step (a whole factor) stays in form and moves down.** The form-preserving grain is a region. -/
theorem factorwise_step_stays_in_form {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (w1 : X1 → X1 → Bool) (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) :
    (∃ d1 d2 dimp, assembleClassify (partialization w1 c1) c2 imp = assembleClassify d1 d2 dimp)
      ∧ cLE (assembleClassify (partialization w1 c1) c2 imp) (assembleClassify c1 c2 imp) :=
  ⟨⟨partialization w1 c1, c2, imp, rfl⟩, assembleClassify_mono_c1 c2 imp (partialization_le_c w1 c1)⟩

/-- **A region-stepwise path reaches the order-bottom in form.** Emptying every factor lands on `botC`. -/
theorem factorwise_reaches_bottom_in_form {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) :
    assembleClassify (partialization (fun _ _ => true) c1) (partialization (fun _ _ => true) c2)
        (partialization (fun _ _ => true) imp) = botC (X1 × X2) := by
  rw [full_partialization_is_bot, full_partialization_is_bot, full_partialization_is_bot]
  exact bottom_stays_in_form.symm

/-- **The path is a family, not a canonical trajectory** (witness): the first region step already depends on
which factor is emptied. -/
theorem descent_path_is_a_family :
    ∃ (c1 c2 : Fin 2 → Fin 2 → Option Bool) (imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool),
      assembleClassify (partialization (fun _ _ => true) c1) c2 imp
        ≠ assembleClassify c1 (partialization (fun _ _ => true) c2) imp := by
  refine ⟨(fun _ _ => some true), (fun _ _ => some false), (fun _ _ => none), ?_⟩
  intro h
  have hcell := congrFun (congrFun h (0, 0)) (1, 0)
  revert hcell; decide

end Chiralogy
