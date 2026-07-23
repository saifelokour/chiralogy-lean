import Chiralogy.Experiments.archive.InformationOrder

/-! # Experiment (ARCHIVED after graduation pass 5): does the information order reach the factors?

ARCHIVED. Both groups are canonical: the n-ary block in `Model/NaryAssemblage` (pass 3) and the BINARY block
(`assembleClassify_mono`, `totalization_commutes` and its refinements, `isAssemblage2_iff`, the region-independence
and break witnesses, `factorwise_*`, `single_cell_partialization_leaves_form`, `descent_path_is_a_family`, the
endpoints) in `Model/AssemblageDynamics` (pass 5). Nothing graduate-worthy remains. Kept as a standalone record,
namespaced `Chiralogy.AssemblageDynamics`.

The dynamics sweep named the sharpest gap: nothing connects a move on a composite to moves on its factors. The
`InformationOrder` pass supplied a partial order on classifications (`cLE`), which makes that gap well-posed.
This file tests it against `assembleClassify`.

Imported tools (established in `InformationOrder`, not re-derived): `cLE` is a partial order, meet-semilattice
with bottom `botC`, maxima = total maps (`maximal_iff_total`); `totalization` is above its input and lands in
the maxima but is not monotone; `partialization` is below and is monotone; `below_iff_partialization` (the order
IS the partialization image).

GRADUATED (group 3 of 5, the n-ary assemblage group) to the new canonical module `Model/NaryAssemblage`
(`namespace Chiralogy`), verbatim under the same names: the construction (`differsInOne`, `differsInOne_unique`,
`nary`, `nary_apply_differ`, `nary_apply_imp`, `nary_bot`, `nary_isTotal`), form (`nary_region_independent`,
`isAssemblageN`, `nary_form_iff`), `nary_mono`, the commutation laws with refinements and necessity
(`nary_totalization_commutes`, `_on_absences`, `_forces_absence_coherence`, `nary_partialization_commutes_on_presences`,
`_forces_presence_coherence`, `nary_assembled_partialization_is_below`, `_a_partialization`), the uniform scale
(`nary_sum_scale_coherent`, `nary_totalization_commutes_sum`), the paths (`emptyFactor`, `emptyFactor_comm`,
`emptyFactor_idem`, `descentBySet`, `descentPath` and its zero/isAssemblageN/descends/reaches_bot lemmas,
`ascentPath` and its zero/isAssemblageN/ascends/reaches_ceiling/ceiling_isTotal lemmas, `descentPath_eq_bySet`,
`ascent_ceilings_incomparable`, `distinct_maxima_incomparable`), and the n-ary order-dependence witness
`descent_path_is_a_family_nary`. NOT graduated here: `descent_path_is_a_family` uses `assembleClassify`, so it
belongs to the binary group (pass 5), deferred. The BINARY results in this file (`assembleClassify_mono`,
`totalization_commutes`, `isAssemblage2_iff`, `single_cell_partialization_leaves_form`, `factorwise_*`, the
region-independence and break witnesses, etc.) are the pass-5 group and stay live. This file is NOT archived:
AssemblageRelations still imports it. -/

open Chiralogy Chiralogy.InformationOrder

namespace Chiralogy.AssemblageDynamics

/-! ## Q1: is assembleClassify monotone in its factors? -/

/-- **Assemblage is jointly monotone.** Raising all three factors in the information order raises the composite.
The region partition depends only on the pair `(a, b)`, identical on both sides, so each region reduces to its
factor's order. The known asymmetry (`a.2 = b.2` tested first) is invisible to the order. -/
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

/-! ## Q2: does a move on the composite relate to moves on the factors? -/

/-- Assembling total factors gives a total composite: every region lands present. -/
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

/-- **Distinct maxima are incomparable.** Any two distinct total classifications have no order relation: the
only relation two totalizations can bear is equality. -/
theorem distinct_maxima_incomparable {X : Type} [DecidableEq X] (c d : X → X → Option Bool)
    (hc : isTotal c) (hd : isTotal d) (hne : c ≠ d) : ¬ cLE c d ∧ ¬ cLE d c := by
  refine ⟨fun h => hne (cLE_antisymm h ((maximal_iff_total c).2 hc d h)), ?_⟩
  intro h; exact hne (cLE_antisymm ((maximal_iff_total d).2 hd c h) h)

/-- **Totalization commutes with assembly under a scale-compatibility condition.** If the product scale `s`
restricts to `s1` on each `a.2 = b.2` region and to `s2` on each `a.1 = b.1` region (and the import is totalized
by `s` itself), then totalizing the composite equals assembling the totalized factors. -/
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

/-- The scale condition is realizable, not vacuous: a lexicographic product scale satisfies it. -/
theorem totalization_commutes_realizable :
    ∃ (s : Fin 2 × Fin 2 → Nat) (s1 s2 : Fin 2 → Nat),
      (∀ a b : Fin 2 × Fin 2, a.2 = b.2 → decide (s b ≤ s a) = decide (s1 b.1 ≤ s1 a.1))
        ∧ (∀ a b : Fin 2 × Fin 2, a.2 ≠ b.2 → a.1 = b.1 → decide (s b ≤ s a) = decide (s2 b.2 ≤ s2 a.2)) := by
  refine ⟨fun a => 2 * a.1.val + a.2.val, (fun i => i.val), (fun i => i.val), ?_, ?_⟩ <;> decide

/-- **Off the condition, the two totalized composites are incomparable maxima.** Both are total (so maximal), and
they can differ, so by `distinct_maxima_incomparable` neither is below the other. There is no inequality to
recover: totalizing the composite and assembling the totalized factors are simply two different ceilings. -/
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

/-- **Partialization behaves better: it commutes structurally.** Assembling partialized factors is always below
the assembled composite (Q1 monotonicity plus `partialization_le_c`). -/
theorem assembled_partialization_is_below {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (w1 : X1 → X1 → Bool) (w2 : X2 → X2 → Bool) (w3 : (X1 × X2) → (X1 × X2) → Bool)
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) :
    cLE (assembleClassify (partialization w1 c1) (partialization w2 c2) (partialization w3 imp))
        (assembleClassify c1 c2 imp) :=
  assembleClassify_mono (partialization_le_c w1 c1) (partialization_le_c w2 c2) (partialization_le_c w3 imp)

/-- **Assembling partialized factors is always a partialization of the composite.** By `below_iff_partialization`
the composite mask exists: unlike totalization, this commutation needs no side condition. The monotone arm whose
image IS the order stays inside the order. -/
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

/-! ## Q3: can factors be recovered after a move? -/

/-- **The signature of assemblage form.** In any assemblage, cells over a shared second coordinate are constant
in that coordinate: `A (x1, z) (y1, z)` does not depend on `z` (it is `c1 x1 y1`). This is the checkable invariant
that factor-recovery relies on. -/
theorem assemblage_region1_independent {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (x1 y1 : X1) (z z' : X2) :
    assembleClassify c1 c2 imp (x1, z) (y1, z) = assembleClassify c1 c2 imp (x1, z') (y1, z') :=
  ((factors_determine_the_shared_region c1 c2 imp (x1, z) (y1, z)).1 rfl).trans
    ((factors_determine_the_shared_region c1 c2 imp (x1, z') (y1, z')).1 rfl).symm

/-- **A region-incoherent partialization destroys the assemblage form.** A mask reading the shared coordinate
opens a present region-1 cell at one shared value but not another, so the result is not `assembleClassify` of any
factors: the decomposition is gone, not merely relabeled. -/
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

/-- **A region-incoherent totalization also destroys the assemblage form.** A product scale fills a region-1
absence differently at different shared coordinates, so the totalized composite is not an assemblage of anything. -/
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

/-! ## Q4: where do the endpoints sit? -/

/-- **The assemblage floor comes apart from the order-bottom**, exactly as the general floor did. The all-false
composite is an assemblage (of all-false factors), satisfies the floor predicate (never `some true`), sits above
the order-bottom, and is not it. -/
theorem assemblage_floor_comes_apart :
    assembleClassify (cFalse : Fin 1 → Fin 1 → Option Bool) cFalse cFalse
        = (cFalse : (Fin 1 × Fin 1) → (Fin 1 × Fin 1) → Option Bool)
      ∧ (∀ a b, (cFalse : (Fin 1 × Fin 1) → (Fin 1 × Fin 1) → Option Bool) a b ≠ some true)
      ∧ cLE (botC (Fin 1 × Fin 1)) cFalse
      ∧ botC (Fin 1 × Fin 1) ≠ cFalse := by
  refine ⟨?_, fun a b => by simp [cFalse], botC_le _, ?_⟩
  · funext a b; simp [assembleClassify, cFalse]
  · intro h; have := congrFun (congrFun h 0) 0; simp [botC, cFalse] at this

/-- **The assemblage ceiling is an order-maximum.** Assembling total factors yields a total composite, which by
`maximal_iff_total` is maximal: the factor-wise ceiling lands among the order-maxima. -/
theorem assemblage_ceiling_is_maximal {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    {c1 : X1 → X1 → Option Bool} {c2 : X2 → X2 → Option Bool}
    {imp : (X1 × X2) → (X1 × X2) → Option Bool}
    (h1 : isTotal c1) (h2 : isTotal c2) (hi : isTotal imp) :
    ∀ d, cLE (assembleClassify c1 c2 imp) d → cLE d (assembleClassify c1 c2 imp) :=
  (maximal_iff_total _).2 (assemble_total_isTotal h1 h2 hi)

/-- **Descent to the order-bottom stays within the assemblage form.** The all-absent composite is the assemblage
of all-absent factors: the bottom is reachable inside the form, via the monotone arm. -/
theorem bottom_stays_in_form {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2] :
    botC (X1 × X2) = assembleClassify (botC X1) (botC X2) (botC (X1 × X2)) := by
  funext a b
  simp only [botC, assembleClassify]
  by_cases h2 : a.2 = b.2
  · rw [if_pos h2]
  · rw [if_neg h2]; by_cases h1 : a.1 = b.1
    · rw [if_pos h1]
    · rw [if_neg h1]

/-! ## Q1 (converse): is region-coherence necessary?

Region-coherence is SUFFICIENT (above). The true necessary-and-sufficient condition is weaker: the parameter
need agree only where the move acts. For totalization the fill default is used only on ABSENCE cells; for
partialization the mask matters only on PRESENCE cells. Region-coherence (agreement everywhere) overshoots. -/

/-- **Totalization commutes under coherence on the absence cells only.** The scale need agree with the factor
scales only where the factor is absent; on present cells `getD` ignores the default. Strictly weaker than full
region-coherence. -/
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

/-- **And absence-coherence is necessary too**: commutation forces the scales to agree at each absent region-1
cell. So commutation is EQUIVALENT to absence-coherence, and full region-coherence is sufficient-only. -/
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

/-- **Full region-coherence is NOT necessary for totalization commutation.** On total factors an incoherent
scale still commutes. -/
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

/-- **Partialization commutes under coherence on the presence cells only** (dual to totalization: the mask
matters only where the factor is present). -/
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

/-- **Full region-coherence is NOT necessary for partialization commutation.** On all-absent factors an
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

/-- **Form-preservation does not require a coherent parameter either, and is not a property of the parameter
alone.** The very same incoherent mask destroys the form on present factors yet preserves it (result is an
assemblage) on absent factors. Form-preservation is a factor-parameter interaction, not a mask property. -/
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

/-! ## (a) Presence-coherence necessity (mechanization) -/

/-- **Presence-coherence is necessary for partialization commutation** (the dual of the absence extraction).
Commutation forces the masks to agree at each present region-1 cell. -/
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

/-! ## (d) An intrinsic positive predicate for assemblage form (binary) -/

/-- Region-2 independence: a region-c2 cell depends only on coordinate 2. -/
theorem assemblage_region2_independent {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (x1 x1' : X1) (z2 w2 : X2) (h : z2 ≠ w2) :
    assembleClassify c1 c2 imp (x1, z2) (x1, w2) = assembleClassify c1 c2 imp (x1', z2) (x1', w2) :=
  ((factors_determine_the_shared_region c1 c2 imp (x1, z2) (x1, w2)).2 rfl h).trans
    ((factors_determine_the_shared_region c1 c2 imp (x1', z2) (x1', w2)).2 rfl h).symm

/-- The intrinsic predicate: region-1 and region-2 cells each depend only on their own coordinate. Refers to no
factorization. -/
def isAssemblage2 {X1 X2 : Type} (A : (X1 × X2) → (X1 × X2) → Option Bool) : Prop :=
  (∀ x1 y1 : X1, ∀ z z' : X2, A (x1, z) (y1, z) = A (x1, z') (y1, z'))
    ∧ (∀ x1 x1' : X1, ∀ z2 w2 : X2, z2 ≠ w2 → A (x1, z2) (x1, w2) = A (x1', z2) (x1', w2))

/-- **The positive characterization.** A classification is a binary assemblage IFF it satisfies the two
region-independence conditions. Sufficiency reconstructs the factors from basepoints, so "is an assemblage" is
checkable with no reference to any factorization. -/
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

/-! ## (e) A stepwise form-preserving path -/

/-- **A single-cell step leaves the form.** Opening one region-1 cell breaks its constancy across the shared
coordinate: the result is not an assemblage. The minimal form-preserving step cannot be a single cell. -/
theorem single_cell_partialization_leaves_form :
    ∃ (A : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool) (w : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Bool),
      isAssemblage2 A ∧ ¬ isAssemblage2 (partialization w A) := by
  refine ⟨(fun _ _ => some true), (fun a b => decide (a = (0, 0) ∧ b = (1, 0))),
    ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩, ?_⟩
  rintro ⟨hR1, _⟩
  have := hR1 0 1 0 1
  revert this; decide

/-- **A region step (a whole factor) stays in form and moves down.** Emptying one factor keeps the composite an
assemblage and below the original: the form-preserving grain is a region, not a cell. -/
theorem factorwise_step_stays_in_form {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (w1 : X1 → X1 → Bool) (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) :
    (∃ d1 d2 dimp, assembleClassify (partialization w1 c1) c2 imp = assembleClassify d1 d2 dimp)
      ∧ cLE (assembleClassify (partialization w1 c1) c2 imp) (assembleClassify c1 c2 imp) :=
  ⟨⟨partialization w1 c1, c2, imp, rfl⟩, assembleClassify_mono_c1 c2 imp (partialization_le_c w1 c1)⟩

/-- **A region-stepwise path reaches the order-bottom in form.** Emptying every factor lands on `botC`, and each
intermediate is an assemblage. The endpoint is reached by form-preserving region steps. -/
theorem factorwise_reaches_bottom_in_form {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) :
    assembleClassify (partialization (fun _ _ => true) c1) (partialization (fun _ _ => true) c2)
        (partialization (fun _ _ => true) imp) = botC (X1 × X2) := by
  rw [full_partialization_is_bot, full_partialization_is_bot, full_partialization_is_bot]
  exact bottom_stays_in_form.symm

/-! ## (c) The general n-ary assemblage

Carrier `∀ i, X i` (heterogeneous product over `Fin n`). Uniform region description: classify a pair by the
unique coordinate it differs in, if exactly one; else the cross import. -/

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- Two points differ in exactly coordinate `i`. -/
abbrev differsInOne (a b : ∀ i, X i) (i : Fin n) : Prop := a i ≠ b i ∧ ∀ j, j ≠ i → a j = b j

/-- **The differing coordinate is unique.** -/
theorem differsInOne_unique {a b : ∀ i, X i} {p q : Fin n}
    (hp : differsInOne a b p) (hq : differsInOne a b q) : p = q := by
  by_contra hpq; exact hp.1 (hq.2 p hpq)

/-- The general n-ary assemblage: the unique differing coordinate picks its factor, else the import. -/
noncomputable def nary (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    (∀ i, X i) → (∀ i, X i) → Option Bool :=
  fun a b => if h : ∃ i, differsInOne a b i then c h.choose (a h.choose) (b h.choose) else imp a b

/-- On a pair differing in exactly `i`, the n-ary reads factor `i` at that coordinate. -/
theorem nary_apply_differ (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) {a b : ∀ i, X i} {i : Fin n}
    (hi : differsInOne a b i) : nary c imp a b = c i (a i) (b i) := by
  have hex : ∃ i, differsInOne a b i := ⟨i, hi⟩
  have hch : hex.choose = i := differsInOne_unique hex.choose_spec hi
  unfold nary; rw [dif_pos hex, hch]

/-- On a pair differing in more than one coordinate (or none), the n-ary reads the import. -/
theorem nary_apply_imp (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) {a b : ∀ i, X i}
    (hne : ¬ ∃ i, differsInOne a b i) : nary c imp a b = imp a b := by
  unfold nary; rw [dif_neg hne]

/-- **The n-ary is monotone in every factor and the import**, for the same reason: the partition depends only on
the pair. -/
theorem nary_mono {c c' : ∀ i, X i → X i → Option Bool}
    {imp imp' : (∀ i, X i) → (∀ i, X i) → Option Bool}
    (h : ∀ i, cLE (c i) (c' i)) (hi : cLE imp imp') : cLE (nary c imp) (nary c' imp') := by
  intro a b
  by_cases hex : ∃ i, differsInOne a b i
  · rw [nary_apply_differ c imp hex.choose_spec, nary_apply_differ c' imp' hex.choose_spec]
    exact h hex.choose (a hex.choose) (b hex.choose)
  · rw [nary_apply_imp c imp hex, nary_apply_imp c' imp' hex]; exact hi a b

/-- **The n-ary form signature: a differ-in-`i` cell depends only on coordinate `i`.** The axiom-free necessary
signature, uniform in `n`. -/
theorem nary_region_independent (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) {a b a' b' : ∀ i, X i} {i : Fin n}
    (hi : differsInOne a b i) (hi' : differsInOne a' b' i) (ha : a i = a' i) (hb : b i = b' i) :
    nary c imp a b = nary c imp a' b' := by
  rw [nary_apply_differ c imp hi, nary_apply_differ c imp hi', ha, hb]

/-- The intrinsic n-ary predicate: every differ-in-one cell depends only on its own coordinate. No factorization. -/
def isAssemblageN (A : (∀ i, X i) → (∀ i, X i) → Option Bool) : Prop :=
  ∀ (a b a' b' : ∀ i, X i) (i : Fin n), differsInOne a b i → differsInOne a' b' i →
    a i = a' i → b i = b' i → A a b = A a' b'

/-- **The positive characterization, general `n`.** A classification is an n-ary assemblage IFF every
differ-in-one cell depends only on its coordinate. Sufficiency reconstructs each factor from a basepoint via
`Function.update`, so "is an n-ary assemblage" is checkable with no reference to any factorization. -/
theorem nary_form_iff [∀ i, Inhabited (X i)] (A : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    (∃ c imp, A = nary c imp) ↔ isAssemblageN A := by
  constructor
  · rintro ⟨c, imp, rfl⟩ a b a' b' i hi hi' ha hb
    exact nary_region_independent c imp hi hi' ha hb
  · intro hInd
    refine ⟨fun i x y => A (Function.update (fun _ => default) i x) (Function.update (fun _ => default) i y),
      A, ?_⟩
    funext a b
    by_cases hex : ∃ i, differsInOne a b i
    · rw [nary_apply_differ _ _ hex.choose_spec]
      refine hInd a b _ _ hex.choose hex.choose_spec
        ⟨?_, fun j hj => ?_⟩ ?_ ?_
      · simp only [Function.update_self]; exact hex.choose_spec.1
      · simp only [Function.update_of_ne hj]
      · simp only [Function.update_self]
      · simp only [Function.update_self]
    · rw [nary_apply_imp _ _ hex]

/-- **The coherence condition unifies.** The `n` per-region conditions collapse to ONE condition quantified over
the differing coordinate; the import is handled by totalizing with `s`. This is the uniform closed form: one
condition plus the import, not `n` separate ones. -/
theorem nary_totalization_commutes (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (hs : ∀ a b : ∀ i, X i, ∀ hex : ∃ i, differsInOne a b i,
      decide (s b ≤ s a) = decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose))) :
    totalization s (nary c imp)
      = nary (fun i => totalization (si i) (c i)) (totalization s imp) := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · have hL : totalization s (nary c imp) a b
        = some ((c hex.choose (a hex.choose) (b hex.choose)).getD (decide (s b ≤ s a))) := by
      simp only [totalization, nary_apply_differ c imp hex.choose_spec]
    have hR : nary (fun i => totalization (si i) (c i)) (totalization s imp) a b
        = some ((c hex.choose (a hex.choose) (b hex.choose)).getD
            (decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose)))) := by
      rw [nary_apply_differ (fun i => totalization (si i) (c i)) (totalization s imp) hex.choose_spec]
      simp only [totalization]
    rw [hL, hR, hs a b hex]
  · have hL : totalization s (nary c imp) a b = some ((imp a b).getD (decide (s b ≤ s a))) := by
      simp only [totalization, nary_apply_imp c imp hex]
    have hR : nary (fun i => totalization (si i) (c i)) (totalization s imp) a b
        = some ((imp a b).getD (decide (s b ≤ s a))) := by
      rw [nary_apply_imp (fun i => totalization (si i) (c i)) (totalization s imp) hex]
      simp only [totalization]
    rw [hL, hR]

/-- **The monotone/non-monotone split reproduces at general `n`.** Assembling partialized factors is below the
n-ary composite, hence a partialization of it (unconditional, structural). -/
theorem nary_assembled_partialization_is_below (w : ∀ i, X i → X i → Bool)
    (w' : (∀ i, X i) → (∀ i, X i) → Bool) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    cLE (nary (fun i => partialization (w i) (c i)) (partialization w' imp)) (nary c imp) :=
  nary_mono (fun i => partialization_le_c (w i) (c i)) (partialization_le_c w' imp)

theorem nary_assembled_partialization_is_a_partialization (w : ∀ i, X i → X i → Bool)
    (w' : (∀ i, X i) → (∀ i, X i) → Bool) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    ∃ W, nary (fun i => partialization (w i) (c i)) (partialization w' imp)
        = partialization W (nary c imp) :=
  (below_iff_partialization _ _).1 (nary_assembled_partialization_is_below w w' c imp)

/-! ## (ii) The form-preserving path as an explicit chain

A `Nat`-indexed descent: at step `k` the first `k` factors are emptied (a region step each), then the import.
Every intermediate is a `nary` (hence in form), the chain descends in `cLE`, and it reaches `botC`. -/

/-- `nary` of all-absent factors and absent import is the bottom. -/
theorem nary_bot : nary (fun i => botC (X i)) (botC (∀ i, X i)) = botC (∀ i, X i) := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · rw [nary_apply_differ (fun i => botC (X i)) (botC (∀ i, X i)) hex.choose_spec]; rfl
  · rw [nary_apply_imp (fun i => botC (X i)) (botC (∀ i, X i)) hex]

/-- `nary` of total factors and total import is total (a maximal element). -/
theorem nary_isTotal {c : ∀ i, X i → X i → Option Bool} {imp : (∀ i, X i) → (∀ i, X i) → Option Bool}
    (hc : ∀ i, isTotal (c i)) (hi : isTotal imp) : isTotal (nary c imp) := by
  intro a b
  by_cases hex : ∃ i, differsInOne a b i
  · rw [nary_apply_differ c imp hex.choose_spec]; exact hc hex.choose (a hex.choose) (b hex.choose)
  · rw [nary_apply_imp c imp hex]; exact hi a b

/-- Factors of the descent at step `k`: the first `k` emptied. -/
noncomputable def descentFactors (c : ∀ i, X i → X i → Option Bool) (k : Nat) :
    ∀ i, X i → X i → Option Bool := fun i => if i.val < k then botC (X i) else c i

/-- Import of the descent: emptied only after all factors. -/
noncomputable def descentImp (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) :
    (∀ i, X i) → (∀ i, X i) → Option Bool := if n < k then botC (∀ i, X i) else imp

/-- The descent chain. -/
noncomputable def descentPath (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) : (∀ i, X i) → (∀ i, X i) → Option Bool :=
  nary (descentFactors c k) (descentImp imp k)

/-- The chain starts at the given assemblage. -/
theorem descentPath_zero (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) : descentPath c imp 0 = nary c imp := by
  have hf : descentFactors c 0 = c := by
    funext i; simp only [descentFactors]; rw [if_neg (by omega : ¬ i.val < 0)]
  have himp : descentImp imp 0 = imp := by
    simp only [descentImp]; rw [if_neg (by omega : ¬ n < 0)]
  unfold descentPath; rw [hf, himp]

/-- **Every intermediate is in form.** Each `descentPath` step is a `nary`, hence an n-ary assemblage. -/
theorem descentPath_isAssemblageN [∀ i, Inhabited (X i)] (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) : isAssemblageN (descentPath c imp k) :=
  (nary_form_iff _).mp ⟨descentFactors c k, descentImp imp k, rfl⟩

/-- **The chain descends in the information order.** Each step empties one region. -/
theorem descentPath_descends (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) :
    cLE (descentPath c imp (k + 1)) (descentPath c imp k) := by
  unfold descentPath
  apply nary_mono
  · intro i; simp only [descentFactors]
    by_cases h2 : i.val < k + 1
    · by_cases h1 : i.val < k
      · rw [if_pos h2, if_pos h1]; exact cLE_refl _
      · rw [if_pos h2, if_neg h1]; exact botC_le _
    · rw [if_neg h2, if_neg (show ¬ i.val < k by omega)]; exact cLE_refl _
  · simp only [descentImp]
    by_cases h2 : n < k + 1
    · by_cases h1 : n < k
      · rw [if_pos h2, if_pos h1]; exact cLE_refl _
      · rw [if_pos h2, if_neg h1]; exact botC_le _
    · rw [if_neg h2, if_neg (show ¬ n < k by omega)]; exact cLE_refl _

/-- **The chain terminates at the order-bottom.** After `n+1` steps everything is emptied. -/
theorem descentPath_reaches_bot (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) : descentPath c imp (n + 1) = botC (∀ i, X i) := by
  have hf : descentFactors c (n + 1) = fun i => botC (X i) := by
    funext i; simp only [descentFactors]; rw [if_pos (Nat.lt_succ_of_lt i.isLt)]
  have himp : descentImp imp (n + 1) = botC (∀ i, X i) := by
    simp only [descentImp]; rw [if_pos (Nat.lt_succ_self n)]
  unfold descentPath; rw [hf, himp, nary_bot]

/-! ### The ascent chain, and the reach asymmetry -/

/-- Factors of the ascent at step `k`: the first `k` totalized. -/
noncomputable def ascentFactors (si : ∀ i, X i → Nat) (c : ∀ i, X i → X i → Option Bool) (k : Nat) :
    ∀ i, X i → X i → Option Bool := fun i => if i.val < k then totalization (si i) (c i) else c i

noncomputable def ascentImp (s : (∀ i, X i) → Nat) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) :
    (∀ i, X i) → (∀ i, X i) → Option Bool := if n < k then totalization s imp else imp

noncomputable def ascentPath (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) :
    (∀ i, X i) → (∀ i, X i) → Option Bool := nary (ascentFactors si c k) (ascentImp s imp k)

theorem ascentPath_zero (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    ascentPath s si c imp 0 = nary c imp := by
  have hf : ascentFactors si c 0 = c := by
    funext i; simp only [ascentFactors]; rw [if_neg (by omega : ¬ i.val < 0)]
  have himp : ascentImp s imp 0 = imp := by
    simp only [ascentImp]; rw [if_neg (by omega : ¬ n < 0)]
  unfold ascentPath; rw [hf, himp]

theorem ascentPath_isAssemblageN [∀ i, Inhabited (X i)] (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) :
    isAssemblageN (ascentPath s si c imp k) :=
  (nary_form_iff _).mp ⟨ascentFactors si c k, ascentImp s imp k, rfl⟩

/-- **The ascent ascends.** Each step totalizes one region. -/
theorem ascentPath_ascends (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) :
    cLE (ascentPath s si c imp k) (ascentPath s si c imp (k + 1)) := by
  unfold ascentPath
  apply nary_mono
  · intro i; simp only [ascentFactors]
    by_cases h1 : i.val < k
    · rw [if_pos h1, if_pos (show i.val < k + 1 by omega)]; exact cLE_refl _
    · by_cases h2 : i.val < k + 1
      · rw [if_neg h1, if_pos h2]; exact c_le_totalization _ _
      · rw [if_neg h1, if_neg h2]; exact cLE_refl _
  · simp only [ascentImp]
    by_cases h1 : n < k
    · rw [if_pos h1, if_pos (show n < k + 1 by omega)]; exact cLE_refl _
    · by_cases h2 : n < k + 1
      · rw [if_neg h1, if_pos h2]; exact c_le_totalization _ _
      · rw [if_neg h1, if_neg h2]; exact cLE_refl _

/-- **The ascent reaches one scale-forced ceiling**, not an arbitrary maximum: the endpoint is
`nary (totalizations) (totalized import)`, fully determined by the scales. -/
theorem ascentPath_reaches_ceiling (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    ascentPath s si c imp (n + 1)
      = nary (fun i => totalization (si i) (c i)) (totalization s imp) := by
  have hf : ascentFactors si c (n + 1) = fun i => totalization (si i) (c i) := by
    funext i; simp only [ascentFactors]; rw [if_pos (Nat.lt_succ_of_lt i.isLt)]
  have himp : ascentImp s imp (n + 1) = totalization s imp := by
    simp only [ascentImp]; rw [if_pos (Nat.lt_succ_self n)]
  unfold ascentPath; rw [hf, himp]

/-- The ascent endpoint is a maximal element (total). -/
theorem ascentPath_ceiling_isTotal (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    isTotal (ascentPath s si c imp (n + 1)) := by
  rw [ascentPath_reaches_ceiling]
  exact nary_isTotal (fun i => totalization_isTotal (si i) (c i)) (totalization_isTotal s imp)

/-- **The path is a family, not a canonical trajectory.** The first region step already depends on which factor
is emptied: emptying factor 1 first differs from emptying factor 2 first. All trajectories share the endpoints. -/
theorem descent_path_is_a_family :
    ∃ (c1 c2 : Fin 2 → Fin 2 → Option Bool) (imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool),
      assembleClassify (partialization (fun _ _ => true) c1) c2 imp
        ≠ assembleClassify c1 (partialization (fun _ _ => true) c2) imp := by
  refine ⟨(fun _ _ => some true), (fun _ _ => some false), (fun _ _ => none), ?_⟩
  intro h
  have hcell := congrFun (congrFun h (0, 0)) (1, 0)
  revert hcell; decide

/-! ## (i) General-n refinements: absence/presence and the necessity extractions -/

/-- **General-n absence refinement.** The coherence condition need hold only at absent differ-in-one cells. -/
theorem nary_totalization_commutes_on_absences (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (hs : ∀ a b : ∀ i, X i, ∀ hex : ∃ i, differsInOne a b i,
      c hex.choose (a hex.choose) (b hex.choose) = none →
      decide (s b ≤ s a) = decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose))) :
    totalization s (nary c imp)
      = nary (fun i => totalization (si i) (c i)) (totalization s imp) := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · have hL : totalization s (nary c imp) a b
        = some ((c hex.choose (a hex.choose) (b hex.choose)).getD (decide (s b ≤ s a))) := by
      simp only [totalization, nary_apply_differ c imp hex.choose_spec]
    have hR : nary (fun i => totalization (si i) (c i)) (totalization s imp) a b
        = some ((c hex.choose (a hex.choose) (b hex.choose)).getD
            (decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose)))) := by
      rw [nary_apply_differ (fun i => totalization (si i) (c i)) (totalization s imp) hex.choose_spec]
      simp only [totalization]
    rw [hL, hR]
    rcases hc : c hex.choose (a hex.choose) (b hex.choose) with _ | v
    · rw [Option.getD_none, Option.getD_none, hs a b hex hc]
    · rw [Option.getD_some, Option.getD_some]
  · have hL : totalization s (nary c imp) a b = some ((imp a b).getD (decide (s b ≤ s a))) := by
      simp only [totalization, nary_apply_imp c imp hex]
    have hR : nary (fun i => totalization (si i) (c i)) (totalization s imp) a b
        = some ((imp a b).getD (decide (s b ≤ s a))) := by
      rw [nary_apply_imp (fun i => totalization (si i) (c i)) (totalization s imp) hex]
      simp only [totalization]
    rw [hL, hR]

/-- **General-n necessity (totalization).** Commutation forces absence-coherence at each absent differ-in-one
cell. With the sufficiency above this is the tight iff, in the quantified-coordinate form. -/
theorem nary_totalization_commutation_forces_absence_coherence (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (h : totalization s (nary c imp) = nary (fun i => totalization (si i) (c i)) (totalization s imp))
    (a b : ∀ i, X i) (hex : ∃ i, differsInOne a b i)
    (hc : c hex.choose (a hex.choose) (b hex.choose) = none) :
    decide (s b ≤ s a) = decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose)) := by
  have hcong := congrFun (congrFun h a) b
  have hL : totalization s (nary c imp) a b = some (decide (s b ≤ s a)) := by
    simp only [totalization, nary_apply_differ c imp hex.choose_spec, hc, Option.getD_none]
  have hR : nary (fun i => totalization (si i) (c i)) (totalization s imp) a b
      = some (decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose))) := by
    rw [nary_apply_differ (fun i => totalization (si i) (c i)) (totalization s imp) hex.choose_spec]
    simp only [totalization, hc, Option.getD_none]
  rw [hL, hR] at hcong
  exact Option.some_inj.mp hcong

/-- **General-n presence refinement (partialization sufficiency).** The mask need agree only at present
differ-in-one cells. -/
theorem nary_partialization_commutes_on_presences (w : (∀ i, X i) → (∀ i, X i) → Bool)
    (wi : ∀ i, X i → X i → Bool) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (hw : ∀ a b : ∀ i, X i, ∀ hex : ∃ i, differsInOne a b i,
      c hex.choose (a hex.choose) (b hex.choose) ≠ none →
      w a b = wi hex.choose (a hex.choose) (b hex.choose)) :
    partialization w (nary c imp)
      = nary (fun i => partialization (wi i) (c i)) (partialization w imp) := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · have hL : partialization w (nary c imp) a b
        = (if w a b then none else c hex.choose (a hex.choose) (b hex.choose)) := by
      simp only [partialization, nary_apply_differ c imp hex.choose_spec]
    have hR : nary (fun i => partialization (wi i) (c i)) (partialization w imp) a b
        = (if wi hex.choose (a hex.choose) (b hex.choose) then none
            else c hex.choose (a hex.choose) (b hex.choose)) := by
      rw [nary_apply_differ (fun i => partialization (wi i) (c i)) (partialization w imp) hex.choose_spec]
      simp only [partialization]
    rw [hL, hR]
    rcases hc : c hex.choose (a hex.choose) (b hex.choose) with _ | v
    · simp
    · rw [hw a b hex (by rw [hc]; exact Option.some_ne_none v)]
  · have hL : partialization w (nary c imp) a b = (if w a b then none else imp a b) := by
      simp only [partialization, nary_apply_imp c imp hex]
    have hR : nary (fun i => partialization (wi i) (c i)) (partialization w imp) a b
        = (if w a b then none else imp a b) := by
      rw [nary_apply_imp (fun i => partialization (wi i) (c i)) (partialization w imp) hex]
      simp only [partialization]
    rw [hL, hR]

/-- **General-n necessity (partialization).** Commutation forces presence-coherence at each present differ-in-one
cell. With the sufficiency above this is the general-n presence-coherence iff. -/
theorem nary_partialization_commutation_forces_presence_coherence (w : (∀ i, X i) → (∀ i, X i) → Bool)
    (wi : ∀ i, X i → X i → Bool) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (h : partialization w (nary c imp) = nary (fun i => partialization (wi i) (c i)) (partialization w imp))
    (a b : ∀ i, X i) (hex : ∃ i, differsInOne a b i) (v : Bool)
    (hc : c hex.choose (a hex.choose) (b hex.choose) = some v) :
    w a b = wi hex.choose (a hex.choose) (b hex.choose) := by
  have hcong := congrFun (congrFun h a) b
  have hL : partialization w (nary c imp) a b = (if w a b then none else some v) := by
    simp only [partialization, nary_apply_differ c imp hex.choose_spec, hc]
  have hR : nary (fun i => partialization (wi i) (c i)) (partialization w imp) a b
      = (if wi hex.choose (a hex.choose) (b hex.choose) then none else some v) := by
    rw [nary_apply_differ (fun i => partialization (wi i) (c i)) (partialization w imp) hex.choose_spec]
    simp only [partialization, hc]
  rw [hL, hR] at hcong
  by_cases hw : w a b = true
  · by_cases hw1 : wi hex.choose (a hex.choose) (b hex.choose) = true
    · rw [hw, hw1]
    · rw [if_pos hw, if_neg hw1] at hcong; exact absurd hcong (by simp)
  · by_cases hw1 : wi hex.choose (a hex.choose) (b hex.choose) = true
    · rw [if_neg hw, if_pos hw1] at hcong; exact absurd hcong (by simp)
    · rw [Bool.not_eq_true] at hw hw1; rw [hw, hw1]

/-! ## (iii) A canonical uniform scale at arbitrary n

The coherence condition compares only points differing in ONE coordinate, so all other coordinates cancel: no
mixed radix is needed. The plain sum of per-coordinate scales works, for any `n` and any per-coordinate scales,
with no finiteness or ordering hypothesis on the `X i` beyond the scales themselves. -/

open Finset in
/-- **The sum scale realizes coherence.** For per-coordinate scales `si`, the scale `a ↦ ∑ j, si j (a j)`
satisfies the single quantified coherence condition, because on a differ-in-one pair every other summand cancels. -/
theorem nary_sum_scale_coherent (si : ∀ i, X i → Nat) (a b : ∀ i, X i)
    (hex : ∃ i, differsInOne a b i) :
    decide ((∑ j, si j (b j)) ≤ ∑ j, si j (a j))
      = decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose)) := by
  have hi : differsInOne a b hex.choose := hex.choose_spec
  have htail : (∑ j ∈ univ.erase hex.choose, si j (a j)) = ∑ j ∈ univ.erase hex.choose, si j (b j) :=
    Finset.sum_congr rfl (fun j hj => by rw [hi.2 j (Finset.ne_of_mem_erase hj)])
  have ha : (∑ j, si j (a j)) = si hex.choose (a hex.choose) + ∑ j ∈ univ.erase hex.choose, si j (a j) :=
    (Finset.add_sum_erase univ (fun j => si j (a j)) (mem_univ hex.choose)).symm
  have hb : (∑ j, si j (b j)) = si hex.choose (b hex.choose) + ∑ j ∈ univ.erase hex.choose, si j (b j) :=
    (Finset.add_sum_erase univ (fun j => si j (b j)) (mem_univ hex.choose)).symm
  rw [ha, hb, htail]
  simp only [add_le_add_iff_right]

open Finset in
/-- **A canonical scale for commutation at every `n`.** Totalizing by the sum scale commutes with assembling the
per-coordinate totalizations. Uniform, no side condition beyond the per-coordinate scales. -/
theorem nary_totalization_commutes_sum (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    totalization (fun a => ∑ j, si j (a j)) (nary c imp)
      = nary (fun i => totalization (si i) (c i)) (totalization (fun a => ∑ j, si j (a j)) imp) :=
  nary_totalization_commutes _ si c imp (fun a b hex => nary_sum_scale_coherent si a b hex)

/-! ## (1) The path quotient: the intermediate depends only on the emptied set

Emptying a factor is `Function.update` to `botC`. Distinct factors commute, so the intermediate after emptying a
set of regions is independent of the order: the quotient of the path-family is the Boolean lattice of
subsets-of-regions-emptied. -/

/-- Emptying one factor: replace it by the absent classification. -/
def emptyFactor (i : Fin n) (c : ∀ i, X i → X i → Option Bool) : ∀ i, X i → X i → Option Bool :=
  Function.update c i (botC (X i))

/-- **Emptying distinct factors commutes.** The generator of order-independence. -/
theorem emptyFactor_comm {i j : Fin n} (hij : i ≠ j) (c : ∀ i, X i → X i → Option Bool) :
    emptyFactor i (emptyFactor j c) = emptyFactor j (emptyFactor i c) := by
  simp only [emptyFactor]; rw [Function.update_comm hij.symm]

/-- Emptying the same factor twice is emptying it once. -/
theorem emptyFactor_idem (i : Fin n) (c : ∀ i, X i → X i → Option Bool) :
    emptyFactor i (emptyFactor i c) = emptyFactor i c := by
  simp only [emptyFactor, Function.update_idem]

/-- The set-indexed intermediate: emptied factors given by a `Finset`, import by a `Bool`. -/
noncomputable def descentBySet (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (F : Finset (Fin n)) (e : Bool) :
    (∀ i, X i) → (∀ i, X i) → Option Bool :=
  nary (fun i => if i ∈ F then botC (X i) else c i) (if e then botC (∀ i, X i) else imp)

/-- **The ordered descent factors through the set-indexed intermediate.** So the family of descent paths is the
set of maximal chains in the Boolean lattice `Finset (Fin n) × Bool`, and the quotient (identify intermediates by
emptied-set) is that lattice: two orderings share an intermediate exactly when they have emptied the same set. -/
theorem descentPath_eq_bySet (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) :
    descentPath c imp k
      = descentBySet c imp (Finset.univ.filter (fun i => i.val < k)) (decide (n < k)) := by
  unfold descentPath descentBySet
  congr 1
  · funext i; simp only [descentFactors, Finset.mem_filter, Finset.mem_univ, true_and]
  · simp only [descentImp]; by_cases h : n < k <;> simp [h]

/-! ## (2) A general-n order-dependence witness -/

/-- **Order dependence at the n-ary.** Emptying factor 0 first differs from emptying factor 1 first: the two
single-region steps give different intermediates (`n = 2`). Same phenomenon as the binary witness, at the arity
the theory now uses. -/
theorem descent_path_is_a_family_nary :
    ∃ (c : ∀ _ : Fin 2, Fin 2 → Fin 2 → Option Bool)
      (imp : (∀ _ : Fin 2, Fin 2) → (∀ _ : Fin 2, Fin 2) → Option Bool)
      (a b : ∀ _ : Fin 2, Fin 2),
      nary (emptyFactor 0 c) imp a b ≠ nary (emptyFactor 1 c) imp a b := by
  refine ⟨fun _ => fun _ _ => some true, fun _ _ => none, ![0, 0], ![1, 0], ?_⟩
  have hd : differsInOne (![0, 0] : ∀ _ : Fin 2, Fin 2) ![1, 0] 0 := by decide
  rw [nary_apply_differ _ _ hd, nary_apply_differ _ _ hd]
  decide

/-! ## (3) Incomparable ceilings, packaged -/

/-- **Distinct ascent ceilings are incomparable.** The only hypothesis is that the endpoints differ: both are
total (hence maximal), so distinctness forces incomparability. -/
theorem ascent_ceilings_incomparable
    (s s' : (∀ i, X i) → Nat) (si si' : ∀ i, X i → Nat)
    (c c' : ∀ i, X i → X i → Option Bool) (imp imp' : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (hne : ascentPath s si c imp (n + 1) ≠ ascentPath s' si' c' imp' (n + 1)) :
    ¬ cLE (ascentPath s si c imp (n + 1)) (ascentPath s' si' c' imp' (n + 1))
      ∧ ¬ cLE (ascentPath s' si' c' imp' (n + 1)) (ascentPath s si c imp (n + 1)) :=
  distinct_maxima_incomparable _ _ (ascentPath_ceiling_isTotal s si c imp)
    (ascentPath_ceiling_isTotal s' si' c' imp') hne

end Chiralogy.AssemblageDynamics
