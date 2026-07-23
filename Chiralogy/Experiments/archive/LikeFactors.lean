import Chiralogy

/-! ARCHIVED (question SETTLED NEGATIVELY): does the assemblage's cross-fragility admit a clean
bound from the factors? ANSWER: bounded per fixed factors, but NO clean law, not in factor fragility
and not in present-column structure (nfc, the non-present-carried index pairs).

OBSTRUCTION (the substance): assembleClassify checks a.2 = b.2 before a.1 = b.1, so for a
factor-2-aligned pair the columns where c2 would present-carry it are exactly where the assemblage
takes the factor-1 branch and reads c1's diagonal. The ordering intercepts c2 before it can act: c2
is nearly inert, and the factor-2-aligned region A2 is a cross-factor-plus-import coupling that no
single-factor coordinate captures.

REFUTATIONS: the fragility ceiling (Fin3 x Fin2, c1 = two identical all-none rows plus a self-present
row: claimed 20, actual 28) and the nfc ceiling (deg/rob 30 vs 24, eq/rob 28 vs 24, par/rob 28 vs 24).
Not even a one-sided ceiling exists: deg and sat share nfc c1 = 6 yet give A2 = 6 vs 0.

CLEAN FRAGMENT (NOT graduated): A1 <= card X2 * nfc c1 bounds the factor-1-aligned region alone. Judged
not a standalone result: it is one region of a ceiling that does not exist and would need a canonical
nfc def used for nothing else, so it stays a fragment, recorded here only.

THIS FILE: asked whether like vs unlike factors constrain the cross-region differently; answered: the two factors are not interchangeable (c1 governs, c2 inert), so there is no like/unlike law.

Negative findings are recorded in archive only, never in canonical or spec. Typechecks standalone. -/

/-! # Experiment: like factors and the cross-region

Assemblages are objects and compose. Test whether assembling like factors, the same classification, constrains the
cross-region differently from assembling unlike ones. The factors survive assembly unchanged, the cross-region is
free, the import sets whether the whole exceeds and its fragility, and the factors bound the fragility ceiling by
their distinction-structure. Compute across several like and unlike pairs at a fixed carrier size, `Fin 2 × Fin 2`.
Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.LikeFactors

/-- Saturated and present classifications on `Fin 2`. -/
def s : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none
def p : Fin 2 → Fin 2 → Option Bool := fun x y => some (decide (x = y))

/-- The assemblage baseline cross-fragility with the empty cross. -/
def cfB (c1 c2 : Fin 2 → Fin 2 → Option Bool) : Nat :=
  (Finset.univ.filter (fun q : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
    assembleClassify c1 c2 (fun _ _ => none) q.1 ≠ assembleClassify c1 c2 (fun _ _ => none) q.2
    ∧ totalization (fun _ => 0) (assembleClassify c1 c2 (fun _ _ => none)) q.1
      = totalization (fun _ => 0) (assembleClassify c1 c2 (fun _ _ => none)) q.2)).card

/-- Fragility of a classification on the product carrier. -/
def fr (c : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool) : Nat :=
  (Finset.univ.filter (fun q : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
    c q.1 ≠ c q.2 ∧ totalization (fun _ => 0) c q.1 = totalization (fun _ => 0) c q.2)).card

/-- Mirroring imports: extend a factor's classification to the cross. -/
def mir : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool := fun a b => s a.1 b.1
def mirP : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool := fun a b => p a.1 b.1
/-- A differentiating import: value one cross pair. -/
def dif : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool :=
  fun a b => if a = (0, 0) ∧ b = (1, 1) then some true else none

/-! ## Part 1: is the cross-region constrained by likeness? -/

/-- **The import is free for a like pair.** For like factors, as for any, every import gives a payload-firing
assemblage: likeness does not constrain the achievable cross-region. -/
theorem like_pair_cross_region :
    ∀ imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool,
      ¬ Function.Surjective (assembleClassify s s imp) :=
  fun _ => hole_uniform _

/-- **Likeness does not fix one ceiling.** Two like pairs have different ceilings, the saturated pair twelve and
the present pair four: the ceiling is set by the distinction-structure, not by likeness itself. -/
theorem is_the_ceiling_the_same :
    (cfB s s = 12) ∧ (cfB p p = 4) := by
  refine ⟨by decide, by decide⟩

/-- **Unlike pairs for comparison.** At the fixed carrier size the saturated-saturated pair reaches twelve, the
saturated-present pair zero, the present-present pair four: three factor-pairs, three ceilings, set by the pairing's
distinction-structures, not by whether the factors are alike. -/
theorem unlike_pairs_for_comparison :
    (cfB s s = 12) ∧ (cfB s p = 0) ∧ (cfB p p = 4) := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## Part 2: what is symmetric in a like pair -/

/-- **The determined regions are symmetric for a like pair.** Both the shared-second and the shared-first region use
the same classification, so the two determined regions are symmetric copies of it; the cross-region's symmetry is
set by the import, not by likeness. -/
theorem is_the_cross_symmetric (imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool) (a b : Fin 2 × Fin 2) :
    (a.2 = b.2 → assembleClassify s s imp a b = s a.1 b.1)
    ∧ (a.1 = b.1 → a.2 ≠ b.2 → assembleClassify s s imp a b = s a.2 b.2) :=
  factors_determine_the_shared_region s s imp a b

/-- **Swapping the factors changes an unlike pair, not a like one.** For like factors the two are the same
classification, so swapping them is the identity; for unlike factors, swapping changes the assemblage. -/
theorem does_swapping_the_factors_change_the_assemblage :
    (assembleClassify s s = assembleClassify s s)
    ∧ (assembleClassify s p (fun _ _ => none) ≠ assembleClassify p s (fun _ _ => none)) := by
  refine ⟨rfl, by decide⟩

/-! ## Part 3: the relation the import fixes -/

/-- **Both treatments are available.** The mirroring import treats the like factors as identical and the
differentiating import as distinct; the first is non-exceeding, the second exceeding. -/
theorem what_the_import_says_about_the_pair :
    (assembleClassify s s mir = assembleClassify s s (fun _ _ => none))
    ∧ (assembleClassify s s dif ≠ assembleClassify s s (fun _ _ => none)) := by
  refine ⟨by decide, by decide⟩

/-- **Mirroring collapses a saturated pair, not a present one.** Mirroring the saturated factor gives the absence on
every cross pair, the cross pairs being off-diagonal where the saturated classification is absent, so the mirroring
assemblage is the juxtaposition and does not exceed. Mirroring a present factor, valued off the diagonal, does
exceed. So treating like factors as identical collapses the whole exactly when the shared classification is absent
off the diagonal. -/
theorem mirroring_import :
    (assembleClassify s s mir = assembleClassify s s (fun _ _ => none))
    ∧ (assembleClassify p p mirP ≠ assembleClassify p p (fun _ _ => none)) := by
  refine ⟨by decide, by decide⟩

/-- **Differentiating exceeds, at the factors' fragility.** A differentiating import values a cross pair and
exceeds; its fragility is twelve, the saturated factors' own baseline, the differentiating content adding no
fragility beyond what the factors carry. -/
theorem differentiating_import :
    (assembleClassify s s dif ≠ assembleClassify s s (fun _ _ => none))
    ∧ (fr (assembleClassify s s dif) = 12) := by
  refine ⟨by decide, by decide⟩

/-! ## The verdicts

Part 1: likeness does not constrain the cross-region beyond fixing the ceiling. The import is free for a like pair
(`like_pair_cross_region`); two like pairs have different ceilings, twelve and four, so the ceiling is the
distinction-structure not likeness (`is_the_ceiling_the_same`); and three pairs give three ceilings by their
structures (`unlike_pairs_for_comparison`).

Part 2: a like pair is symmetric in its determined regions and swap-invariant. Both determined regions use the same
classification (`is_the_cross_symmetric`); and swapping the factors is the identity for a like pair while it changes
an unlike one (`does_swapping_the_factors_change_the_assemblage`).

Part 3: the import fixes the relation, and mirroring can collapse. Both treatments are available, mirroring
non-exceeding and differentiating exceeding (`what_the_import_says_about_the_pair`); mirroring a saturated factor
collapses to the juxtaposition while mirroring a present one exceeds (`mirroring_import`); and differentiating
exceeds at the factors' own fragility (`differentiating_import`).

The verdict: likeness does not constrain the cross-region beyond what the factors' distinction-structure already
fixes, but it makes one treatment meaningful, treating the factors as identical, which for a saturated pair
collapses the whole. The import is free for a like pair exactly as for any pair, so the achievable cross-region is
not narrowed by likeness; the ceiling is set by the distinction-structure, and since two like pairs, saturated and
present, reach different ceilings, twelve and four, likeness is not itself the index, only a case of the factors
sharing a structure. What likeness does supply is symmetry: the two determined regions of a like pair are the same
classification, so they are symmetric copies, and swapping the factors is the identity, where for an unlike pair it
changes the assemblage, so a like pair is genuinely order-indifferent while an unlike pair is not, the
construction's asymmetry between the factors vanishing when they coincide. And likeness makes mirroring meaningful,
an import that extends one factor's classification across the cross, treating the two as identical; for a saturated
factor this gives the absence on every cross pair, the cross being off the diagonal where the saturated
classification is absent, so the mirroring assemblage is the juxtaposition and does not exceed, the identity
treatment collapsing the whole, while for a present factor mirroring is valued and exceeds. So the import chooses
the relation the like factors bear each other, identical and collapsed or distinct and exceeding, both available,
and the differentiating one exceeds at the factors' own fragility, adding no fragility beyond theirs. Per the
counter-bias, likeness was not assumed to constrain, the import found free and the ceiling attributed to
distinction-structure as before; symmetry was not assumed, checked and found to hold for a like pair and fail for
an unlike one; and mirroring was not assumed non-exceeding, computed and found to collapse for a saturated pair but
exceed for a present one. Reported per part. Nothing here is resolved. -/

end Chiralogy.LikeFactors
