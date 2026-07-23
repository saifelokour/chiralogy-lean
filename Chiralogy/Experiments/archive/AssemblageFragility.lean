import Chiralogy

/-! ARCHIVED (coordinate settled: NO clean law). The GAINS coordinate: net distinctions created minus destroyed
by totalization (change in the count of distinct row-pairs).

ANSWER: no clean carrier-general law. Net gain is parameter-dependent, negative, zero, or positive depending on
BOTH the classification AND the scale: measured deg +6, mid +2, sat/rob/imp 0 at scale = index; and for one fixed
classification, -2 / 0 / 0 across constant / index / reverse scales. So gain is a choice of import-and-scale, not
a property.

The general mechanism is ALREADY canonical: creation is totalization_separates_equal_rows (a shared absence filled
differently by the scale separates equal rows); survival is survives_totalization; destruction is the absence-
carried merge. The file's own universal theorems are already canonical or trivial: cross_region_carries_the_
emergent_distinctions IS construction_takes_two_objects_and_a_cross_map, and totalization_fills_the_cross_region
is import_is_the_complement composed with totalization_totalizes. The rest (fragile_case, robust_case,
gaining_case) are witnesses that all three outcomes occur; the finding is that the emergent part is import-
dependent, not systematically fragile. No new general law to graduate.

Negative finding recorded in the archive note only, never in canonical or spec. Typechecks standalone. -/

/-! # Experiment: what totalization does to an assemblage

An assemblage locates disagreement in its imported cross-region. Totalization fills every absence, including those.
Test what that does to the assemblage's own structure, and whether the emergent part is fragile, robust, or gains.
Compute all three cases before judging. Degenerate factors isolate all distinction into the cross-region, so the
emergent part can be examined alone. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.AssemblageFragility

/-- Degenerate factors and imports, to isolate the emergent cross-region. -/
def z2 : Fin 2 → Fin 2 → Option Bool := fun _ _ => none
def zA : Fin 3 → Fin 3 → Option Bool := fun _ _ => none
def zB : Fin 2 → Fin 2 → Option Bool := fun _ _ => none
def zP : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool := fun _ _ => none

/-- A present factor, distinguishing at present verdicts. -/
def pres1 : Fin 2 → Fin 2 → Option Bool := fun x y => some (decide (x = y))

/-- A cross-region distinction resting on an absence: one present verdict, the rest absent. -/
def impFrag : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool :=
  fun a b => if a = (0, 0) ∧ b = (1, 1) then some true else none

/-- A present-carried cross distinction: two present verdicts differing at a shared cross-column. -/
def impPres : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool :=
  fun a b => if a = (0, 1) ∧ b = (2, 0) then some true else if a = (1, 1) ∧ b = (2, 0) then some false else none

/-- An absence-carried cross distinction with the same factors, for the import comparison. -/
def impAbs : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool :=
  fun a b => if a = (0, 1) ∧ b = (2, 0) then some true else none

/-- A distinguishing scale on the assemblage carrier. -/
def sc : (Fin 2 × Fin 2) → Nat := fun p => p.1.val * 2 + p.2.val

/-! ## Part 1: does totalization ignore the location? -/

/-- **Totalization fills the cross-region.** A located pair with an absent import was the undetermined absence;
after totalization it is a determinate scale-verdict, filled like any other absence. -/
theorem totalization_fills_the_cross_region {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (s : (X1 × X2) → Nat) (a b : X1 × X2)
    (h1 : a.1 ≠ b.1) (h2 : a.2 ≠ b.2) (hnone : imp a b = none) :
    (assembleClassify c1 c2 imp a b = none)
    ∧ (totalization s (assembleClassify c1 c2 imp) a b ≠ none) := by
  refine ⟨?_, totalization_totalizes s _ a b⟩
  rw [import_is_the_complement c1 c2 imp a b h1 h2]; exact hnone

/-- **The record is overwritten, not resolved.** After totalization the located pair is indistinguishable from an
affirmed one, the undetermined absence and a present verdict totalizing to the same value; but the location
survives as a carrier fact, untouched by totalization. The where survives, the that-it-was-undetermined does not. -/
theorem is_the_disagreement_resolved_or_overwritten :
    (totalization (fun _ => 0) (assembleClassify z2 z2 zP) (0, 0) (1, 1)
      = totalization (fun _ => 0) (assembleClassify z2 z2 impFrag) (0, 0) (1, 1))
    ∧ (((0, 0) : Fin 2 × Fin 2).1 ≠ ((1, 1) : Fin 2 × Fin 2).1
       ∧ ((0, 0) : Fin 2 × Fin 2).2 ≠ ((1, 1) : Fin 2 × Fin 2).2) := by
  refine ⟨by decide, by decide⟩

/-! ## Part 2: the three cases -/

/-- **The cross-region carries the emergent distinctions.** Two assemblages of the same factors agreeing on the
cross-region are equal, so everything that varies with the import, the emergent content, lives there; the factors'
regions replicate the factors. -/
theorem cross_region_carries_the_emergent_distinctions {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp imp' : (X1 × X2) → (X1 × X2) → Option Bool) :
    (∀ a b, a.1 ≠ b.1 → a.2 ≠ b.2 → imp a b = imp' a b) →
    (∀ a b, assembleClassify c1 c2 imp a b = assembleClassify c1 c2 imp' a b) :=
  construction_takes_two_objects_and_a_cross_map c1 c2 imp imp'

/-- **The fragile case.** An assemblage whose emergent distinction rests on a cross-region absence is non-degenerate
before totalization and degenerate after: totalizing flattens exactly the emergent part. -/
theorem fragile_case :
    NonDegenerate (assembleClassify z2 z2 impFrag)
    ∧ ¬ NonDegenerate (totalization (fun _ => 0) (assembleClassify z2 z2 impFrag)) := by
  refine ⟨by unfold NonDegenerate; decide, by unfold NonDegenerate; decide⟩

/-- **The robust case.** An assemblage whose emergent distinction is present-carried in the cross-region, two
verdicts differing at a shared cross-column, survives totalization. The emergent part is not always fragile. -/
theorem robust_case :
    NonDegenerate (assembleClassify zA zB impPres)
    ∧ NonDegenerate (totalization (fun _ => 0) (assembleClassify zA zB impPres)) := by
  refine ⟨by unfold NonDegenerate; decide, by unfold NonDegenerate; decide⟩

/-- **The gaining case.** A degenerate assemblage, its cross-region shared absences, becomes non-degenerate under a
distinguishing scale and stays degenerate under the flat one: totalizing creates emergent distinctions that were
not there, scale-dependently, as in the creation result, not the boundary antifragility. -/
theorem gaining_case :
    ¬ NonDegenerate (assembleClassify z2 z2 zP)
    ∧ NonDegenerate (totalization sc (assembleClassify z2 z2 zP))
    ∧ ¬ NonDegenerate (totalization (fun _ => 0) (assembleClassify z2 z2 zP)) := by
  refine ⟨by unfold NonDegenerate; decide, by unfold NonDegenerate; decide, by unfold NonDegenerate; decide⟩

/-! ## Part 3: is emergence systematically fragile? -/

/-- **Emergent fragility is set by the import.** For fixed factors, a present-carried import survives totalization
and an absence-carried one flattens, both non-degenerate before. So the emergent fragility depends on the import, a
choice made at assembly, not on the factors. -/
theorem emergent_fragility_across_imports :
    (NonDegenerate (totalization (fun _ => 0) (assembleClassify zA zB impPres)))
    ∧ (¬ NonDegenerate (totalization (fun _ => 0) (assembleClassify zA zB impAbs)))
    ∧ (NonDegenerate (assembleClassify zA zB impPres))
    ∧ (NonDegenerate (assembleClassify zA zB impAbs)) := by
  refine ⟨by unfold NonDegenerate; decide, by unfold NonDegenerate; decide,
          by unfold NonDegenerate; decide, by unfold NonDegenerate; decide⟩

/-- **The cross-region is not systematically more fragile.** A factor's present-carried distinction survives, and
a cross-region can be present-carried and survive too; both depend on whether the distinctions are present-carried.
So the cross-region is not systematically more fragile than the factors', the difference being the import. -/
theorem compare_factor_and_cross_fragility :
    (NonDegenerate (totalization (fun _ => 0) (assembleClassify pres1 z2 zP)))
    ∧ (NonDegenerate (totalization (fun _ => 0) (assembleClassify zA zB impPres))) := by
  refine ⟨by unfold NonDegenerate; decide, by unfold NonDegenerate; decide⟩

/-- **What survives.** The factors' present-carried distinctions survive; the emergent absence-content is
overwritten, the flat totalization of a none import equalling that of an affirmed one, so the import is erased and
the totalized assemblage carries the scale-fill in the cross-region, not the import. -/
theorem what_survives_totalizing_an_assemblage :
    (NonDegenerate (totalization (fun _ => 0) (assembleClassify pres1 z2 zP)))
    ∧ (totalization (fun _ => 0) (assembleClassify z2 z2 zP)
        = totalization (fun _ => 0) (assembleClassify z2 z2 impFrag)) := by
  refine ⟨by unfold NonDegenerate; decide, by decide⟩

/-! ## The verdicts

Part 1: totalization fills the located pairs and overwrites the record. A cross-region absence is filled like any
other (`totalization_fills_the_cross_region`); the filled pair is indistinguishable from an affirmed one, though
the location survives as a carrier fact (`is_the_disagreement_resolved_or_overwritten`). The where survives, the
that-it-was-undetermined does not.

Part 2: all three cases are reachable. The emergent distinctions live in the cross-region
(`cross_region_carries_the_emergent_distinctions`); an absence-carried cross distinction flattens (`fragile_case`),
a present-carried one survives (`robust_case`), and shared cross-absences gain under a distinguishing scale
(`gaining_case`). The emergent part is not systematically fragile.

Part 3: emergent fragility is a choice at assembly, not a property of the parts. For fixed factors, the import sets
whether the emergent part is fragile or robust (`emergent_fragility_across_imports`); the cross-region is not
systematically more fragile than the factors' (`compare_factor_and_cross_fragility`); what survives is the factors'
present-carried distinctions, the emergent absence-content overwritten (`what_survives_totalizing_an_assemblage`).

The verdict: totalizing an assemblage fills its located disagreement and overwrites the record, and what happens to
the emergent part is fragile, robust, or gaining depending on the import, a choice made at assembly rather than a
property of the parts. The located pairs, the imported cross-region where the factors conflict, are filled like any
absence, so after totalization the where survives as a carrier fact but the that-it-was-undetermined is gone, the
filled pair indistinguishable from an affirmed one. The emergent distinctions live in the cross-region, and all
three cases are reachable there: an emergent distinction resting on a cross-absence flattens under totalization,
one carried by differing present verdicts at a shared cross-column survives, and shared cross-absences gain under a
distinguishing scale, so the emergent part is not systematically fragile. Which case obtains is set by the import:
the same factors give a fragile or a robust assemblage according to whether the import places its distinctions on
absences or on present verdicts, so emergent fragility is a choice made at assembly, not a property of the factors,
and the cross-region is not systematically more fragile than the factors' regions, both depending on the same
present-carried condition. What survives totalization is the factors' present-carried distinctions and whatever the
scale creates; the emergent absence-content is overwritten, the flat totalization erasing the import, so the
totalized assemblage carries the scale-fill in its cross-region rather than the located disagreement. The gaining
case is reachable and scale-dependent, non-degenerate under a distinguishing scale and degenerate under the flat
one, so its mechanism is the creation result's, a property of the totalization with a scale, not the framework's
antifragility, which is a fixed boundary fact independent of scale; the name is not reused, the case reported as
gaining. Per the counter-bias, emergence was not concluded fragile from one instance, all three cases computed and
robust and gaining exhibited; the import-dependence was found, so fragility is a choice not a property of the
parts; and the antifragility name was withheld, the mechanism matching creation not the boundary derivation.
Reported per part. Nothing here is resolved. -/

end Chiralogy.AssemblageFragility
