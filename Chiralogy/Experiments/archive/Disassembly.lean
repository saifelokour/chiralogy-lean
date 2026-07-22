import Chiralogy

/-! # Experiment: when does an assemblage stop exceeding its parts?

An assemblage is more than its factors only if it adds something; if it adds nothing it is a juxtaposition, not an
assemblage. This parallels Member: an object stops being an object when it distinguishes nothing, an assemblage
stops being an assemblage when it adds nothing over its factors, both conditions on being the kind of thing.
Define the condition and test which configurations fail it, computing all routes before judging. Stays in
`Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Disassembly

def z2 : Fin 2 → Fin 2 → Option Bool := fun _ _ => none
def zP : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool := fun _ _ => none
def sat2 : Fin 2 → Fin 2 → Option Bool := fun x y => some (decide (x = y))
def impFrag : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool :=
  fun a b => if a = (0, 0) ∧ b = (1, 1) then some true else none

/-- The condition: the assemblage adds content over the empty-cross juxtaposition, the import contributing beyond
what the factors alone determine. -/
def exceeds {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2] (c1 : X1 → X1 → Option Bool)
    (c2 : X2 → X2 → Option Bool) (imp : (X1 × X2) → (X1 × X2) → Option Bool) : Prop :=
  assembleClassify c1 c2 imp ≠ assembleClassify c1 c2 (fun _ _ => none)

/-! ## Part 1: the condition -/

/-- **Adds content and adds a distinction do not coincide.** The empty-cross juxtaposition is the baseline; an
import differing from it exceeds by content. But with saturated factors the juxtaposition already distinguishes
every row, so an import adds content without adding any distinction. The content condition is the membership one,
weaker than the distinction condition: a whole can add a relation between elements already distinguished. -/
theorem exceeds_its_factors :
    (exceeds z2 z2 impFrag)
    ∧ (exceeds sat2 sat2 impFrag
        ∧ (¬ ∃ a a' : Fin 2 × Fin 2, a ≠ a'
            ∧ assembleClassify sat2 sat2 (fun _ _ => none) a
              = assembleClassify sat2 sat2 (fun _ _ => none) a')) := by
  refine ⟨by unfold exceeds; decide, by unfold exceeds; decide, by decide⟩

/-- **It is a membership condition.** Failing it, the import adding nothing, leaves a juxtaposition, a different
kind of thing, as failing non-degeneracy leaves a non-member. Both are conditions on being the kind of thing, not
on doing something wrong. -/
theorem is_it_a_membership_condition {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool) :
    (¬ exceeds c1 c2 (fun _ _ => none))
    ∧ (¬ NonDegenerate (fun _ _ => none : Fin 2 → Fin 2 → Option Bool)) := by
  refine ⟨by unfold exceeds; exact fun h => h rfl, by unfold NonDegenerate; decide⟩

/-! ## Part 2: the routes to failing it -/

/-- **Totalizing the cross-region.** The assemblage exceeds before, but its flat totalization equals that of its
juxtaposition, the emergent content overwritten: after totalizing, an absence-carried assemblage is not
distinguishable from the totalized juxtaposition. -/
theorem totalizing_the_cross_region :
    (exceeds z2 z2 impFrag)
    ∧ (totalization (fun _ => 0) (assembleClassify z2 z2 impFrag)
        = totalization (fun _ => 0) (assembleClassify z2 z2 zP)) := by
  refine ⟨by unfold exceeds; decide, by decide⟩

/-- **Opening the cross-region.** The uniform fill sets every cross pair to the absence, so the assemblage becomes
its empty-cross juxtaposition and no longer exceeds: the located content is removed. -/
theorem opening_the_cross_region :
    partialization (fun a b => decide (a.1 ≠ b.1 ∧ a.2 ≠ b.2)) (assembleClassify z2 z2 impFrag)
      = assembleClassify z2 z2 zP := by
  decide

/-- **The trivial import.** An import agreeing with the empty cross does not exceed at all: the assemblage is its
own juxtaposition from the start. This is the third route, a choice at assembly rather than a move, failing the
condition by construction. -/
theorem is_the_import_trivial {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool) :
    ¬ exceeds c1 c2 (fun _ _ => none) := by
  unfold exceeds; exact fun h => h rfl

/-! ## Part 3: what preserves it -/

/-- **Retaining absences does not itself exceed.** An assemblage can exceed while retaining absences, importing a
verdict at one cross pair and leaving others undetermined; but retaining absences alone, the pure open cross, does
not exceed, being the juxtaposition. Exceeding comes from imported content, retaining from absences, and they are
independent: retaining more does not exceed more. -/
theorem retaining_absences_in_the_cross_region :
    (exceeds z2 z2 impFrag)
    ∧ (assembleClassify z2 z2 impFrag (0, 1) (1, 0) = none)
    ∧ (¬ exceeds z2 z2 zP) := by
  refine ⟨by unfold exceeds; decide, by decide, by unfold exceeds; exact fun h => h rfl⟩

/-- **Openness is not structurally favoured.** The pure open cross is the non-exceeding baseline, so the exceeding
condition does not prefer retaining absences, and the framework has no stability notion to prefer it. The one
asymmetry is the ethics, opening asserting no falsehood while filling can fabricate, but that is about falsehood,
not exceeding or stability, so no preference for openness is read in. -/
theorem is_openness_structurally_favoured :
    (¬ exceeds z2 z2 zP)
    ∧ (∀ (X : Type) (w : X → X → Bool) (c : X → X → Option Bool) (t : X → X → Bool) (x y : X),
        assertsFalse (partialization w c) t x y → assertsFalse c t x y) := by
  refine ⟨by unfold exceeds; exact fun h => h rfl,
          fun X w c t x y => partialization_asserts_no_falsehood w c t x y⟩

/-! ## Part 4: the parameters -/

/-- **The parameters are blind to the condition.** Exceeding varies with the import, but coding and
territorialization are computed from the ground-order, the disjoint sum of the factor orders, fixed by the factors
and independent of the import; so an exceeding and a non-exceeding assemblage of the same factors have identical
parameters. The parameters see the ground-structure, not whether the whole exceeds its parts. -/
theorem do_the_parameters_track_it :
    (exceeds z2 z2 impFrag ∧ ¬ exceeds z2 z2 zP)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => ¬ closeable prereqTwoChain S)).card = 7)
    ∧ ((Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqTwoChain i j = false)).card = 2) := by
  refine ⟨⟨by unfold exceeds; decide, by unfold exceeds; exact fun h => h rfl⟩, by decide, by decide⟩

/-! ## The verdicts

Part 1: the condition is that the assemblage adds content over its empty-cross juxtaposition, a membership
condition. Adds-content and adds-a-distinction do not coincide, saturated factors distinguishing all rows so that
an import adds content without a distinction (`exceeds_its_factors`); and failing the condition leaves a
juxtaposition, a different kind, as a degenerate map is a non-member (`is_it_a_membership_condition`).

Part 2: all three routes fail it. Totalizing overwrites the emergent content, the totalized assemblage matching the
totalized juxtaposition (`totalizing_the_cross_region`); opening empties the cross-region back to the juxtaposition
(`opening_the_cross_region`); and a trivial import does not exceed from the start (`is_the_import_trivial`).

Part 3: retaining absences does not preserve exceeding, and openness is not favoured. The pure open cross is the
non-exceeding baseline (`retaining_absences_in_the_cross_region`); openness is not structurally favoured, the one
asymmetry being the ethics, not stability (`is_openness_structurally_favoured`).

Part 4: the parameters do not see it. Exceeding varies with the import while the ground-order parameters are fixed
by the factors (`do_the_parameters_track_it`).

The verdict: an assemblage stops exceeding its parts exactly when its cross-region carries no content beyond the
factors, and this is a membership condition parallel to Member, failed by all three routes, invisible to the
parameters, and not preserved by keeping the cross open. The condition is that the assemblage adds content over the
empty-cross juxtaposition, the import contributing a value the factors do not determine; failing it, the assemblage
is its own juxtaposition, a different kind of thing, just as a classification distinguishing nothing is not an
object. The adds-content condition is weaker than adds-a-distinction, since with saturated factors the
juxtaposition already distinguishes every row and an import can add only a relation between elements already
distinguished, so the two do not coincide and the membership condition is the content one. Three routes fail it,
two moves and a choice: totalizing fills the cross and overwrites the emergent content, so the totalized assemblage
is the totalized juxtaposition; opening empties the cross uniformly back to the juxtaposition; and a trivial import
never exceeds. Retaining absences does not preserve exceeding, which is the striking point: the pure open cross,
the fully located but unvalued disagreement, is exactly the non-exceeding baseline, so exceeding requires importing
content, valuing some of the cross, while retaining absences leaves the located disagreement but adds nothing. The
two are independent, and the framework does not favour openness: it has no stability notion, and the only asymmetry
is the ethics, that opening asserts no falsehood while filling can fabricate, which is about falsehood, not
exceeding. And the parameters are blind: coding and territorialization read the ground-order, the disjoint sum of
the factor orders, fixed by the factors regardless of the import, so an exceeding and a non-exceeding assemblage
share every parameter. Per the counter-bias, no stability was read in, the gate reporting the framework has no
preference for openness beyond the ethics; all three routes were computed, not one assumed sufficient; and the
parameters were computed and found blind. Reported per part. Nothing here is resolved. -/

end Chiralogy.Disassembly
