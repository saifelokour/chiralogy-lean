import Chiralogy

/-! # Experiment: is located difference the necessary condition for exceeding, and what supplies sufficiency?

Exceeding is inter-object, arity two or more, with no arity-1 shadow, and mirroring the coincidence claim does not
exceed. Characterize the relation between difference and exceeding: necessary, sufficient, both. `exceeds c1 c2 imp`
is the assemblage differing from its empty-cross juxtaposition. `located X1 X2` is the cross-region being non-empty,
two pairs differing in both components, a condition on the carriers not the import; it appears under no canonical
name, so it is defined here minimally. Difference is non-coincidence at three sites: ends (forced), rows
(non-degeneracy), whole-vs-parts (exceeding). Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.DifferenceCondition

def satN : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none

/-- Located difference: the cross-region is non-empty, two pairs differing in both components. A condition on the
carriers, not the import. -/
def located (X1 X2 : Type) : Prop := ∃ a b : X1 × X2, a.1 ≠ b.1 ∧ a.2 ≠ b.2

/-- A differentiating import: value one cross pair. -/
def dif : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool :=
  fun a b => if a = (0, 0) ∧ b = (1, 1) then some true else none

/-! ## Part 1: located difference as necessary condition -/

/-- **Exceeding requires location.** If the assemblage exceeds its juxtaposition, the cross-region is non-empty: for
if no two pairs differ in both components, the assemblage equals its juxtaposition for every import and cannot
exceed. -/
theorem exceeding_requires_location {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) :
    (assembleClassify c1 c2 imp ≠ assembleClassify c1 c2 (fun _ _ => none)) → located X1 X2 := by
  intro hexc
  by_contra hnl
  apply hexc
  funext a b
  refine construction_takes_two_objects_and_a_cross_map c1 c2 imp (fun _ _ => none) ?_ a b
  intro a b h1 h2
  exact absurd ⟨h1, h2⟩ (fun hab => hnl ⟨a, b, hab⟩)

/-! ## Part 2: location is not sufficient -/

/-- **Location does not suffice.** The pure open cross, located factors with the empty import, has a non-empty
cross yet does not exceed: the assemblage is its own juxtaposition. Difference is present, the whole does not
exceed, so located is strictly weaker than exceeding. -/
theorem location_is_not_sufficient :
    (located (Fin 2) (Fin 2))
    ∧ (¬ (assembleClassify satN satN (fun _ _ => none)
          ≠ assembleClassify satN satN (fun _ _ => none))) := by
  refine ⟨⟨(0, 0), (1, 1), by decide, by decide⟩, fun h => h rfl⟩

/-! ## Part 3: what supplies sufficiency -/

/-- **Sufficiency is the import.** For located factors there is an import that exceeds and one that does not, so
above location the deciding factor is the free import, not any structural condition on the factors: exceeding is
reachable both ways, a genuine choice at assembly. -/
theorem sufficiency_is_the_import :
    (assembleClassify satN satN dif ≠ assembleClassify satN satN (fun _ _ => none))
    ∧ (¬ (assembleClassify satN satN (fun _ _ => none)
          ≠ assembleClassify satN satN (fun _ _ => none))) := by
  refine ⟨by decide, fun h => h rfl⟩

/-! ## Part 4: the verdict -/

/-- **Difference gates, the import supplies.** Exceeding requires located difference; located difference does not
suffice, a located pair with the empty import not exceeding; and above location an exceeding import exists, so
sufficiency is the free import's, not a factor condition. -/
theorem difference_gates_import_supplies :
    (∀ imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool,
        (assembleClassify satN satN imp ≠ assembleClassify satN satN (fun _ _ => none)) → located (Fin 2) (Fin 2))
    ∧ (located (Fin 2) (Fin 2)
        ∧ ¬ (assembleClassify satN satN (fun _ _ => none) ≠ assembleClassify satN satN (fun _ _ => none)))
    ∧ (assembleClassify satN satN dif ≠ assembleClassify satN satN (fun _ _ => none)) := by
  refine ⟨fun imp => exceeding_requires_location satN satN imp,
          ⟨⟨(0, 0), (1, 1), by decide, by decide⟩, fun h => h rfl⟩, by decide⟩

/-! ## The verdicts

Part 1: exceeding requires located difference. If the cross-region is empty the assemblage equals its juxtaposition
for every import, so exceeding forces the cross non-empty (`exceeding_requires_location`).

Part 2: location does not suffice. The pure open cross is located yet does not exceed
(`location_is_not_sufficient`), so located is strictly weaker.

Part 3: sufficiency is the import. For located factors an import exceeds and another does not
(`sufficiency_is_the_import`), so the deciding factor above location is the free import.

Part 4: difference gates, the import supplies (`difference_gates_import_supplies`): exceeding requires location,
location does not suffice, sufficiency is the import's.

The verdict: located difference is the necessary condition for exceeding, it is not sufficient, and sufficiency above
it is supplied by the free import rather than by any condition on the factors. Exceeding requires that the two
factors be genuinely two, the cross-region non-empty, two pairs differing in both components; where the cross is
empty, at arity one or a singleton second factor, the import is never consulted and the assemblage equals its
juxtaposition for every import, so it cannot exceed, and located difference follows from exceeding. This gathers the
three standing failures under one condition: mirroring collapses because it fills the cross with what the factors
already say and adds nothing, the trivial import leaves the cross empty of content, and arity one leaves the cross
empty of place, all of them the failure of the whole to be more than its parts, and the last of them the failure of
location itself. But location is only necessary. The pure open cross, located factors with the empty import, has a
non-empty cross and still does not exceed, the located disagreement unvalued, so difference at the carriers is
strictly weaker than exceeding, present where exceeding is absent. What lifts a located pair to exceeding is the
import, and it is a free choice, not a further condition on the factors: for located factors there is an import that
exceeds and one that does not, so no structural property of the factors settles exceeding once location holds, only
the import does. The deciding content sits in the free cross-map, which is why the factors bound the fragility
ceiling but not whether the whole exceeds, and why exceeding is a choice made at assembly. So difference gates and
the import supplies: located difference is the gate that exceeding must pass, necessary and carrier-borne, and
sufficiency is handed to the free import above it. Per the discipline, this is the framework-native necessity of
difference for exceeding, not emergence, which is the imported DeLanda reading and is kept out of the theorem names;
any emergence correspondence stays a reading, that a whole exceeding its parts requires the parts be genuinely two
and something imported to relate them. Per the counter-bias, sufficiency was not stated circularly, located as the
carrier condition kept distinct from the import firing, and sufficiency located in the import's freedom by
reachability both ways rather than a repackaged definition; content and distinction were kept apart, located being
the carriers' non-empty cross and not the import adding a distinction; and emergence was not laundered into a
theorem name. Reported per part. Nothing here is resolved. -/

end Chiralogy.DifferenceCondition
