import Chiralogy

/-! ARCHIVED (SPENT): the graduatable universal results of this investigation already reached
canonical in prior sessions, so nothing graduated in the graduate-now wave. Mapping:
  factors_survive_intact -> Model/Assemblage (factors_determine_the_shared_region); disagreement_lands_in_the_cross_region -> Model/Assemblage (import_is_the_complement); floor_of_an_assemblage / ceiling_of_an_assemblage already canonical (Model/Assemblage).
Remaining content is fixed-size witnesses and (where present) fragility/scale coordinates, kept as
the investigation record. Namespaced under Chiralogy.Reconciliation, it typechecks standalone against canonical. -/

/-! # Experiment: does the assemblage locate disagreement, and how do bounds compose?

Reconciliation is not derivable: the coproduct is absent and the cross-region is free. Test whether an assemblage
nonetheless locates a disagreement, and how bounds compose under assembly. Compute across several factor-pairs
before judging. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Reconciliation

/-! ## Part 1: is disagreement expressible? -/

/-- **The identification is the product's own pairing.** To say two objects classify the same thing needs a
pairing of their elements; the assemblage's product carrier provides it, a point pairing an element of each factor
and projecting back to each, so the identification is intrinsic, not imported. It is the weak one, pairing every
element of one factor with every element of the other. -/
theorem identification_needs_a_map {X1 X2 : Type} (x1 : X1) (x2 : X2) :
    ((x1, x2).1 = x1) ∧ ((x1, x2).2 = x2) :=
  ⟨rfl, rfl⟩

/-- **Disagreement is statable without an imported map.** Using the assemblage's own carrier, a pair of points
reads factor one at `c1 a.1 b.1` and factor two at `c2 a.2 b.2`, and these can differ at a fully-cross pair: the
two objects assign different verdicts to their identified elements. The gate does not trigger. -/
theorem is_disagreement_statable :
    ∃ (c1 c2 : Fin 2 → Fin 2 → Option Bool) (a b : Fin 2 × Fin 2),
      (a.1 ≠ b.1 ∧ a.2 ≠ b.2) ∧ c1 a.1 b.1 ≠ c2 a.2 b.2 :=
  ⟨fun _ _ => some true, fun _ _ => some false, (0, 0), (1, 1), ⟨by decide, by decide⟩, by decide⟩

/-! ## Part 2: does the assemblage locate it? -/

/-- **The factors survive intact.** Both classifications appear in the assemblage unaltered, each in its own
region: the shared-second pairs by `c1`, the shared-first pairs by `c2`. -/
theorem factors_survive_intact {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (a b : X1 × X2) :
    (a.2 = b.2 → assembleClassify c1 c2 imp a b = c1 a.1 b.1)
    ∧ (a.1 = b.1 → a.2 ≠ b.2 → assembleClassify c1 c2 imp a b = c2 a.2 b.2) :=
  factors_determine_the_shared_region c1 c2 imp a b

/-- **Disagreement lands in the cross-region.** A fully-cross pair, where the two factors read different elements
and can disagree, is classified by the import: the assemblage's value there is the imported one, not derived from
the factors. -/
theorem disagreement_lands_in_the_cross_region {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (a b : X1 × X2) :
    a.1 ≠ b.1 → a.2 ≠ b.2 → assembleClassify c1 c2 imp a b = imp a b :=
  import_is_the_complement c1 c2 imp a b

/-- **Located but not resolved.** The location is determinate: on the shared-component region the assemblage is
independent of the import, so the import-dependent pairs are exactly the fully-cross ones, the disagreement region,
computable from the factors. But the value there is not determinate: two imports give different verdicts. The
framework names where the factors conflict without saying what the verdict is. -/
theorem located_but_not_resolved :
    (∀ (c1 c2 : Fin 2 → Fin 2 → Option Bool) (a b : Fin 2 × Fin 2), (a.2 = b.2 ∨ a.1 = b.1) →
        assembleClassify c1 c2 (fun _ _ => none) a b = assembleClassify c1 c2 (fun _ _ => some true) a b)
    ∧ (∃ a b : Fin 2 × Fin 2,
        assembleClassify (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) (fun _ _ => none) (fun _ _ => none) a b
          ≠ assembleClassify (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) (fun _ _ => none)
              (fun _ _ => some true) a b) := by
  refine ⟨fun c1 c2 a b h => grounds_are_derivable_not_imported c1 c2 _ _ a b h, ⟨(0, 0), (1, 1), by decide⟩⟩

/-! ## Part 3: how bounds compose -/

/-- **The ceiling is the conjunction of the factors'.** The assemblage's ground-order is the disjoint sum, so its
full closure closes both factors' grounds: the assemblage reaches its ceiling exactly when both factors reach
theirs. It sits atop the product of the factors' closeable lattices, nine as three times three. -/
theorem ceiling_of_an_assemblage :
    (∀ S : Fin 4 → Bool, (∀ i, S i = true) ↔ ((S 0 = true ∧ S 1 = true) ∧ (S 2 = true ∧ S 3 = true)))
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable prereqTwoChain S)).card =
       (Finset.univ.filter (fun S : Fin 2 → Bool => closeable prereqChain2 S)).card *
       (Finset.univ.filter (fun S : Fin 2 → Bool => closeable prereqChain2 S)).card) := by
  refine ⟨by decide, by decide⟩

/-- **The floor is the conjunction of the parts'.** The assemblage is at its floor, a present verdict never
firing, only when all three, both factors and the import, are at theirs: the verdict fires in whichever region it
is present. So one factor at its floor does not floor the assemblage. -/
theorem floor_of_an_assemblage {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) :
    (∀ x y, c1 x y ≠ some true) → (∀ x y, c2 x y ≠ some true) → (∀ a b, imp a b ≠ some true) →
    (∀ a b : X1 × X2, assembleClassify c1 c2 imp a b ≠ some true) := by
  intro h1 h2 himp a b
  unfold assembleClassify
  split
  · exact h1 a.1 b.1
  · split
    · exact h2 a.2 b.2
    · exact himp a b

/-- **Assembly can clear a floor.** A floored factor, never firing the verdict, assembled with a healthy one gives
an assemblage that fires it, in the healthy factor's region: the whole clears a floor a factor cannot clear
alone. -/
theorem can_assembly_clear_a_floor :
    ∃ (c1 c2 : Fin 2 → Fin 2 → Option Bool) (imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool)
      (a b : Fin 2 × Fin 2),
      (∀ x y, c1 x y ≠ some true) ∧ assembleClassify c1 c2 imp a b = some true :=
  ⟨fun _ _ => none, fun _ _ => some true, fun _ _ => none, (0, 0), (0, 1), by decide, by decide⟩

/-- **Assembly cannot impose a floor.** Two healthy factors, an import firing nothing, still give an assemblage
that fires the verdict, in a factor's region: a dead import does not floor healthy factors, since their regions are
untouched by it. -/
theorem can_assembly_impose_one :
    ∃ (c1 c2 : Fin 2 → Fin 2 → Option Bool) (a b : Fin 2 × Fin 2),
      (∃ x y, c1 x y = some true) ∧ (∃ x y, c2 x y = some true)
      ∧ assembleClassify c1 c2 (fun _ _ => none) a b = some true :=
  ⟨fun _ _ => some true, fun _ _ => some true, (0, 0), (1, 0),
   ⟨0, 0, by decide⟩, ⟨0, 0, by decide⟩, by decide⟩

/-! ## The verdicts

Part 1: disagreement is statable without an imported map. The identification is the product's own pairing, a point
pairing an element of each factor and projecting back (`identification_needs_a_map`); with it, two objects assign
different verdicts to identified elements at a fully-cross pair (`is_disagreement_statable`). The gate does not
trigger: the framework's product supplies the identification, weak but its own.

Part 2: the assemblage locates the disagreement without resolving it. The factors survive intact in their regions
(`factors_survive_intact`); a fully-cross pair, where the factors can disagree, is classified by the import
(`disagreement_lands_in_the_cross_region`); and the location is determinate while the value is not, the
shared-component region import-independent and the cross-region import-free (`located_but_not_resolved`).

Part 3: the bounds compose conjunctively, and the floor asymmetrically. The ceiling is the conjunction of the
factors' full closures, atop the product of their lattices (`ceiling_of_an_assemblage`); the floor is the
conjunction of the parts', all three floored (`floor_of_an_assemblage`); so assembly can clear a floor
(`can_assembly_clear_a_floor`) but cannot impose one (`can_assembly_impose_one`).

The verdict: an assemblage locates a disagreement it cannot resolve, and the bounds compose conjunctively, the
floor asymmetrically so that assembly clears but does not impose. Disagreement is statable without importing an
identification: the assemblage's product carrier is itself the pairing, a point identifying an element of each
factor, so two objects can be said to assign different verdicts to identified elements, at a fully-cross pair. This
identification is the weak one, every element paired with every other, but it is the framework's own, so the gate
does not trigger and disagreement is a framework notion here. The assemblage then locates the disagreement: the
factors survive intact in their regions, and the pairs where they can disagree are exactly the fully-cross ones,
the imported region, determinate as a location because the rest is import-independent. But it does not resolve it:
the value on the cross-region is free, two imports disagreeing, so the framework names where the factors conflict
without saying what holds there. Naming the undetermined region is more than nothing structurally, a determinate
location with no determinate value, which is what locating without resolving means. The bounds compose
conjunctively, not like the parameters, which add and multiply: the ceiling is reached when both factors' full
closures are, atop the product of their closeable lattices, and the floor is reached only when all three parts,
both factors and the import, never fire the verdict. This makes the floor asymmetric under assembly: a floored
factor assembled with a healthy one gives a healthy assemblage, the verdict firing in the healthy region, so
assembly clears a floor a factor cannot clear alone; but two healthy factors give a healthy assemblage whatever the
import, so assembly cannot impose a floor, the factors' regions being untouched by a dead import. Per the
counter-bias, disagreement was not assumed statable, the identification found to be the product's own rather than
imported; location was not read as resolution, the value shown undetermined where the location is determinate; and
the bounds were computed, composing conjunctively rather than by the parameters' laws. Reported per part. Nothing
here is resolved. -/

end Chiralogy.Reconciliation
