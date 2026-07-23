import Chiralogy

/-! ARCHIVED (coordinates settled: NO clean law). The VALUED-FRACTION axis and the (valued x fragility) joint.

The valued fraction counts the cross pairs the import gives a present value (rather than none). ANSWER: it is
FREE, any value from 0 to crossMax is achievable, because the import is unconstrained on the cross region
(cross_is_free_over_all_factors, no_factor_forces_the_cross, canonical). It is a free import-side count with no
law beyond its range.

The joint (valued x fragility) occupancy: NO clean law. The two axes are independent (the file's are_they_
independent: same valued, different fragility), and the fragility axis itself has no clean present-structure law
(settled: assemblage cross-fragility is configuration-dependent, obstructed at the factor-2-aligned region by
assembleClassify's a.2 = b.2-first ordering). So the joint has no closed form. The threshold finding (exceeds iff
valued >= 1) restates the canonical exceeds machinery (exceeding_requires_location, sufficiency_is_the_import).
Every theorem here is a specific instance (i0, i1, i2r, i2d, i4r), a witness, not a general law.

Negative finding recorded in the archive note only, never in canonical or spec. Typechecks standalone. -/

/-! # Experiment: the assemblage phase space

The membership condition is settled and three routes out are known. Compute the interior: coordinates,
independence, occupancy. The parameters read the factor-fixed ground-order and are blind to exceeding, so interior
coordinates must be import-side. Compute every coordinate for every instance before judging. Degenerate factors
isolate the emergent cross-region; the carrier `Fin 3 × Fin 2` allows both concentrated and spread valued pairs.
Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.PhaseSpace

def zA : Fin 3 → Fin 3 → Option Bool := fun _ _ => none
def zB : Fin 2 → Fin 2 → Option Bool := fun _ _ => none

/-- Coordinate one: the valued fraction, how many cross pairs the import values rather than leaves absent. -/
def valued (imp : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool) : Nat :=
  (Finset.univ.filter (fun p : (Fin 3 × Fin 2) × (Fin 3 × Fin 2) =>
    p.1.1 ≠ p.2.1 ∧ p.1.2 ≠ p.2.2 ∧ imp p.1 p.2 ≠ none)).card

/-- Coordinate two: the cross fragility, how many emergent distinctions flat totalization destroys. -/
def crossFrag (imp : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool) : Nat :=
  (Finset.univ.filter (fun p : (Fin 3 × Fin 2) × (Fin 3 × Fin 2) =>
    assembleClassify zA zB imp p.1 ≠ assembleClassify zA zB imp p.2
    ∧ totalization (fun _ => 0) (assembleClassify zA zB imp) p.1
      = totalization (fun _ => 0) (assembleClassify zA zB imp) p.2)).card

/-- The empty cross, one valued pair, two at a shared column (concentrated), two at different columns (spread),
and four concentrated. -/
def i0 : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool := fun _ _ => none
def i1 : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool :=
  fun a b => if a = (0, 1) ∧ b = (2, 0) then some true else none
def i2r : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool :=
  fun a b => if a = (0, 1) ∧ b = (2, 0) then some true else if a = (1, 1) ∧ b = (2, 0) then some false else none
def i2d : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool :=
  fun a b => if a = (0, 1) ∧ b = (2, 0) then some true else if a = (0, 0) ∧ b = (1, 1) then some true else none
def i4r : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool :=
  fun a b => if a = (0, 1) ∧ b = (2, 0) then some true else if a = (1, 1) ∧ b = (2, 0) then some false
    else if a = (2, 1) ∧ b = (0, 0) then some true else if a = (2, 1) ∧ b = (1, 0) then some false else none

/-! ## Part 1: the candidate coordinates -/

/-- **The valued fraction.** Zero cross pairs valued is the juxtaposition boundary; more valued is more content:
zero, one, two, four across the instances. -/
theorem valued_fraction :
    (valued i0 = 0) ∧ (valued i1 = 1) ∧ (valued i2r = 2) ∧ (valued i2d = 2) ∧ (valued i4r = 4) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **The cross fragility.** How many emergent distinctions flat totalization destroys: zero at the juxtaposition,
and varying with the import, ten, eight, eighteen, six across the instances. -/
theorem cross_fragility :
    (crossFrag i0 = 0) ∧ (crossFrag i1 = 10) ∧ (crossFrag i2r = 8)
    ∧ (crossFrag i2d = 18) ∧ (crossFrag i4r = 6) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **They are independent.** The two imports valuing the same number of cross pairs, one concentrated at a shared
column and one spread across different columns, have different cross fragility, eight against eighteen: cross
fragility is not a function of the valued fraction, so the second coordinate is genuine. -/
theorem are_they_independent :
    (valued i2r = valued i2d) ∧ (crossFrag i2r ≠ crossFrag i2d) := by
  refine ⟨by decide, by decide⟩

/-- **No third coordinate.** Position and concentration feed the cross fragility rather than forming a third axis:
the same valued count with different position gives different fragility, and more concentrated valued pairs give
less fragility even at a higher valued count, six at four valued against eighteen at two. -/
theorem is_there_a_third :
    (valued i2r = valued i2d ∧ crossFrag i2r ≠ crossFrag i2d)
    ∧ (valued i2d < valued i4r ∧ crossFrag i4r < crossFrag i2d) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-! ## Part 2: the trade -/

/-- **Exceeding is a threshold, not a trade.** A single valued pair already exceeds the juxtaposition, while zero
valued is the juxtaposition; valuing more does not exceed more, exceeding being binary. The gate reports a
threshold: below it a juxtaposition, above it an assemblage, and the valued fraction is an interior coordinate, not
a degree of exceeding. -/
theorem locating_versus_exceeding :
    (assembleClassify zA zB i0 = assembleClassify zA zB (fun _ _ => none))
    ∧ (assembleClassify zA zB i1 ≠ assembleClassify zA zB (fun _ _ => none))
    ∧ (assembleClassify zA zB i4r ≠ assembleClassify zA zB (fun _ _ => none)) := by
  refine ⟨rfl, by decide, by decide⟩

/-! ## Part 3: occupancy -/

/-- **The imports spread across the space.** The same factors under different imports occupy distinct coordinates,
the free import placing them apart: the assemblages of fixed factors do not cluster, unlike the registers
themselves, the import setting the interior position. -/
theorem which_regions_are_occupied :
    ((valued i1, crossFrag i1) = (1, 10))
    ∧ ((valued i2r, crossFrag i2r) = (2, 8))
    ∧ ((valued i2d, crossFrag i2d) = (2, 18))
    ∧ ((valued i4r, crossFrag i4r) = (4, 6)) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The extremes and the interior are populated.** The zero-valued boundary, and interior points at various
valued fractions and cross fragilities, are all occupied, including two points at the same valued fraction with the
lowest and a high cross fragility: the interior is not empty. -/
theorem constructed_extremes :
    (valued i0 = 0 ∧ crossFrag i0 = 0)
    ∧ (crossFrag i2r = 8 ∧ crossFrag i2d = 18 ∧ valued i2r = valued i2d)
    ∧ (valued i4r = 4 ∧ crossFrag i4r = 6) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-! ## Part 4: the verdict -/

/-- **A phase space above a threshold.** The membership boundary is a threshold on the valued fraction, zero being
the juxtaposition; above it the interior is a genuine two-coordinate phase space, the cross fragility independent
of the valued fraction and the interior populated by distinct points. -/
theorem is_it_a_phase_space :
    (assembleClassify zA zB i0 = assembleClassify zA zB (fun _ _ => none))
    ∧ (valued i2r = valued i2d ∧ crossFrag i2r ≠ crossFrag i2d)
    ∧ ((valued i1, crossFrag i1) ≠ (valued i4r, crossFrag i4r)) := by
  refine ⟨rfl, ⟨by decide, by decide⟩, by decide⟩

/-! ## The verdicts

Part 1: two import-side coordinates, independent, with no third. The valued fraction counts the valued cross pairs
(`valued_fraction`), the cross fragility the emergent distinctions flat totalization destroys (`cross_fragility`);
they are independent, cross fragility not a function of the valued fraction (`are_they_independent`); and position
and concentration feed the cross fragility rather than forming a third axis (`is_there_a_third`).

Part 2: exceeding is a threshold, not a trade. A single valued pair already exceeds and zero valued is the
juxtaposition (`locating_versus_exceeding`), so membership is crossed at the first valued pair and the valued
fraction is an interior coordinate, not a degree of exceeding.

Part 3: the imports spread and the interior is populated. Different imports of the same factors occupy distinct
coordinates (`which_regions_are_occupied`), the extremes and interior all populated (`constructed_extremes`).

Part 4: a phase space above a threshold (`is_it_a_phase_space`). The membership boundary is a threshold on the
valued fraction; above it two independent coordinates with a populated interior.

The verdict: the assemblage interior is a genuine two-coordinate phase space sitting above a membership threshold,
the coordinates import-side and independent, the interior populated. Membership, exceeding the factors, is a
threshold on the valued fraction: a single valued cross pair already exceeds, zero valued is the juxtaposition, and
valuing more does not exceed more, so there is no trade between locating and exceeding, only a boundary. Above the
boundary the interior has two coordinates. The valued fraction measures how much of the cross-region the import
values, from the juxtaposition at zero toward a full fill. The cross fragility measures how much of the emergent
content flat totalization destroys, and it is independent of the valued fraction: two imports valuing the same
number of cross pairs, one concentrated at a shared column and one spread, have different cross fragility, so the
second coordinate is genuine and not redundant. Position and concentration do not add a third axis but feed the
cross fragility, concentrated valued pairs surviving totalization and so lowering it even as the valued fraction
rises. The interior is populated, distinct imports of the same factors scattering across it rather than clustering,
because the import is free, unlike the registers themselves which sit in a corner: an assembler chooses the whole's
interior position by choosing the cross-map, within a space the factors fix the boundary of but not the interior.
Per the counter-bias, the trade was not assumed, the gate reporting a threshold with the valued fraction a
coordinate not a degree; two coordinates were not assumed sufficient, position and concentration checked and found
to feed the second rather than form a third; and no region was named, only occupancy and independence reported.
Reported per part. Nothing here is resolved. -/

end Chiralogy.PhaseSpace
