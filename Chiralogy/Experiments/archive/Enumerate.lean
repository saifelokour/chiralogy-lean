import Chiralogy

/-! ARCHIVED (GRADUATED, SUPERSEDED): the 1D fragility-spectrum question this file explored is closed.
Mapping to canonical (Model/Apophatic): the interior-by-enumeration (Fin 2 fragility spectrum {0,2}, and its shape) -> interior_full_fill + fragility_even: the fragility spectrum is exactly the even values in [0, n^2-n], full fill no gaps, now a theorem for general n.
The remaining open frontier (the 2D assemblage phase space: valued fraction against cross-fragility, and
whether factors bound the cross-fragility ceiling) lives on in the assemblage/phase-space experiments.
Namespaced under its own name, this record typechecks standalone against canonical. -/

/-! # Experiment: the interior by enumeration

The register set exercises the space too thinly to say what is populated, and the thinness is a modelling artifact.
Enumerate instead. At Fin 2 the classifications number `3 ^ 4 = 81` and are enumerated exhaustively; the ordered
factor-pairs number `81 ^ 2 = 6561` and their assemblage baselines take only a handful of discrete values, but the
pair enumeration exceeds the kernel's reach, so it is reported from evaluation with its coverage stated, and the
theorems assert the classification-level enumeration and specific witnesses. Fin 3 is sampled, not exhausted, its
classifications numbering `3 ^ 9`. Do not trust Fin 2 alone. Stays in `Experiments/`; canonical untouched; nothing
resolved. -/

open Chiralogy

namespace Chiralogy.Enumerate

/-- A classification's own fragility: distinct rows flat totalization merges. -/
def frag {n : Type} [Fintype n] [DecidableEq n] (c : n → n → Option Bool) : Nat :=
  (Finset.univ.filter (fun p : n × n =>
    c p.1 ≠ c p.2 ∧ totalization (fun _ => 0) c p.1 = totalization (fun _ => 0) c p.2)).card

/-- A classification's absence count. -/
def absc {n : Type} [Fintype n] [DecidableEq n] (c : n → n → Option Bool) : Nat :=
  (Finset.univ.filter (fun p : n × n => c p.1 p.2 = none)).card

/-- Two classifications, both with two absences, one robust and one fragile. -/
def w1 : Fin 2 → Fin 2 → Option Bool := fun x y => if x = 0 then (if y = 0 then some true else some false) else none
def w2 : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none

def sat3 : Fin 3 → Fin 3 → Option Bool := fun x y => if x = y then some true else none
def pre3 : Fin 3 → Fin 3 → Option Bool := fun x y => some (decide (x = y))

/-! ## Part 1: exhaustive at Fin 2 -/

/-- **The classifications enumerated.** Over the eighty-one classifications, own fragility takes two values, sixty
five at zero and sixteen at two, none between or beyond; absence count spreads sixteen, thirty two, twenty four,
eight, one from zero absences to four. -/
theorem all_classifications :
    ((Finset.univ.filter (fun c : Fin 2 → Fin 2 → Option Bool => frag c = 0)).card = 65)
    ∧ ((Finset.univ.filter (fun c : Fin 2 → Fin 2 → Option Bool => frag c = 2)).card = 16)
    ∧ ((Finset.univ.filter (fun c : Fin 2 → Fin 2 → Option Bool => absc c = 0)).card = 16)
    ∧ ((Finset.univ.filter (fun c : Fin 2 → Fin 2 → Option Bool => absc c = 4)).card = 1) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The distribution.** Own fragility is binary, sixty five of the eighty one robust or degenerate at zero,
sixteen fragile at two; the two witnesses share an absence count of two yet differ in fragility, so the amount is
not fixed by the absence count. -/
theorem the_distribution :
    (absc w1 = 2 ∧ absc w2 = 2)
    ∧ (frag w1 = 0 ∧ frag w2 = 2) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-! ## Part 2: does the three-region division hold? -/

/-- **The ceilings do not spread continuously.** Exhaustively, own fragility takes only the two values zero and two
over the eighty one classifications, none other: a discrete cut, not a continuum. The assemblage baselines, from
evaluation over the six thousand five hundred sixty one pairs, likewise take only the six values zero, two, four,
eight, ten, twelve, but that count exceeds the kernel and is not asserted here. -/
theorem do_ceilings_cluster :
    (Finset.univ.filter (fun c : Fin 2 → Fin 2 → Option Bool => frag c ≠ 0 ∧ frag c ≠ 2)).card = 0 := by
  decide

/-- **No formula indexes it.** The absence count does not determine fragility, the two witnesses sharing an absence
count of two while their fragility differs, zero and two: so the candidate formula fails, and the index is
descriptive, not a computed quantity. -/
theorem what_indexes_the_ceiling :
    (absc w1 = absc w2)
    ∧ (frag w1 ≠ frag w2) := by
  refine ⟨by decide, by decide⟩

/-! ## Part 3: Fin 3, sampled -/

/-- **The verdict swap does not quotient fragility.** Swapping the two present verdicts changes fragility, the
saturated classification at two but its swap at zero: because the flat scale fills absences with `some true`, a
`some true` against an absence merges while a `some false` against an absence survives, so fragility privileges
`some true` and the swap is not a symmetry of it. Only carrier relabelling quotients. -/
theorem quotient_by_relabelling :
    (frag (fun x y => Option.map not (w2 x y) : Fin 2 → Fin 2 → Option Bool) = 0)
    ∧ (frag w2 = 2) := by
  refine ⟨by decide, by decide⟩

/-- **The Fin 2 picture does not persist.** Sampled at Fin 3, the saturated classification has fragility six,
beyond the Fin 2 range of zero and two, while the present and degenerate stay at zero: so the binary distribution
was smallness, and the range grows with size. The sample is three constructed classifications, not the `3 ^ 9`
exhausted. -/
theorem does_the_fin2_picture_persist :
    (frag sat3 = 6) ∧ (frag pre3 = 0) ∧ (frag (fun _ _ => none : Fin 3 → Fin 3 → Option Bool) = 0) := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## Part 4: the verdict -/

/-- **What is populated.** Sixty five of the eighty one classifications have fragility zero, robust or degenerate;
sixteen have fragility two, fragile. The registers' own classification, the saturated one, is in the sixteen, the
fragile minority: so the registers sit in the smaller group, not the typical one, at this size. -/
theorem what_is_populated :
    ((Finset.univ.filter (fun c : Fin 2 → Fin 2 → Option Bool => frag c = 2)).card = 16)
    ∧ (frag (fun x y => if x = y then some true else none : Fin 2 → Fin 2 → Option Bool) = 2) := by
  refine ⟨by decide, by decide⟩

/-- **The index is not a formula.** The absence count does not fix fragility, and the binary Fin 2 range does not
persist, Fin 3 reaching six: so no computed quantity found determines the ceiling, and the index remains
descriptive. -/
theorem is_the_index_a_formula :
    (absc w1 = absc w2 ∧ frag w1 ≠ frag w2)
    ∧ (frag sat3 = 6) := by
  refine ⟨⟨by decide, by decide⟩, by decide⟩

/-! ## The verdicts

Part 1: at Fin 2, exhaustively, own fragility is binary, sixty five at zero and sixteen at two
(`all_classifications`), the fragile sixteen not fixed by the absence count (`the_distribution`).

Part 2: the cut is discrete but the index is descriptive. Own fragility takes only two values over the eighty one,
none between (`do_ceilings_cluster`); and the absence count does not determine it, so no formula was found
(`what_indexes_the_ceiling`).

Part 3: Fin 2 was smallness. The verdict swap does not preserve fragility, the flat fill privileging `some true`,
so only carrier relabelling quotients (`quotient_by_relabelling`); and sampled at Fin 3 the saturated classification
has fragility six, beyond the Fin 2 range (`does_the_fin2_picture_persist`).

Part 4: the fragile classifications are the minority and the registers sit among them, and the index is not a
formula. Sixteen of eighty one are fragile, the registers' saturated classification among them
(`what_is_populated`); no computed quantity determines the ceiling (`is_the_index_a_formula`).

The verdict: exhaustive enumeration at Fin 2 shows a discrete distribution, the registers in the fragile minority,
and an index that is descriptive rather than a formula, with Fin 3 confirming the binary range was smallness. Over
the eighty one classifications own fragility is binary, sixty five at zero and sixteen at two, with nothing between
or beyond, so the cut is genuinely discrete and not an artifact of choosing extremes; the assemblage baselines over
the pairs take only six discrete values by evaluation, though that enumeration exceeds the kernel and is not
asserted, reported with its coverage. The fragile classifications are the smaller group, sixteen of eighty one, and
the registers' own saturated classification is among them, so the registers landing in the fragile region is not
the typical case but the atypical one at this size, which sharpens the earlier finding that their clustering was a
modelling choice rather than a domain fact. The index of the ceiling is not a formula: the absence count, the
candidate, does not determine even the own fragility, two classifications sharing an absence count of two while one
is robust and one fragile, so no single computed quantity was found to fix the ceiling, and the index stays
descriptive, how much absence the factors leave in a way not captured by a count. And Fin 2 is not to be trusted
alone: the binary range zero and two does not persist, the saturated classification at Fin 3 reaching fragility
six, so the small-instance discreteness is partly smallness, the values growing with size, and the exhaustive
proportions are Fin 2's, the Fin 3 picture only sampled. Per the counter-bias, Fin 2 was not trusted alone, Fin 3
sampled and found to differ; the three-region division was tested against enumeration and found discrete at the
classification level though not confirmed continuous or clustered at the pair level, which was left to evaluation;
and the proportions were reported with their coverage, exhaustive over classifications, sampled over pairs and over
Fin 3. Reported per part. Nothing here is resolved. -/

end Chiralogy.Enumerate
