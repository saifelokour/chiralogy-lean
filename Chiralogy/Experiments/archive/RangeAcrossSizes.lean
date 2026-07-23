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

THIS FILE: asked whether the bound holds across sizes and shapes; answered: the obstruction is structural (the a.2 = b.2-first ordering), size-independent, so no size makes a clean bound appear.

Negative findings are recorded in archive only, never in canonical or spec. Typechecks standalone. -/

/-! # Experiment: does the constraint hold across sizes and shapes?

InteriorRange found the factors bound the assemblage's cross-fragility ceiling, shape not scale, at one carrier
size across four pairs. Test whether the pattern holds across sizes and a wider set of factor-shapes. Compute the
full grid before judging; small-instance structure has been smallness before. The factor classifications: degenerate
(distinguishing nothing), saturated (one present verdict per diagonal), present (every verdict present). Carriers
`Fin m × Fin 2` for `m = 2, 3, 4`. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.RangeAcrossSizes

def deg {m : ℕ} : Fin m → Fin m → Option Bool := fun _ _ => none
def sat {m : ℕ} : Fin m → Fin m → Option Bool := fun x y => if x = y then some true else none
def pre {m : ℕ} : Fin m → Fin m → Option Bool := fun x y => some (decide (x = y))
def nP (X : Type) : X → X → Option Bool := fun _ _ => none

/-- A classification's own fragility: distinct rows flat totalization merges. -/
def frag {n : Type} [Fintype n] [DecidableEq n] (c : n → n → Option Bool) : Nat :=
  (Finset.univ.filter (fun p : n × n =>
    c p.1 ≠ c p.2 ∧ totalization (fun _ => 0) c p.1 = totalization (fun _ => 0) c p.2)).card

/-- The assemblage's baseline cross fragility: the empty-cross assemblage of `c1` with a degenerate second factor,
its distinct rows flat totalization merges. -/
def cf (m : ℕ) (c1 : Fin m → Fin m → Option Bool) : Nat :=
  (Finset.univ.filter (fun p : (Fin m × Fin 2) × (Fin m × Fin 2) =>
    assembleClassify c1 (nP (Fin 2)) (nP (Fin m × Fin 2)) p.1
      ≠ assembleClassify c1 (nP (Fin 2)) (nP (Fin m × Fin 2)) p.2
    ∧ totalization (fun _ => 0) (assembleClassify c1 (nP (Fin 2)) (nP (Fin m × Fin 2))) p.1
      = totalization (fun _ => 0) (assembleClassify c1 (nP (Fin 2)) (nP (Fin m × Fin 2))) p.2)).card

/-- The cross fragility of an assemblage on `Fin 3 × Fin 2` with a given import. -/
def fragC (c1 : Fin 3 → Fin 3 → Option Bool) (c2 : Fin 2 → Fin 2 → Option Bool)
    (imp : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool) : Nat :=
  (Finset.univ.filter (fun p : (Fin 3 × Fin 2) × (Fin 3 × Fin 2) =>
    assembleClassify c1 c2 imp p.1 ≠ assembleClassify c1 c2 imp p.2
    ∧ totalization (fun _ => 0) (assembleClassify c1 c2 imp) p.1
      = totalization (fun _ => 0) (assembleClassify c1 c2 imp) p.2)).card

def i0 : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool := fun _ _ => none
def i2d : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool :=
  fun a b => if a = (0, 1) ∧ b = (2, 0) then some true else if a = (0, 0) ∧ b = (1, 1) then some true else none

/-! ## Part 1: across sizes -/

/-- **The baseline across sizes.** Saturated factors give a baseline cross fragility that grows with size, twelve,
thirty, fifty-six; present and degenerate stay zero at every size. The ordering, present and degenerate below
saturated, persists. -/
theorem ceilings_at_several_sizes :
    (cf 2 sat = 12 ∧ cf 3 sat = 30 ∧ cf 4 sat = 56)
    ∧ (cf 2 deg = 0 ∧ cf 3 deg = 0 ∧ cf 4 deg = 0)
    ∧ (cf 2 pre = 0 ∧ cf 3 pre = 0 ∧ cf 4 pre = 0) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide⟩⟩

/-- **The baseline is a function of shape and size.** At one carrier size the baseline is fixed by the shape, thirty
for saturated, zero for degenerate and present; the shape changes it, so shape is the index. -/
theorem is_the_ceiling_a_function_of_shape_and_size :
    (cf 3 sat = 30 ∧ cf 3 deg = 0 ∧ cf 3 pre = 0)
    ∧ (cf 3 sat ≠ cf 3 deg) := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide⟩

/-- **Normalized, the ordering holds.** The saturated baseline as a fraction of all pairs grows, three quarters,
five sixths, seven eighths, so growth with size is not the whole story, the fraction rising toward one; present and
degenerate stay at zero. -/
theorem normalize :
    (cf 2 sat * 36 < cf 3 sat * 16)
    ∧ (cf 3 sat * 64 < cf 4 sat * 36)
    ∧ (cf 3 deg = 0 ∧ cf 3 pre = 0) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## Part 2: a wider set of shapes -/

/-- **Wider shapes.** A like fragile pair, saturated with saturated, has a high baseline, thirty; an unlike pair,
saturated with present, has baseline zero, the present factor robustifying the whole. A single robust factor pins
the pair. -/
theorem more_factor_shapes :
    (fragC sat sat i0 = 30)
    ∧ (fragC sat pre i0 = 0) := by
  refine ⟨by decide, by decide⟩

/-- **Own fragility does not predict the ceiling.** Degenerate and present factors have the same own fragility,
zero, yet the assemblage reaches different cross fragility, eighteen for the degenerate pair under an import, zero
for the present pair: so the ceiling is not a function of the factors' own fragility, and the constraint is not mere
inheritance. -/
theorem does_the_factors_own_fragility_predict_the_ceiling :
    (frag (deg : Fin 3 → Fin 3 → Option Bool) = 0 ∧ frag (pre : Fin 3 → Fin 3 → Option Bool) = 0)
    ∧ (fragC deg deg i2d = 18 ∧ fragC pre pre i2d = 0) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-! ## Part 3: is the space carved? -/

/-- **The extreme regions recur.** The present region, cross fragility zero, recurs at every size; the saturated
region, positive cross fragility, recurs at every size. The regions are more than points, holding across sizes. -/
theorem which_regions_recur :
    (cf 2 pre = 0 ∧ cf 3 pre = 0 ∧ cf 4 pre = 0)
    ∧ (0 < cf 2 sat ∧ 0 < cf 3 sat ∧ 0 < cf 4 sat) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

/-- **No region is empty for all pairs, but each pair is confined.** Present pairs are confined to cross fragility
zero over their imports, so the positive region is empty for them; but degenerate pairs reach it, eighteen, so it is
not empty for all pairs. The emptiness is per-pair confinement, not a structural hole. -/
theorem are_any_regions_empty :
    (fragC pre pre i0 = 0 ∧ fragC pre pre i2d = 0)
    ∧ (0 < fragC deg deg i2d) := by
  refine ⟨⟨by decide, by decide⟩, by decide⟩

/-! ## The verdicts

Part 1: the ordering holds across sizes, normalized. The saturated baseline grows with size, present and degenerate
stay zero (`ceilings_at_several_sizes`); the baseline is fixed by shape and size (`is_the_ceiling_a_function_of_shape_and_size`);
and normalized the saturated fraction rises toward one while present and degenerate stay zero, so growth is not
mistaken for shape (`normalize`).

Part 2: a wider set confirms the constraint, and it is not inheritance. A like fragile pair has a high baseline, an
unlike pair with a present factor zero (`more_factor_shapes`); and own fragility does not predict the ceiling,
degenerate and present factors sharing own fragility zero yet reaching eighteen and zero
(`does_the_factors_own_fragility_predict_the_ceiling`).

Part 3: the regions recur and the confinement is per-pair. The present and saturated regions recur at every size
(`which_regions_recur`); no region is empty for all pairs, but each pair is confined, present pairs to zero
(`are_any_regions_empty`).

The verdict: the constraint holds across sizes and shapes, and it is not the inheritance of the factors' own
fragility. Across three carrier sizes the ordering persists: saturated factors give a high cross fragility that
grows with size, twelve, thirty, fifty-six, while present and degenerate factors stay at zero baseline, and
normalizing by the total pairs the saturated fraction rises toward one rather than staying fixed, so the growth is
real and the ordering survives normalization. The baseline is a function of shape and size, fixed once both are
given. A wider set of shapes confirms this, an unlike pair with a present factor pinned at zero by the robust
factor. But the gate fails: the factors' own fragility does not determine the assemblage's ceiling, since degenerate
and present factors both have own fragility zero yet the degenerate pair reaches cross fragility eighteen under an
import while the present pair stays at zero. So the constraint is not fragility inherited, a cleaner story the data
refuses; it is the factors' distinction-structure more finely, degenerate factors offering absence for the import
to make fragile, present factors offering none, saturated factors carrying their own fragility into the product.
The space is carved into recurring regions, the present region at zero and the saturated region positive both
holding across sizes, and no part of the plane is empty for every pair, but each pair is confined to its own region,
present pairs to the zero line whatever the import. So the interior is indexed by factor-shape across sizes, the
index not reducible to a single known quantity. Per the counter-bias, the ordering was computed at three sizes not
assumed, and it held; growth was normalized and the fraction still rose, shape not scale; and the inheritance gate
was checked and failed, so no cleaner fragility story is asserted where the data denies it. Reported per part.
Nothing here is resolved. -/

end Chiralogy.RangeAcrossSizes
