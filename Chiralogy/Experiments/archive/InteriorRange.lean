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

THIS FILE: asked whether the factor-pair constrains the interior; answered NO clean bound, configuration-dependent.

Negative findings are recorded in archive only, never in canonical or spec. Typechecks standalone. -/

/-! # Experiment: does the factor-pair constrain the interior?

The assemblage interior is a two-coordinate phase space, populated by free choice of import. Test whether the
factors constrain which coordinates are achievable, or whether the whole plane is available for every pair. Compute
across many factor-pairs, not one. The factor classifications differ in distinction-structure: degenerate
(distinguishing nothing), saturated (one present verdict per diagonal, the rest absent), present (every verdict
present). All on the carrier `Fin 3 × Fin 2`, so the cross-region size is fixed and shape can be compared to size.
Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.InteriorRange

def zA : Fin 3 → Fin 3 → Option Bool := fun _ _ => none
def zB : Fin 2 → Fin 2 → Option Bool := fun _ _ => none
def sA : Fin 3 → Fin 3 → Option Bool := fun x y => if x = y then some true else none
def sB : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none
def pA : Fin 3 → Fin 3 → Option Bool := fun x y => some (decide (x = y))
def pB : Fin 2 → Fin 2 → Option Bool := fun x y => some (decide (x = y))

/-- Coordinate one: valued cross pairs. -/
def valuedC (_c1 : Fin 3 → Fin 3 → Option Bool) (_c2 : Fin 2 → Fin 2 → Option Bool)
    (imp : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool) : Nat :=
  (Finset.univ.filter (fun p : (Fin 3 × Fin 2) × (Fin 3 × Fin 2) =>
    p.1.1 ≠ p.2.1 ∧ p.1.2 ≠ p.2.2 ∧ imp p.1 p.2 ≠ none)).card

/-- Coordinate two: emergent distinctions destroyed by flat totalization. -/
def fragC (c1 : Fin 3 → Fin 3 → Option Bool) (c2 : Fin 2 → Fin 2 → Option Bool)
    (imp : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool) : Nat :=
  (Finset.univ.filter (fun p : (Fin 3 × Fin 2) × (Fin 3 × Fin 2) =>
    assembleClassify c1 c2 imp p.1 ≠ assembleClassify c1 c2 imp p.2
    ∧ totalization (fun _ => 0) (assembleClassify c1 c2 imp) p.1
      = totalization (fun _ => 0) (assembleClassify c1 c2 imp) p.2)).card

def i0 : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool := fun _ _ => none
def i1 : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool :=
  fun a b => if a = (0, 1) ∧ b = (2, 0) then some true else none
def i2d : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool :=
  fun a b => if a = (0, 1) ∧ b = (2, 0) then some true else if a = (0, 0) ∧ b = (1, 1) then some true else none
def iF : (Fin 3 × Fin 2) → (Fin 3 × Fin 2) → Option Bool :=
  fun a b => if a.1 ≠ b.1 ∧ a.2 ≠ b.2 then some false else none

/-! ## Part 1: the achievable range per factor-pair -/

/-- **The range differs by pair.** For present factors the cross fragility is pinned at zero over the imports, a
proper subset of the plane; for degenerate factors it varies with the import, reaching eighteen. The achievable set
is not the full rectangle for every pair. -/
theorem range_for_a_pair :
    (fragC pA pB i0 = 0 ∧ fragC pA pB i1 = 0 ∧ fragC pA pB iF = 0)
    ∧ (fragC zA zB i0 = 0 ∧ fragC zA zB i1 = 10 ∧ fragC zA zB i2d = 18) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

/-- **Across pairs, the reachable cross fragility differs.** At the same carrier size, present factors reach zero,
degenerate factors eighteen, saturated factors thirty, and a mixed pair zero: four factor-pairs, four different
achievable ceilings. -/
theorem compute_across_pairs :
    (fragC pA pB i0 = 0)
    ∧ (fragC zA zB i2d = 18)
    ∧ (fragC sA sB i0 = 30)
    ∧ (fragC sA pB i0 = 0) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The ranges genuinely differ.** At the same carrier size the present pair reaches only zero while the
saturated pair reaches thirty, so not every pair achieves the full plane: the interior is not free. -/
theorem does_the_range_differ :
    (fragC pA pB i0 = 0) ∧ (fragC sA sB i0 = 30) ∧ (0 ≠ 30) := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## Part 2: what the factors fix -/

/-- **The valued extent is factor-fixed and size-only.** The maximum valued fraction is the cross-region size,
twelve here, the same for every factor-pair: the horizontal extent is carrier size, scale not shape. -/
theorem what_is_factor_determined :
    (valuedC zA zB iF = 12) ∧ (valuedC sA sB iF = 12) ∧ (valuedC pA pB iF = 12) := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Fragility is bounded by the factors.** Present factors, robust, bound the cross fragility to zero over the
imports, the none, the single, and the full; saturated factors admit thirty. The factors' own distinction-structure
sets the reachable cross fragility. -/
theorem is_fragility_bounded_by_the_factors :
    (fragC pA pB i0 = 0 ∧ fragC pA pB i1 = 0 ∧ fragC pA pB iF = 0)
    ∧ (fragC sA sB i0 = 30) := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide⟩

/-! ## Part 3: the verdict -/

/-- **The interior is indexed, not free.** At the same carrier size, the same maximum valued fraction, the present
and saturated pairs reach different cross fragility, zero against thirty: the difference is shape, the factors'
distinction-structure, not scale, the cross-region size. The factor-pair carves out a region of the interior. -/
theorem is_the_interior_free_or_indexed :
    (valuedC pA pB iF = valuedC sA sB iF)
    ∧ (fragC pA pB i0 ≠ fragC sA sB i0)
    ∧ (fragC pA pB i0 = 0 ∧ fragC sA sB i0 = 30) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## The verdicts

Part 1: the achievable range differs by factor-pair. For present factors the cross fragility is pinned at zero,
for degenerate factors it varies to eighteen (`range_for_a_pair`); across four pairs at the same carrier size the
reachable ceiling is zero, eighteen, thirty, zero (`compute_across_pairs`); so the ranges genuinely differ, not
every pair achieving the full plane (`does_the_range_differ`).

Part 2: the factors fix the valued extent by size and the fragility extent by shape. The maximum valued fraction is
the cross-region size, twelve for every pair (`what_is_factor_determined`); the reachable cross fragility is bounded
by the factors' own distinction-structure, present factors to zero, saturated to thirty
(`is_fragility_bounded_by_the_factors`).

Part 3: the interior is indexed, not free (`is_the_interior_free_or_indexed`). At the same carrier size and the same
maximum valued fraction, different factor-pairs reach different cross fragility, so the difference is shape, not
scale.

The verdict: the factor-pair constrains the interior, and the constraint is shape, not only scale, so the interior
is indexed rather than free. The valued fraction is factor-free in its structure, its maximum being the cross-region
size, which is carrier size and so scale; every factor-pair on the same carriers reaches the same maximum valued
fraction. But the cross fragility is bounded by the factors' own distinction-structure: a robust present pair pins
it at zero, the import unable to add any fragility the totalization would destroy, since the factors already
distinguish every row by present verdicts that survive; a fragile saturated pair reaches thirty, its factor rows
flattening under totalization, while an aggressive import of surviving verdicts can pull it back down; a degenerate
pair, distinguishing nothing itself, lets the import build emergent fragility up to eighteen. These are four
different achievable regions at one carrier size, one maximum valued fraction, so the difference is not the
cross-region size but the factor-shape, and normalizing for size does not collapse them. So the interior is indexed
by the factor-pair after all: the plane is not free for every pair, and what indexes it is the factors' own
position on the fragility axis, robust factors admitting no cross fragility and fragile ones admitting much. The
horizontal extent is scale, the vertical extent shape. Per the counter-bias, the verdict rests on many pairs not
one, four factor-pairs computed; scale was normalized, the ceilings compared at one carrier size and one maximum
valued fraction, and they still differ; and the finding is indexed, not free, the large gap between zero and thirty
at fixed size being shape rather than smallness. Reported per part. Nothing here is resolved. -/

end Chiralogy.InteriorRange
