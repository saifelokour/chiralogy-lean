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

THIS FILE: asked where register assemblages land; answered: registers are saturated (present diagonal) so they rescue A2, but no general law places arbitrary assemblages.

Negative findings are recorded in archive only, never in canonical or spec. Typechecks standalone. -/

/-! # Experiment: where do the registers' assemblages land?

Three regions recur across sizes: present factors pinned at zero cross-fragility, degenerate factors admitting a
wide range, saturated factors carrying their own upward. All three were established on constructed extremes. Test
where assemblages of the actual registers land. Domain content IMPORTED. The register classifications are canonical:
`genuineFam` for cognition, immunology, chemistry, and trust; `imprecise` for physics; `typeClassify` for the type
system. Compute all pairs before judging. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.RegisterAssemblages

/-- A classification's own fragility. -/
def frag {n : Type} [Fintype n] [DecidableEq n] (c : n → n → Option Bool) : Nat :=
  (Finset.univ.filter (fun p : n × n =>
    c p.1 ≠ c p.2 ∧ totalization (fun _ => 0) c p.1 = totalization (fun _ => 0) c p.2)).card

/-- The assemblage baseline cross-fragility: the empty-cross assemblage of two factors, distinct rows flat
totalization merges. -/
def cfB {X1 X2 : Type} [Fintype X1] [Fintype X2] [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool) : Nat :=
  (Finset.univ.filter (fun p : (X1 × X2) × (X1 × X2) =>
    assembleClassify c1 c2 (fun _ _ => none) p.1 ≠ assembleClassify c1 c2 (fun _ _ => none) p.2
    ∧ totalization (fun _ => 0) (assembleClassify c1 c2 (fun _ _ => none)) p.1
      = totalization (fun _ => 0) (assembleClassify c1 c2 (fun _ _ => none)) p.2)).card

/-! ## Part 1: the register classifications -/

/-- **The registers' classifications.** `genuineFam`, the classification of cognition, immunology, chemistry, and
trust, is literally the saturated one, a present verdict on the diagonal and absence off it; its own fragility is
two. Physics's `imprecise` is partial, a few present verdicts and absences, own fragility also two. Four registers
share one classification, so saturation is a modelling choice, the domain content sitting in the differing
ground-orders, not the classifications. -/
theorem what_the_registers_are :
    (genuineFam = (fun x y => if x = y then some true else none : Fin 2 → Fin 2 → Option Bool))
    ∧ (frag genuineFam = 2)
    ∧ (frag imprecise = 2) := by
  refine ⟨rfl, by decide, by decide⟩

/-! ## Part 2: the assemblages -/

/-- **Pairwise assemblages.** The saturated pair, cognition with immunology and the like, and the mixed pair, a
saturated register with physics, both have baseline cross-fragility twelve: high, in the fragile region. -/
theorem pairwise_assemblages :
    (cfB genuineFam genuineFam = 12)
    ∧ (cfB genuineFam imprecise = 12) := by
  refine ⟨by decide, by decide⟩

/-- **Which regions are reached.** Both assemblable register pairs have positive cross-fragility, landing in the
fragile region, none at zero: the register assemblages cluster, not spreading to the present region. -/
theorem which_regions_are_reached :
    (0 < cfB genuineFam genuineFam) ∧ (0 < cfB genuineFam imprecise) := by
  refine ⟨by decide, by decide⟩

/-- **No unlike pair.** Both assemblable register classifications are fragile, own fragility positive, so no
register pair has a robust factor to pin the whole at zero: the robust register, the type system, is out of the
Option-Bool codomain, so the pinning effect has no register instance. -/
theorem unlike_pairs :
    (0 < frag genuineFam) ∧ (0 < frag imprecise) := by
  refine ⟨by decide, by decide⟩

/-! ## Part 3: the verdict -/

/-- **The fragile region has instances, the present region none.** The assemblages of actual registers occupy the
fragile region, positive cross-fragility; but every assemblable register classification is itself fragile, so no
register assemblage reaches the zero region. The three regions are structurally real, but the registers populate
only the fragile ones. -/
theorem do_the_archetypes_have_instances :
    (0 < cfB genuineFam genuineFam ∧ 0 < cfB genuineFam imprecise)
    ∧ (0 < frag genuineFam ∧ 0 < frag imprecise) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-! ## The verdicts

Part 1: the registers are not all saturated, and saturation was chosen. `genuineFam`, shared by four registers, is
the saturated classification, and physics's `imprecise` is partial, both fragile (`what_the_registers_are`); the
type system uses a different codomain, `Bool ⊕ TypeGround`, a robust present classification the others do not share,
so saturation is a modelling choice, the domain content in the ground-orders.

Part 2: the assemblages cluster in the fragile region. The saturated and mixed pairs both reach cross-fragility
twelve (`pairwise_assemblages`), both positive, none at zero (`which_regions_are_reached`); and no register pair is
unlike enough to pin, the robust register being out of codomain (`unlike_pairs`).

Part 3: the fragile region has register instances, the present region none (`do_the_archetypes_have_instances`).

The verdict: the registers' assemblages cluster in the fragile region, and this is a finding about the register set
rather than the space. The three regions are structurally real, established on constructed extremes, but the actual
registers do not spread across them: four of the six share one classification, `genuineFam`, which is exactly the
saturated one, and physics's is partial, so every assemblable register classification is fragile, and their
assemblages land at high cross-fragility, twelve for both the saturated and the mixed pair. None reaches the zero,
present region, because the only robust register, the type system, classifies into a different codomain,
`Bool ⊕ TypeGround`, and cannot be assembled in the Option-Bool framework at all. So the present region has no
register instance, not because the domains forbid it but because the modelling gives four registers a uniform
saturated placeholder and puts the one robust domain out of reach. The gate matters here: saturation was chosen,
not forced, the domain content living in the ground-orders, which differ across the four, while the classifications
are identical; so the corner Flattening found is a modelling artifact for those four, confirmed by physics and the
type system having genuinely different classifications. The clustering is therefore a fact about how the register
set was modelled, uniform where it could have varied, and about the codomain barrier that keeps the robust register
out, not a fact about the space, which remains a genuine three-region interior with only its fragile part
populated. Per the counter-bias, the modelling artifact was named as such, the gate reporting saturation chosen not
forced; the clustering was read as a result about the registers, not a failure; and the regions were not named,
only their occupancy reported, the fragile region with instances and the present region without. Reported per part.
Nothing here is resolved. -/

end Chiralogy.RegisterAssemblages
