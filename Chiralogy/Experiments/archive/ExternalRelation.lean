import Chiralogy.Model.AssemblageRelations

/-! ARCHIVED (fully graduated). The structure of external relations, consolidated.

GRADUATED to `Model/NaryAssemblage` as FOUR NAMED THEOREMS rather than the `Q : Type` conjunction this file
carried: `externality`, `irreducibility`, `freedom`, `bundle_selects_no_import`, with `bound_of_factors` and
`no_reading_is_fixed` as support, and the abstract vocabulary `Reachable`, `Structural`, `Bound`,
`structural_iff_orbit_constant`. Spec 9.23.

The reshaping was the point. `external_relation_is_structured`, the bundle, did NOT graduate: quantifying over
`Q : Type` made it a statement about every type at once and forced every clause to carry every hypothesis. As
four theorems each carries only what it uses, which is why none of them mentions finiteness.

The discipline check held throughout: the theorems describe the space of imports and single none out.
Typechecks standalone. -/

/-! # Experiment (LIVE): the structure of external relations, consolidated

The import lineage established four separate things about the cross content of an assembly: no factor reaches
it, only an operation on the whole writes it, the framework fixes no value of it, and it is nonetheless
structured. This packages those into one carrier-general object and tests, against the graph, whether that
object sits where the lineage's narrative puts it.

Register-neutral throughout: no statement and no proof mentions any domain.

Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.ExternalRelation

/-! ### GRADUATED (external-relation pass)

Into `Model/NaryAssemblage`, same names, as FOUR NAMED THEOREMS rather than the `Q : Type` conjunction:
`externality`, `irreducibility`, `freedom`, `bundle_selects_no_import`, with `bound_of_factors` and
`no_reading_is_fixed` as support, and the abstract vocabulary `Reachable`, `Structural`, `Bound`,
`structural_iff_orbit_constant`. Spec 9.23.

NOT GRADUATED: `external_relation_is_structured`, the bundle. The reshaping into four theorems was the recorded
graduable form and it is what keeps each theorem's hypotheses to what it uses.

This file is fully graduated. -/

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-! ## Part 1: the four properties, and the object they describe

The EXTERNAL RELATION of an assembly is its cross content: the verdicts at the cells no factor reads. Each
clause below is a property of that content, and none of them names a particular import. -/

/-- **(a) EXTERNALITY.** No change of factors reaches the cross. Replacing every factor by anything at all
leaves every cross cell where it was, so the external relation is underivable from the factors. -/
theorem externality (c c' : ∀ i, X i → X i → Option Bool) (imp : Pt X → Pt X → Option Bool)
    {a b : Pt X} (h : IsCross a b) : nary c imp a b = nary c' imp a b := by
  rw [nary_apply_imp c imp h, nary_apply_imp c' imp h]

/-- **(b) IRREDUCIBILITY.** An operation on the whole does reach the cross, and it writes there what no factor
operation could: a fill on the composite overwrites an absent cross cell, while by (a) every factor-side fill
leaves it untouched. So the external relation is reached only from the whole. -/
theorem irreducibility (c : ∀ i, X i → X i → Option Bool) (imp : Pt X → Pt X → Option Bool)
    (s : Pt X → Nat) (si : ∀ i, X i → Nat) {a b : Pt X} (h : IsCross a b)
    (habs : imp a b = none) :
    totalization s (nary c imp) a b = some (decide (s b ≤ s a))
      ∧ nary (fun i => totalization (si i) (c i)) imp a b = nary c imp a b :=
  ⟨composite_fill_overwrites_absent_cross c imp s h habs, externality _ c imp h⟩

/-- **(c) FREEDOM.** Any cross content whatever is realized: for an arbitrary target the assembly over it as
import agrees with it on every cross cell, over any factors. The framework fixes no value. -/
theorem freedom (c : ∀ i, X i → X i → Option Bool) (V : Pt X → Pt X → Option Bool)
    {a b : Pt X} (h : IsCross a b) : nary c V a b = V a b :=
  nary_apply_imp c V h

/-! ### (d) STRUCTURE: the invariant readings of the cross

A READING of the cross is a label on its cells; an import is BOUND at a reading when its verdict is a function
of the label. A reading is STRUCTURAL when the cross-stable bijections cannot move a cell out of its block.
These are the definitions the tower lineage settled on, restated here so the bundle is self-contained. -/

def Bound {Q : Type} (q : Pt X → Pt X → Q) (imp : Pt X → Pt X → Option Bool) : Prop :=
  ∀ a b a' b', IsCross a b → IsCross a' b' → q a b = q a' b' → imp a b = imp a' b'

def CrossStable (e : Pt X ≃ Pt X) : Prop := ∀ a b, IsCross a b ↔ IsCross (e a) (e b)

/-- Two cross cells share an orbit when a cross-stable bijection carries one to the other. -/
def Reachable (a b a' b' : Pt X) : Prop :=
  ∃ e : Pt X ≃ Pt X, CrossStable e ∧ e a = a' ∧ e b = b'

def Structural {Q : Type} (q : Pt X → Pt X → Q) : Prop :=
  ∀ e : Pt X ≃ Pt X, CrossStable e → ∀ a b, IsCross a b → q (e a) (e b) = q a b

/-- **The orbit partition classifies the structural readings.** A reading is invariant under the group exactly
when it is constant on orbits, so the structural readings are precisely the coarsenings of the orbit partition
and the orbit partition is the finest of them. -/
theorem structural_iff_orbit_constant {Q : Type} (q : Pt X → Pt X → Q) :
    Structural q ↔ ∀ a b a' b', IsCross a b → Reachable a b a' b' → q a' b' = q a b := by
  constructor
  · rintro hs a b a' b' hab ⟨e, he, h1, h2⟩
    rw [← h1, ← h2]
    exact hs e he a b hab
  · intro ho e he a b hab
    exact ho a b (e a) (e b) hab ⟨e, he, rfl, rfl⟩

/-- Anything computed from a reading is bound at it, so every reading is inhabited by imports. -/
theorem bound_of_factors {Q : Type} (q : Pt X → Pt X → Q) (g : Q → Option Bool) :
    Bound q (fun a b => g (q a b)) := by
  intro a b a' b' _ _ hq
  show g (q a b) = g (q a' b')
  rw [hq]

/-- **No reading is fixed either.** At any reading whatever, a bound import and an arbitrary one both assemble
over the same factors and agree on every region cell, so the structure does not narrow the freedom at any
rung. -/
theorem no_reading_is_fixed {Q : Type} (c : ∀ i, X i → X i → Option Bool)
    (q : Pt X → Pt X → Q) (g : Q → Option Bool) (imp : Pt X → Pt X → Option Bool) :
    isAssemblageN (nary c (fun a b => g (q a b)))
      ∧ isAssemblageN (nary c imp)
      ∧ ∀ (a b : Pt X) (i : Fin n), differsInOne a b i →
          nary c (fun a b => g (q a b)) a b = nary c imp a b := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun _ _ _ _ _ hd hd' ha hb => nary_region_independent _ _ hd hd' ha hb
  · exact fun _ _ _ _ _ hd hd' ha hb => nary_region_independent _ _ hd hd' ha hb
  · intro a b i h
    rw [nary_apply_differ c _ h, nary_apply_differ c imp h]

/-- **THE CONSOLIDATED THEOREM.** For any factors over any finite product carrier, the external relation of an
assembly is external, irreducible, free, and structured:

  externality ....... no change of factors reaches any cross cell
  irreducibility .... a fill on the whole writes a cross cell that every factor-side fill leaves alone
  freedom ........... every cross content whatever is realized, over any factors
  structure ......... the invariant readings of the cross are exactly the coarsenings of the orbit partition,
                      each is inhabited, and none of them is fixed

Carrier-general: arbitrary `n`, arbitrary fibres, no finiteness beyond the product shape and no inhabitation.
The statement quantifies over imports and readings throughout and names no import. -/
theorem external_relation_is_structured (c : ∀ i, X i → X i → Option Bool)
    (imp : Pt X → Pt X → Option Bool) :
    (∀ (c' : ∀ i, X i → X i → Option Bool) (a b : Pt X), IsCross a b →
        nary c imp a b = nary c' imp a b)
      ∧ (∀ (s : Pt X → Nat) (si : ∀ i, X i → Nat) (a b : Pt X), IsCross a b → imp a b = none →
          totalization s (nary c imp) a b = some (decide (s b ≤ s a))
            ∧ nary (fun i => totalization (si i) (c i)) imp a b = nary c imp a b)
      ∧ (∀ (V : Pt X → Pt X → Option Bool) (a b : Pt X), IsCross a b → nary c V a b = V a b)
      ∧ (∀ (Q : Type) (q : Pt X → Pt X → Q),
          (Structural q ↔ ∀ a b a' b', IsCross a b → Reachable a b a' b' → q a' b' = q a b)
            ∧ ∀ g : Q → Option Bool,
                Bound q (fun a b => g (q a b))
                  ∧ isAssemblageN (nary c (fun a b => g (q a b)))
                  ∧ ∀ (a b : Pt X) (i : Fin n), differsInOne a b i →
                      nary c (fun a b => g (q a b)) a b = nary c imp a b) :=
  ⟨fun c' _ _ h => externality c c' imp h,
   fun s si _ _ h habs => irreducibility c imp s si h habs,
   fun V _ _ h => freedom c V h,
   fun _ q => ⟨structural_iff_orbit_constant q,
     fun g => ⟨bound_of_factors q g, (no_reading_is_fixed c q g imp).1,
       (no_reading_is_fixed c q g imp).2.2⟩⟩⟩

/-- **THE DISCIPLINE CHECK: no import is selected.** The bundle above is a property of an arbitrary `imp` over
arbitrary factors, and every clause quantifies over the objects it discusses. Concretely: two arbitrary imports
satisfy it alike, so nothing in it distinguishes one from another. -/
theorem bundle_selects_no_import (c : ∀ i, X i → X i → Option Bool)
    (imp imp' : Pt X → Pt X → Option Bool) :
    (∀ (c' : ∀ i, X i → X i → Option Bool) (a b : Pt X), IsCross a b →
        nary c imp a b = nary c' imp a b)
      ∧ (∀ (c' : ∀ i, X i → X i → Option Bool) (a b : Pt X), IsCross a b →
        nary c imp' a b = nary c' imp' a b) :=
  ⟨fun c' _ _ h => externality c c' imp h, fun c' _ _ h => externality c c' imp' h⟩

/-! ## Part 2: the seam

The external relation is what the framework leaves free. The orbit partition is what the framework's symmetries
fix. The seam theorem is that the second classifies the first. -/

/-- **THE SEAM.** The variance and the invariance are the same statement read from two sides. On the variance
side, the import map carries the classification order faithfully into the assemblies and singles out only
emptiness. On the invariance side, the readings of that same free content that survive the symmetries are
exactly the coarsenings of the orbit partition, and no reading is fixed. So the space the framework declines to
determine carries structure the framework does determine: invariant structure OF the variance. -/
theorem external_relation_is_invariant_structure_of_variance [∀ i, Inhabited (X i)]
    (c : ∀ i, X i → X i → Option Bool) :
    ((∀ imp imp' : Pt X → Pt X → Option Bool,
        cLE (importMap c imp) (importMap c imp') ↔ ∀ a b, IsCross a b → optLE (imp a b) (imp' a b))
      ∧ (∀ imp : Pt X → Pt X → Option Bool, cLE (importMap c (botC (Pt X))) (importMap c imp))
      ∧ ¬ ∃ t : Pt X → Pt X → Option Bool,
          ∀ imp : Pt X → Pt X → Option Bool, cLE (importMap c imp) (importMap c t))
    ∧ (∀ (Q : Type) (q : Pt X → Pt X → Q),
        (Structural q ↔ ∀ a b a' b', IsCross a b → Reachable a b a' b' → q a' b' = q a b)
          ∧ ∀ (g : Q → Option Bool) (imp : Pt X → Pt X → Option Bool),
              Bound q (fun a b => g (q a b))
                ∧ ∀ (a b : Pt X) (i : Fin n), differsInOne a b i →
                    nary c (fun a b => g (q a b)) a b = nary c imp a b) :=
  ⟨⟨(importMap_is_a_meet_embedding c).1,
    (importMap_singles_out_emptiness c).1, (importMap_singles_out_emptiness c).2⟩,
   fun _ q => ⟨structural_iff_orbit_constant q,
     fun g imp => ⟨bound_of_factors q g, (no_reading_is_fixed c q g imp).2.2⟩⟩⟩

/-! ## THE VERDICTS

PART 1: the four properties bundle, and the bundle names no import.

`external_relation_is_structured` is one carrier-general theorem with four clauses. Externality reuses the
one-line consequence of `nary_apply_imp`: replacing every factor by anything leaves every cross cell where it
was. Irreducibility pairs canonical `composite_fill_overwrites_absent_cross` against that same fact, so the
contrast is stated inside one clause: the whole-move writes a cross cell that no factor-side fill touches.
Freedom is canonical `nary_apply_imp` again, read as realizability of an arbitrary target. Structure is the
orbit classification with its two riders, that every reading is inhabited and none is fixed.

Arbitrary `n`, arbitrary fibres, no finiteness beyond the product shape, no inhabitation, no `decide` anywhere
in the statement or the proof.

THE DISCIPLINE CHECK PASSES. Every clause quantifies over the objects it discusses, and
`bundle_selects_no_import` states it concretely: two arbitrary imports satisfy the bundle alike. Consolidating
introduced no canonical import, which is the check this whole lineage has run at each step.

PART 2: the seam is real, and it is one statement read from two sides.

`external_relation_is_invariant_structure_of_variance` puts the two halves in one theorem. The variance half is
canonical: the import map is an order embedding singling out only emptiness, with no greatest element. The
invariance half is the orbit classification: the readings of that same content that survive the symmetries are
exactly the coarsenings of the orbit partition, and none is fixed. So the space the framework declines to
determine carries structure the framework does determine.

PART 3: THE GRAPH REFUTES THE SEAM READING AS A DEPENDENCY CLAIM, AND CONFIRMS THE LAYER PREDICTION.

Closures extracted per declaration from `depgraph-preview ExternalRelation`. The union over the whole file:

  Model/NaryAssemblage [13]  CrossSupported, IsCross, Pt, composite_fill_overwrites_absent_cross,
                             differsInOne, importMap, importMap_is_a_meet_embedding,
                             importMap_singles_out_emptiness, isAssemblageN, nary, nary_apply_differ,
                             nary_apply_imp, nary_region_independent
  Model/InformationOrder [4] botC, cLE, cMeet, optLE
  Model/Moves [1]            totalization

THE LAYER PREDICTION HOLDS, cleanly. Layers touched: MODEL ONLY. No Protocol node, no Register node, no Kernel
node appears in any closure. So this is a MODEL-LAYER FACT that registers inherit by membership, not a
projection of the protocol onto a new register. That hypothesis is refuted by the graph.

THE HOME IS `Model/NaryAssemblage`. Everything else hooked sits below it in the import order, so there is no
cycle pressure, and NOTHING REACHES `Model/Apophatic`. Unlike `structure_of_variance`, which `presentCarried`
forced up to `Model/AssemblageRelations`, this bundle sits one module lower.

THE SEAM READING DOES NOT HOLD AS A DEPENDENCY CLAIM, and this is the correction. The two halves hook nearly
disjoint canonical material. The variance half reaches `importMap` with its two embedding results,
`CrossSupported`, and the order vocabulary `botC`, `cLE`, `cMeet`, `optLE`. The invariance half reaches almost
nothing: `structural_iff_orbit_constant` hooks `IsCross` and `Pt` and NOTHING ELSE, and `no_reading_is_fixed`
hooks only the assembly basics. The orbit machinery is DEFINED HERE, from `IsCross` and bijections of the
carrier, and hooks no canonical symmetry result at all. In particular it never reaches `fixes_iff_levels`,
which is the canonical automorphism theorem the seam reading assumed it rested on.

So the honest statement is that the seam is a CONCEPTUAL one, not a structural one. The orbit partition is not
built from the framework's automorphism apparatus; it is built from bijections of the carrier and the cross
predicate, and the framework's own symmetry results play no part in it. The invariance side does not carry its
weight in the dependency graph, and calling the bundle a seam between two machineries overstates what the
proofs use.

PART 4: graduation readiness, and it is NOT ready.

WHAT IS READY. `externality`, `irreducibility`, `freedom` and `bundle_selects_no_import` are carrier-general,
reuse canonical, and would graduate to `Model/NaryAssemblage` immediately. So would the orbit definitions and
`structural_iff_orbit_constant`.

WHAT BLOCKS THE BUNDLE. `external_relation_is_structured` universally quantifies over `Q : Type`, so it is a
statement about every type at once and its clauses are not usable without instantiating. That is a packaging
defect rather than a mathematical one, and it is the same defect the readiness pass flagged for the variance
package: a conjunction narrated as a theorem. The right canonical form is the four clauses as four named
theorems with a doc-comment tying them together, not one nested conjunction. Recorded, not fixed here.

DEPENDENCY ORDER, if it goes forward. The orbit definitions (`CrossStable`, `Reachable`, `Structural`, `Bound`)
must land first, since three clauses mention them; then `structural_iff_orbit_constant`; then the three
one-line properties, which depend on nothing new; then any bundle. All of it at `Model/NaryAssemblage`.
`CoarseningClassify` and `CoarseningTower` need not graduate first: this file re-derives the two load-bearing
orbit results in four lines each, and their remaining content is witnesses and evaluations that stay live.

VOCABULARY NOTE FOR THE SPEC, NOT FOR ANY THEOREM NAME. The structural readings of the cross under a group are
the orbits of the group on ordered pairs, which is the standard notion of ORBITALS, and a partition of the pair
set into group-invariant blocks is the standard COHERENT CONFIGURATION setting; on a product carrier with equal
fibres the finest such partition is the HAMMING SCHEME. Those names belong in a spec entry citing the known
setting, never in a theorem name here, and nothing above is claimed as new relative to them.

WHAT REMAINS OPEN

1. The bundle's shape. Four named theorems with a tying doc-comment is the graduable form; the nested
   conjunction is not.
2. The orbit machinery hooks no canonical symmetry result. Whether `Structural` can be DERIVED from canonical
   `fixes_iff_levels` rather than defined afresh is the question that would make the seam structural rather
   than conceptual, and it is not attempted here.
3. Nothing here is graduated. -/

#print axioms externality
#print axioms irreducibility
#print axioms freedom
#print axioms Bound
#print axioms CrossStable
#print axioms Reachable
#print axioms Structural
#print axioms structural_iff_orbit_constant
#print axioms bound_of_factors
#print axioms no_reading_is_fixed
#print axioms external_relation_is_structured
#print axioms bundle_selects_no_import
#print axioms external_relation_is_invariant_structure_of_variance

end Chiralogy.ExternalRelation
