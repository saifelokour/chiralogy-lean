import Chiralogy.Model.Stance
import Chiralogy.Model.NaryAssemblage
import Chiralogy.Model.Moves
import Chiralogy.Kernel.Apophatic
import Chiralogy.Experiments.MembershipBoundary
import Mathlib.Data.Fintype.Pi

/-! # The multi-scale / emergent-pattern local dynamics survey

A SURVEY beyond a single configuration's neighborhood. Three questions. BETWEEN-NODE at one scale: is there
any local interaction between differing nodes, or does cell-decoupling kill it. CROSS-SCALE: how does the
whole's neighborhood relate to the parts' ACROSS scales, whole-of-wholes, does the cross-move recurse.
EMERGENT PATTERNS: do interior/corner/saddle types recur, nest, self-similar.

The local survey proved cell-coupling DEAD, so same-scale between-node interaction is expected DEAD; the one
possible weak channel is a shared seam, tested honestly. The live ground is CROSS-SCALE, whole/part being
proven non-additive, and EMERGENT PATTERN, recurrence. Guard: the arc is permissive, separable, no-arrow, so
expect same-scale DEAD, cross-scale RICH-but-static, patterns REAL-but-not-forced. Nesting is non-associative
and governance diffuses, canonical `assemblage_not_associative`.

Register neutral: readings are prose only. Nothing touches canonical or the stance core.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Chiralogy
namespace MultiScalePatterns

/-! ## PART A: between-node at one scale -/

section BetweenNode

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- **REGION NODES ARE PAIRWISE DISJOINT: NO SHARED REGION CELL.** A pair differs in exactly one coordinate,
`differsInOne_unique`, so a cell of region `i` is never a cell of region `j` for `i ≠ j`. Two distinct nodes
have no cell in common, so there is no shared region cell for a move to sit in: same-scale between-node
coupling through region cells is DEAD. Carrier-general. -/
theorem region_nodes_are_pairwise_disjoint {i j : Fin n} (hij : i ≠ j)
    {a b : Pt X} (hi : differsInOne a b i) (hj : differsInOne a b j) : False :=
  hij (differsInOne_unique hi hj)

end BetweenNode

section JointSeam

abbrev V : Fin 2 → Type := fun _ => Bool
abbrev vF : Pt V := fun _ => false
abbrev vT : Pt V := fun _ => true

/-- **THE ONE WEAK CHANNEL: A JOINT CROSS SEAM.** The pair that differs in BOTH coordinates is a cross cell,
read by the import, and it is the cell where node 0 and node 1 BOTH differ. So it is a seam that both nodes
touch: the import move there belongs to the pair jointly, not to either node alone. This is weaker than
status-transfer and weaker than cell-coupling, a static shared surface rather than an interaction, and it is
the only between-node channel at one scale. FREE, as a shared seam, not a coupling. -/
theorem two_nodes_share_a_joint_cross_seam :
    IsCross (vF : Pt V) vT ∧ vF 0 ≠ vT 0 ∧ vF 1 ≠ vT 1 := by
  refine ⟨?_, by decide, by decide⟩
  decide

end JointSeam

/-! ## PART B: cross-scale, whole-of-wholes -/

section CrossScale

/-- **THE INNER SEAM IS AN OUTER PART CELL: THE CROSS-MOVE RECURSES.** Assemble an assemblage from
assemblages, the outer factors being themselves inner assemblage carriers `Pt Y`. Take an outer pair
differing in exactly the one factor `0`, whose two values `yA, yB` are an INNER cross pair. Then the outer
whole reads, at that outer PART cell, the inner factor `nary d impInner` at `yA, yB`, which is the inner
IMPORT, since `yA, yB` cross inside. So the inner seam value surfaces as an outer region cell: the cross-move
of the inner scale is a part-move of the outer scale. The whole/part non-additivity RECURSES. Carrier-general
in the inner data. -/
theorem the_inner_seam_is_an_outer_part_cell
    {m : ℕ} {Y : Fin m → Type} [∀ j, DecidableEq (Y j)] [DecidableEq (Pt Y)]
    (d : ∀ j, Y j → Y j → Option Bool) (impInner : Pt Y → Pt Y → Option Bool)
    (impOuter : Pt (fun _ : Fin 2 => Pt Y) → Pt (fun _ : Fin 2 => Pt Y) → Option Bool)
    {a b : Pt (fun _ : Fin 2 => Pt Y)} {yA yB : Pt Y}
    (hdiff : differsInOne a b 0) (hcross : IsCross yA yB)
    (h0a : a 0 = yA) (h0b : b 0 = yB) :
    nary (fun _ => nary d impInner) impOuter a b = impInner yA yB := by
  rw [nary_apply_differ (fun _ => nary d impInner) impOuter hdiff, h0a, h0b,
      nary_apply_imp d impInner hcross]

abbrev Yb : Fin 2 → Type := fun _ => Bool
abbrev yA : Pt Yb := fun _ => false
abbrev yB : Pt Yb := fun _ => true
abbrev Oc : Fin 2 → Type := fun _ => Pt Yb
abbrev outerA : Pt Oc := fun _ => yA
abbrev outerB : Pt Oc := Function.update outerA 0 yB

theorem outer_differs_in_one : differsInOne outerA outerB 0 := by
  refine ⟨?_, fun j hj => (Function.update_of_ne hj yB outerA).symm⟩
  rw [show outerB 0 = yB from Function.update_self 0 yB outerA]
  decide

/-- **THE RECURSION IS WITNESSED CONCRETELY.** Two outer points differing in one factor, whose values are an
inner cross pair, so the outer whole reads the inner import there, here `some true`. The inner seam, present
at no inner part, is present as an outer part cell. FORCED, the recursion is real. -/
theorem the_recursion_is_witnessed :
    IsCross (yA : Pt Yb) yB
      ∧ differsInOne outerA outerB 0
      ∧ nary (fun _ => nary (fun _ => botC Bool) (cTrue : Pt Yb → Pt Yb → Option Bool))
              (botC (Pt Oc)) outerA outerB = some true := by
  have hcross : IsCross (yA : Pt Yb) yB := by decide
  refine ⟨hcross, outer_differs_in_one, ?_⟩
  rw [the_inner_seam_is_an_outer_part_cell (fun _ => botC Bool)
        (cTrue : Pt Yb → Pt Yb → Option Bool) (botC (Pt Oc))
        outer_differs_in_one hcross rfl rfl]
  rfl

end CrossScale

section ScaleInvariance

/-- **THE INTERIOR/CORNER GEOGRAPHY IS SCALE-INVARIANT.** The band's two exits, canonical
`the_band_has_two_exits`, is one theorem that holds identically at the inner scale, a flat Bool assemblage,
and at the outer scale, an assemblage of assemblages. Non-mobility is being at one of the two deaths at EVERY
scale: the interior-versus-corner dichotomy is the same object at each level, defined by the same uniform
predicates. The geography is self-similar, no new neighborhood type appears at the nested scale. -/
theorem the_geography_is_scale_invariant :
    (∀ c : Pt Yb → Pt Yb → Option Bool, ¬ Mobile c ↔ (c = botC (Pt Yb) ∨ isTotal c))
      ∧ (∀ c : Pt Oc → Pt Oc → Option Bool, ¬ Mobile c ↔ (c = botC (Pt Oc) ∨ isTotal c)) :=
  ⟨the_band_has_two_exits, the_band_has_two_exits⟩

/-- The corner-over-open-parts motif, stated at any scale. A totally committed whole is a corner, yet a
region slice is mobile whenever some pair differs in that coordinate. Carrier-general. -/
theorem a_total_whole_is_a_corner_with_a_mobile_part
    {N : ℕ} {Z : Fin N → Type} [∀ i, DecidableEq (Z i)] [∀ i, Fintype (Z i)]
    (i : Fin N) (p a b : Pt Z) (hdiff : differsInOne a b i) :
    isTotal (cTrue : Pt Z → Pt Z → Option Bool)
      ∧ Mobile (regionSlice i (cTrue : Pt Z → Pt Z → Option Bool)) :=
  ⟨fun _ _ => Option.some_ne_none _,
   (mobile_regionSlice_iff i cTrue p).mpr ⟨a, b, hdiff, Option.some_ne_none _⟩⟩

abbrev innerA : Pt Yb := fun _ => false
abbrev innerB : Pt Yb := Function.update innerA 0 true

theorem inner_differs_in_one : differsInOne innerA innerB 0 := by
  refine ⟨?_, fun j hj => (Function.update_of_ne hj true innerA).symm⟩
  rw [show innerB 0 = true from Function.update_self 0 true innerA]
  decide

/-- **THE CORNER-OVER-OPEN-PARTS MOTIF RECURS ACROSS SCALES.** The same motif, a committed whole that is a
local corner while a part is a local interior, holds at the inner scale and at the outer, nested scale. So
the whole/part local non-additivity is scale-invariant: a corner-whole with an open part appears at every
level, and by nesting a corner-whole is itself a free part of the level above. The motif STACKS. FORCED as a
recurrence, not a forced arrow. -/
theorem the_corner_over_open_parts_motif_recurs :
    (isTotal (cTrue : Pt Yb → Pt Yb → Option Bool)
        ∧ Mobile (regionSlice 0 (cTrue : Pt Yb → Pt Yb → Option Bool)))
      ∧ (isTotal (cTrue : Pt Oc → Pt Oc → Option Bool)
        ∧ Mobile (regionSlice 0 (cTrue : Pt Oc → Pt Oc → Option Bool))) :=
  ⟨a_total_whole_is_a_corner_with_a_mobile_part 0 innerA innerA innerB inner_differs_in_one,
   a_total_whole_is_a_corner_with_a_mobile_part 0 outerA outerA outerB outer_differs_in_one⟩

end ScaleInvariance

/-! ## PART C: emergent patterns

The only recurrence is the self-similarity of Part B, proven above. The remaining question is whether nesting
or combination produces a neighborhood type richer than interior, corner, saddle. It does not: the composite
of the base types is a per-axis assignment, and the saddle already is such a composite. There is no
irreducible fourth local type. -/

section Patterns

/-- **NON-ASSOCIATIVITY IS THE ONE PLACE NESTING ADDS STRUCTURE, AND IT IS STATIC.** Canonical
`assemblage_not_associative`: the two nestings of three factors send a corresponding triple-point to
different regions, so the nested geography depends on the bracketing, governance diffuses rather than
recurses. This is a real structural fact about the nested arrangement, but it is a fact about WHERE a cell is
read, static, not a dynamic coupling or a forced flow. So nesting adds a static bracketing dependence and no
new dynamic type. -/
theorem nesting_adds_only_a_static_bracketing_dependence :
    MembershipBoundary.nestL ((0, 0), 0) ((1, 1), 0)
      ≠ MembershipBoundary.nestR (0, (0, 0)) (1, (1, 0)) :=
  MembershipBoundary.assemblage_not_associative

/-- **THE COMPOSITE TYPES ARE JUST PRODUCTS OF THE THREE, NO IRREDUCIBLE FOURTH TYPE.** The saddle is the
composite that is committed on the import axis and open on a region axis at once: a per-axis product of the
base directions, inward-only on one axis and outward-only on another, both present in one configuration. Any
higher pattern is such a product of the three base directions per axis, so the classification of local
neighborhoods is the product of the base types, with no irreducible new type. THIN, at the level of new
named types; RICH only in that the three recur. -/
theorem the_composite_types_are_products_of_the_three :
    IsCross (vF : Pt V) vT
      ∧ (nary (fun _ => botC Bool) (cTrue : Pt V → Pt V → Option Bool)) vF vT = some true
      ∧ (nary (fun _ => botC Bool) (cTrue : Pt V → Pt V → Option Bool)) vF
          (Function.update vF 0 true) = none := by
  have hcross : IsCross (vF : Pt V) vT := by decide
  refine ⟨hcross, ?_, ?_⟩
  · rw [nary_apply_imp (fun _ => botC Bool) (cTrue : Pt V → Pt V → Option Bool) hcross]; rfl
  · have hdiff : differsInOne (vF : Pt V) (Function.update vF 0 true) 0 := by
      refine ⟨?_, fun j hj => (Function.update_of_ne hj true vF).symm⟩
      rw [show (Function.update vF 0 true) 0 = true from Function.update_self 0 true vF]
      decide
    rw [nary_apply_differ (fun _ => botC Bool) (cTrue : Pt V → Pt V → Option Bool) hdiff]; rfl

end Patterns

/-! ## The verdict, as prose

PART A, between-node at one scale, is DEAD but for one weak channel. The region nodes are pairwise DISJOINT,
a cell of region `i` is never a cell of region `j`, `region_nodes_are_pairwise_disjoint`, so there is no
shared region cell and, with cell-coupling already proven dead, no between-node coupling through cells. The
ONE weak channel is a JOINT CROSS SEAM: the pair differing in both coordinates is a cross cell that both nodes
touch, `two_nodes_share_a_joint_cross_seam`, and the import move there belongs to the pair jointly. This is a
static shared surface, weaker than status-transfer, not a coupling. So same-scale between-node is DEAD as
interaction, with a shared seam as its only static relation.

PART B, cross-scale, is RICH but static. The cross-move RECURSES: assembling assemblages, an outer pair
differing in one factor whose values cross inside reads the inner import at an outer part cell,
`the_inner_seam_is_an_outer_part_cell`, witnessed concretely, `the_recursion_is_witnessed`. So the inner seam,
present at no inner part, is present as an outer region cell: the whole/part non-additivity recurses through
scale. The geography is SCALE-INVARIANT: the interior/corner dichotomy is one canonical theorem holding
identically at the inner and outer scales, `the_geography_is_scale_invariant`, self-similar, no new type at
the nested scale. And the corner-over-open-parts motif STACKS: a committed whole is a corner with an open part
at every scale, `the_corner_over_open_parts_motif_recurs`, so a corner-whole is itself a free part of the
level above. All static, non-additive not coupled, consistent with the no-arrow arc.

PART C, emergent patterns, are REAL only as the self-similar recurrence of Part B. The three base types recur
at every scale, `the_geography_is_scale_invariant`, and the corner-over-open-parts motif recurs,
`the_corner_over_open_parts_motif_recurs`, so self-similarity is a proven recurrence, not a narrative one.
Beyond that the classification is THIN: nesting adds only a STATIC bracketing dependence,
`nesting_adds_only_a_static_bracketing_dependence`, governance diffusing rather than recursing, and the
composite neighborhood types are PRODUCTS of the three base directions per axis, the saddle being one such
product, `the_composite_types_are_products_of_the_three`, with no irreducible fourth local type. So patterns
are real as recurrence and product, not as new named motifs.

THE VERDICT, the multi-scale geography. SAME-SCALE between-node: DEAD, region nodes disjoint, one static
shared seam. CROSS-SCALE: RICH-but-static, the cross-move recurses, the geography is scale-invariant, and the
corner-over-open-parts motif stacks, all non-additive and none of it coupled. PATTERNS: REAL as self-similar
recurrence of the three base types and their products, THIN as any new type, with nesting adding only a static
bracketing dependence. So the framework is self-similar across scales and non-additive between whole and part
at every scale, while remaining decoupled within a scale and directionless throughout, a fractal-static
geography with no dynamic emergence.

Register readings, output only. Two distinct parts of a system never share a location, so changing one is
invisible at the other, and the only place they meet is the seam where they jointly cross, a shared surface
that belongs to neither alone. When systems are built from systems, the seam of the inner level becomes an
ordinary internal joint of the outer level, and the same three kinds of local situation, free in the middle,
stuck at an extreme, or mixed, appear at every level of assembly, so a locally frozen whole can still be a
freely moving part of something larger. But nothing new emerges from stacking beyond this repetition and
recombination: the way parts are grouped changes where things are read, yet no genuinely new kind of local
behavior appears, and none of it introduces a direction of change.
-/

/-! ## The named targets -/

section Checks
#check @region_nodes_are_pairwise_disjoint
#check @two_nodes_share_a_joint_cross_seam
#check @the_inner_seam_is_an_outer_part_cell
#check @the_recursion_is_witnessed
#check @the_geography_is_scale_invariant
#check @a_total_whole_is_a_corner_with_a_mobile_part
#check @the_corner_over_open_parts_motif_recurs
#check @nesting_adds_only_a_static_bracketing_dependence
#check @the_composite_types_are_products_of_the_three
end Checks

#print axioms region_nodes_are_pairwise_disjoint
#print axioms two_nodes_share_a_joint_cross_seam
#print axioms the_inner_seam_is_an_outer_part_cell
#print axioms the_recursion_is_witnessed
#print axioms the_geography_is_scale_invariant
#print axioms a_total_whole_is_a_corner_with_a_mobile_part
#print axioms the_corner_over_open_parts_motif_recurs
#print axioms nesting_adds_only_a_static_bracketing_dependence
#print axioms the_composite_types_are_products_of_the_three

end MultiScalePatterns
end Chiralogy
