import Chiralogy.Model.NaryAssemblage
import Chiralogy.Model.Moves
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Pi

/-! # The import-structure survey (wide)

A SURVEY of what an import IS as a first-class object. An import is the value a classification places on the
cross cells, the character-giving part of a register. Is the import space a bare function space, or does it
carry framework-forced structure: relations, an order, composition, families, a determination-relation to the
iso-type. The widest and most decisive question is D: is the import FINER than the iso-type, two isomorphic
registers carrying genuinely different imports, or is it determined by the iso-type.

No smuggled expectations. DEAD, a fully arbitrary space, is a first-class outcome. A structure that is only
the iso-type or the value-space type restated is NOT new import-structure. The closed
no-import-free-universal-property result is not reopened: this surveys the structure OF the free input, not a
derivation of it. The math decides.

Register neutral: readings are prose only. Nothing touches canonical or the stance core.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Chiralogy
namespace ImportStructure

/-! ## PART D, THE CRUX: is the import finer than the iso-type?

The direct test. Two relabeling-isomorphic classifications: are their imports related by the relabeling
(determined by the iso-type), or can they differ un-absorbed (finer). The answer splits on which relabeling:
structure-preserving relabelings absorb the import, structure-mixing ones do not preserve the cross at all. -/

section Absorbed

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- **A STRUCTURE-PRESERVING RELABELING ABSORBS THE IMPORT.** If a carrier bijection keeps the cross region
fixed (`CrossStable`), then at a cross cell the relabeled classification reads the original import at another
cross cell, so it carries import to import: the import of a `CrossStable`-isomorphic register is the original
import transported by the relabeling, determined up to that relabeling. So relative to the assemblage iso-type,
the import is NOT finer. Carrier-general. -/
theorem crossStable_relabel_absorbs_the_import (e : Pt X ≃ Pt X) (he : CrossStable e)
    (A : Pt X → Pt X → Option Bool) {a b : Pt X} (h : IsCross a b) :
    relabel (e : Pt X → Pt X) A a b = A (e a) (e b) ∧ IsCross (e a) (e b) :=
  ⟨rfl, (he a b).1 h⟩

end Absorbed

section Mixing

abbrev W2 : Fin 2 → Type := fun _ => Bool
abbrev q00 : Pt W2 := fun _ => false
abbrev q11 : Pt W2 := fun _ => true
abbrev q01 : Pt W2 := fun i => decide (i = 1)

/-- **BUT A STRUCTURE-MIXING RELABELING DOES NOT PRESERVE THE CROSS.** A carrier bijection need not respect the
coordinate structure. The transposition swapping a fully-crossing point with a region point sends a cross cell
to a non-cross cell: `(q00, q11)` cross, its image `(q00, q01)` not. So which cells are cross is not a
bare-relation invariant, and a relabeling can carry an import value onto a region cell and vice versa. -/
theorem a_structure_mixing_relabel_breaks_the_cross :
    IsCross (q00 : Pt W2) q11
      ∧ ¬ IsCross (Equiv.swap q11 q01 q00 : Pt W2) (Equiv.swap q11 q01 q11) := by
  refine ⟨by decide, ?_⟩
  rw [show (Equiv.swap q11 q01 q00 : Pt W2) = q00 from
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide),
      show (Equiv.swap q11 q01 q11 : Pt W2) = q01 from Equiv.swap_apply_left q11 q01]
  decide

/-- **SO THE RELABELED IMPORT READS A FACTOR VALUE.** Under the structure-mixing relabeling, the relabeled
classification at the cross cell `(q00, q11)` reads the original at the REGION cell `(q00, q01)`, a factor
value, not an import value. So two bare-relation-isomorphic registers can carry different imports, un-absorbed
by any cross-preserving relabeling: the import is FINER than the bare-relation iso-type, and the extra it sees
is exactly the coordinate structure the assemblage iso-type already carries. -/
theorem the_mixing_relabel_reads_a_region_value (A : Pt W2 → Pt W2 → Option Bool) :
    relabel (Equiv.swap q11 q01 : Pt W2 → Pt W2) A q00 q11 = A q00 q01 := by
  show A (Equiv.swap q11 q01 q00) (Equiv.swap q11 q01 q11) = A q00 q01
  rw [show (Equiv.swap q11 q01 q00 : Pt W2) = q00 from
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide),
      Equiv.swap_apply_left]

end Mixing

/-! ## PART F: how a move acts on the import

A cross-cell release lowers the import, since the import map is an order embedding. -/

section Operations

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- **A RELEASE LOWERS THE IMPORT.** Partializing the import is below it, and the import map is monotone, so
the assembled classification descends: the moves act on the import through the same information order the
import map embeds. Carrier-general. -/
theorem a_release_lowers_the_import (w : Pt X → Pt X → Bool)
    (c : ∀ i, X i → X i → Option Bool) (imp : Pt X → Pt X → Option Bool) :
    cLE (importMap c (partialization w imp)) (importMap c imp) :=
  (import_order_embeds c _ _).2 (fun a b _ => partialization_le_c w imp a b)

end Operations

/-! ## The verdict, as prose

PART A, the space. CARVED, not free. As a raw SET the import is any function on the cross cells, typed by the
value space, and above located difference the cross is a free parameter (`cross_is_free_over_all_factors`,
`no_factor_forces_the_cross`), so no factor forces it. But as a STRUCTURED object the import space is heavily
carved by canonical results: only its cross-cell values matter, imports agreeing on the cross are identified
(`importMap_kernel`), and the honest representatives are the cross-supported ones
(`importMap_injective_on_crossSupported`). So beyond type and gates the space is not a bare function space, it
is a function space on the cross MODULO region-agreement, with forced order structure below.

PART B, relations. B3, the COMMITMENT ORDER: FORCED. The import map is an order embedding, `cLE` on assemblies
transmitting exactly `cLE` on the imports restricted to the cross (`importMap_is_a_meet_embedding`,
`import_order_embeds`), and it preserves the meet on the nose (`nary_meet`), with a least element, the empty
import, and NO greatest (`importMap_singles_out_emptiness`). So the imports form a meet-semilattice with bottom
and no top, a real forced order. B2, EQUIVALENCE UP TO RELABELING: FORCED as the orbit relation of the
relabeling action, but see Part D for its content. B1, a distinctness order read on the cross: not new, it is
the distinctness lattice already surveyed, restricted to the cross cells, so FREE/derived, not a fresh import
relation.

PART C, algebra. DEAD, no forced composition. Composition of assemblages MULTIPLIES the slot count
non-tensorially (`cross_cell_count`), but manufactures FRESH cross cells no part carried
(`composition_creates_a_fresh_off_diagonal_slot`), and the composite's import on those fresh slots is a free
choice, unconstrained by the parts. So the proven slot-COUNTING has no algebraic counterpart: there is no
forced map from the parts' imports to the whole's, the composite import is FREE. Counting-only.

PART D, THE CRUX. The import is DETERMINED by the assemblage iso-type, and only APPARENTLY finer relative to
the bare-relation iso-type. A structure-preserving relabeling absorbs the import: at a cross cell it reads the
original import at another cross cell (`crossStable_relabel_absorbs_the_import`), so `CrossStable`-isomorphic
registers have relabeling-related imports, no finer than the iso-type. A structure-MIXING relabeling does not
preserve the cross at all (`a_structure_mixing_relabel_breaks_the_cross`), so it carries an import value onto a
region cell (`the_mixing_relabel_reads_a_region_value`): relative to the bare-relation iso-type, which forgets
the coordinate structure, the import is finer, since bare-isomorphic registers can carry different imports. But
the extra the import sees is EXACTLY the coordinate/cross structure, which the assemblage iso-type already
tracks and the invariance/variance surveys already reached. So there is NO new character below the assemblage
iso-type: the import is its share of that iso-type, finer only than the wrong, structure-forgetting notion.

PART E, families. The import space partitions into the meet-semilattice of cross-supported representatives
(Parts A, B), orbited by the structure-preserving relabelings (Part D), which is exactly the assemblage
iso-classes. So families are indexed by the iso-type, refined by the forced import order, with the value-space
cardinality and slot count as coarse coordinates on top. No index finer than the iso-type, since Part D found
nothing below it.

PART F, operations. Relabeling ACTS on the import: structure-preserving relabelings permute cross-cell values
within the import space (the orbit action), structure-mixing ones leave it, mapping import to region. The
commitment moves act through the import order: a cross-cell release lowers the import
(`a_release_lowers_the_import`), a fill raises it, and a region-cell move does not touch the import at all
(`importMap_kernel`, region changes overwritten). So the import is MOVED by cross-cell moves along the forced
meet-semilattice, FIXED by region-cell moves.

THE VERDICT: FAMILIED-BY-ISO-TYPE. The import space is not fully arbitrary, it carries a forced meet-semilattice
order with a bottom and no top, identified modulo cross-agreement; but it is not finer than the assemblage
iso-type either, structure-preserving relabelings absorbing all its character
(`crossStable_relabel_absorbs_the_import`), the apparent finer-ness being only relative to the
structure-forgetting bare-relation iso-type (`a_structure_mixing_relabel_breaks_the_cross`,
`the_mixing_relabel_reads_a_region_value`). So imports are structured exactly as much as the iso-type and its
partial-invariant lattice give, no finer, with no forced composition algebra (Part C DEAD) atop the proven
counting. The import is the character-share of the iso-type, carved but not a new layer.

Register readings, output only. What a system imports is not free-floating: it lives on the seams where its
parts cross, only the seam values count, and those seam values carry a built-in order, from supplying nothing
up through richer supplies, with a least point that supplies nothing and no richest point at all. But the
import is not a secret extra identity beneath the system's shape: any faithful re-presentation of the system
carries its imports along, and two systems of the same shape import the same up to that re-presentation. What
looks like a hidden import-identity is only visible if you forget how the parts are wired, which is to forget
part of the shape. And when systems combine, the joint import on the new seams is a free choice, not computed
from the parts.
-/

/-! ## The named targets -/

section Checks
#check @crossStable_relabel_absorbs_the_import
#check @a_structure_mixing_relabel_breaks_the_cross
#check @the_mixing_relabel_reads_a_region_value
#check @a_release_lowers_the_import
end Checks

#print axioms crossStable_relabel_absorbs_the_import
#print axioms a_structure_mixing_relabel_breaks_the_cross
#print axioms the_mixing_relabel_reads_a_region_value
#print axioms a_release_lowers_the_import

end ImportStructure
end Chiralogy
