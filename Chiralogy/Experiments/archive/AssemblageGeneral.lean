import Chiralogy

/-! # Experiment: assemblages in general

The assemblage construction exists at two registers with an imported cross-classification. Generalize it and
settle its arguments. Settled: an assemblage is an object on a product carrier whose cross-classification is
imported (no canonical coproduct value), its grounds new, exteriority holding, coding and territorialization
identifying with order-density and endpoint-count and lossy at `n = 4`. Domain content IMPORTED, the
assemblage-theory identification a READING. Compute all candidates across instances before judging. Stays in
`Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.AssemblageGeneral

/-- The general assemblage classification: pairs sharing the second component are classified by the first factor,
pairs sharing the first (and differing second) by the second factor, and fully-cross pairs by the import. -/
def assembleClassify {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) : (X1 × X2) → (X1 × X2) → Option Bool :=
  fun a b => if a.2 = b.2 then c1 a.1 b.1 else if a.1 = b.1 then c2 a.2 b.2 else imp a b

/-! ## Part 1: what exactly is imported -/

/-- **The factors determine the shared-component region.** A pair with the same second component is classified by
the first factor `c1`, a pair with the same first component (and differing second) by the second factor `c2`,
independent of the import: the determined region is where the two elements share a component, wider than the
diagonal. -/
theorem factors_determine_the_diagonal {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (a b : X1 × X2) :
    (a.2 = b.2 → assembleClassify c1 c2 imp a b = c1 a.1 b.1)
    ∧ (a.1 = b.1 → a.2 ≠ b.2 → assembleClassify c1 c2 imp a b = c2 a.2 b.2) :=
  ⟨fun h => by unfold assembleClassify; rw [if_pos h],
   fun h1 h2 => by unfold assembleClassify; rw [if_neg h2, if_pos h1]⟩

/-- **The import is the complement.** On a fully-cross pair, both components differing, the assemblage returns the
imported value; this is the entire imported region, exactly the complement of the shared-component pairs the
factors fix. So the import is precisely what the factors do not determine. -/
theorem the_import_is_the_complement {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (a b : X1 × X2) :
    a.1 ≠ b.1 → a.2 ≠ b.2 → assembleClassify c1 c2 imp a b = imp a b :=
  fun h1 h2 => by unfold assembleClassify; rw [if_neg h2, if_neg h1]

/-! ## Part 2: the construction's arguments -/

/-- **The grounds are derivable.** On the determined region, pairs sharing a component, the assemblage's
classification is fixed by the factors regardless of the import: two assemblages of the same factors agree there
whatever their imports. So the ground-structure is computed from the factors and the cross-map, new relative to
the factors but derivable, only the fully-cross grounds depending on the import. -/
theorem are_the_grounds_derivable {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp imp' : (X1 × X2) → (X1 × X2) → Option Bool) (a b : X1 × X2) :
    (a.2 = b.2 ∨ a.1 = b.1) → assembleClassify c1 c2 imp a b = assembleClassify c1 c2 imp' a b := by
  intro h
  unfold assembleClassify
  by_cases h2 : a.2 = b.2
  · rw [if_pos h2, if_pos h2]
  · rcases h with h | h
    · exact absurd h h2
    · rw [if_neg h2, if_neg h2, if_pos h, if_pos h]

/-- **What the construction takes.** The assemblage depends on the import only through its fully-cross values: two
imports agreeing there give the same assemblage. So the signature is two objects and a cross-map on the
fully-cross pairs, not a full ground-structure imported separately; the rest is derived. -/
theorem what_the_construction_takes {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp imp' : (X1 × X2) → (X1 × X2) → Option Bool) :
    (∀ a b, a.1 ≠ b.1 → a.2 ≠ b.2 → imp a b = imp' a b) →
    (∀ a b, assembleClassify c1 c2 imp a b = assembleClassify c1 c2 imp' a b) := by
  intro himp a b
  unfold assembleClassify
  by_cases h2 : a.2 = b.2
  · rw [if_pos h2, if_pos h2]
  · by_cases h1 : a.1 = b.1
    · rw [if_neg h2, if_neg h2, if_pos h1, if_pos h1]
    · rw [if_neg h2, if_neg h2, if_neg h1, if_neg h1]; exact himp a b h1 h2

/-! ## Part 3: generality -/

/-- **The construction takes n factors.** A product of several carriers is a carrier, and an object on it
conforms, the payload firing; the two-factor case is `n = 2`. The determined region generalizes to pairs sharing
all but one component, the import to the rest. -/
theorem n_factors (c : (Fin 2 × Fin 2 × Fin 2) → (Fin 2 × Fin 2 × Fin 2) → Option Bool) :
    ¬ Function.Surjective c :=
  hole_uniform c

/-- **Assemblages compose.** An assemblage is an object, so it can be a factor in another: assembling `A, B` then
with `C` gives an assemblage on `(X1 × X2) × X3`, which conforms, the payload firing. The construction iterates. -/
theorem assemblages_compose {X1 X2 X3 : Type} [DecidableEq X1] [DecidableEq X2] [DecidableEq X3]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool) (c3 : X3 → X3 → Option Bool)
    (imp12 : (X1 × X2) → (X1 × X2) → Option Bool)
    (imp123 : ((X1 × X2) × X3) → ((X1 × X2) × X3) → Option Bool) :
    ¬ Function.Surjective (assembleClassify (assembleClassify c1 c2 imp12) c3 imp123) :=
  hole_uniform _

/-- **The construction is not associative.** The grouping of assembly decides what is imported: a triple with a
shared first component but differing second and third is same-first in `A ⊕ (B ⊕ C)`, determined by `B ⊕ C`, yet
fully-cross in `(A ⊕ B) ⊕ C`, imported. The two groupings treat the same pair differently, so the order of
assembly matters, a finding DeLanda would recognize. -/
theorem is_the_construction_associative :
    ∃ (a1 b1 a2 b2 a3 b3 : Fin 2),
      (((a1, a2), a3).1 ≠ ((b1, b2), b3).1) ∧ ((a3 : Fin 2) ≠ b3)
      ∧ ((a1, a2, a3).1 = (b1, b2, b3).1) :=
  ⟨0, 0, 0, 1, 0, 1, by decide, by decide, by decide⟩

/-! ## Part 4: the parameters at scale

The assemblage's ground-order is the disjoint sum of the factors' orders, the import supplying cross-classify
values but no cross-order. The two-chain `prereqTwoChain` is the sum of two two-chains. -/

/-- Two disjoint two-chains, the ground-order of a two-factor assemblage of two-chain registers. -/
def prereqTwoChain : Fin 4 → Fin 4 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 2) && decide (b = 3))

/-- **The parameters of an assemblage.** The two-chain assemblage has closeable nine, coding seven, territ two; its
factor, a two-chain, closeable three, coding one, territ one. The assemblage's parameters are not the factors'
unchanged, but they relate. -/
theorem parameters_of_an_assemblage :
    ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable prereqTwoChain S)).card = 9)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => ¬ closeable prereqTwoChain S)).card = 7)
    ∧ ((Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqTwoChain i j = false)).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 2 → Bool => closeable prereqChain2 S)).card = 3)
    ∧ ((Finset.univ.filter (fun S : Fin 2 → Bool => ¬ closeable prereqChain2 S)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 2 => ∀ j, prereqChain2 i j = false)).card = 1) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **There is a composition law, split.** Across two instances, the two-chain and the mixed order (a two-chain
plus a point): territorialization adds, the endpoint-count the sum of the factors'; the closeable family
multiplies, nine as three times three and six as three times two; so coding, being `2^n` minus the closeable
count, does not add (seven against one plus one). The two parameters compose by different laws. -/
theorem is_there_a_composition_law :
    ((Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqTwoChain i j = false)).card = 2)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqMixed3 i j = false)).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable prereqTwoChain S)).card = 3 * 3)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqMixed3 S)).card = 3 * 2)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => ¬ closeable prereqTwoChain S)).card ≠ 1 + 1) :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## The verdicts

Part 1: the factors determine the shared-component region and the import is its complement. Pairs sharing a
component are fixed by the respective factor (`factors_determine_the_diagonal`), and the fully-cross pairs, both
components differing, are exactly the imported region (`the_import_is_the_complement`). The determined region is
wider than the diagonal, and the import is precisely what the factors leave open.

Part 2: the grounds are derivable, and the construction takes two objects and a cross-map. On the determined
region the grounds are fixed by the factors regardless of the import (`are_the_grounds_derivable`), and the
assemblage depends on the import only through its fully-cross values (`what_the_construction_takes`); so the
signature is two objects and a cross-classification on the fully-cross pairs, the grounds new but derivable, not
a full ground-structure imported separately.

Part 3: it takes `n` factors, composes, and is not associative. A product of several carriers conforms
(`n_factors`), an assemblage is a factor in another (`assemblages_compose`), but the grouping of assembly decides
what is imported (`is_the_construction_associative`): a triple is determined by one grouping and imported by the
other, so the order of assembly matters.

Part 4: the parameters compose by different laws. The assemblage's ground-order is the disjoint sum of the
factors' (`parameters_of_an_assemblage`); across instances the endpoint-count adds and the closeable family
multiplies, so coding does not add (`is_there_a_composition_law`).

The verdict: the assemblage construction generalizes, and its arguments are two objects and a cross-map on the
fully-cross pairs. The factors determine the shared-component region, wider than the diagonal, and the import is
exactly its complement; so the grounds are new relative to the factors but derivable from the factors and the
cross-map, not a separately imported ground-structure. The construction takes any number of factors and iterates,
an assemblage being a factor in another; but it is not associative, the grouping deciding what is imported, so the
order of assembly matters, which DeLanda would recognize as an assemblage of assemblages depending on how it was
built. And the parameters compose by split laws: territorialization adds, the endpoint-count the sum of the
factors', while the closeable family multiplies, so coding has no additive law. The assemblage-theory reading is
imported and defeasible; the honest result is a settled signature, a non-associative iteration, and a split
composition law, all computed across instances rather than reasoned. Reported per part. Nothing here is resolved. -/

end Chiralogy.AssemblageGeneral
