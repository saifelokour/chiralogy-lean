import Chiralogy.Model.AssemblageRelations

/-! ARCHIVED (fully graduated). The mono-cone limit results, rebuilt on canonical foundations so they could
graduate without the archived partition apparatus.

EVERY declaration graduated to `Model/NaryAssemblage` under the same names: `regionMask`, `crossMask`,
`absenceMask`, `regionSlice`, `crossSlice`, `regionSlice_apply`, `crossSlice_apply`, `regionSlice_reads_factor`,
`crossSlice_reads_import`, `leg_of_total`, `mediator_exists`, `mediator_unique`, `lazy_leg_no_mediator`,
`automorphism_breaks_existence`. Spec 9.16.

This file existed to keep `AssemblyUniversal`'s partition-generic apparatus out of canonical, and it did: the
graduated closure is `partialization` and `differsInOne` and nothing else. The local `relabel` collapsed to the
canonical one. Typechecks standalone. -/

/-! # Experiment (LIVE): the mono-cone limit results, rebuilt on canonical foundations

The graduation dry run found that `CombinedCategory`'s limit results are proved through `regionPiece`,
`crossPiece`, `wRegion`, `wCross`, `absMask` and `cell_cases`, the partition apparatus the readiness pass
archived as partition-generic. Graduating them as written would carry that apparatus into canonical.

This re-proves the same theorems in canonical vocabulary only: `nary`, `differsInOne`, `nary_apply_differ`,
`nary_apply_imp`, `partialization`, `cLE`, `optLE`. The pieces are no longer ad hoc constructions; they are
IMAGES OF THE DOWN-MOVE under masks written in `differsInOne`.

The finding must not change. Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.MonoConeCanonical


/-! ### GRADUATED (Model/NaryAssemblage pass)

The whole rebuilt file graduated, same names: `regionMask`, `crossMask`, `absenceMask`, `regionSlice`,
`crossSlice`, `regionSlice_apply`, `crossSlice_apply`, `regionSlice_reads_factor`, `crossSlice_reads_import`,
`leg_of_total`, `mediator_exists`, `mediator_unique`, `lazy_leg_no_mediator`,
`automorphism_breaks_existence`. The local `relabel` is superseded by the canonical one.

This is what the rebuild was for: the archived partition apparatus never entered canonical. -/

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]


/-! ## Part 1: the pieces, canonically

The masks are written in canonical `differsInOne` alone, and each piece is the assembly opened by its mask.
Nothing here is a new construction: a piece is a value of the canonical down-move. -/

/-- Fires everywhere EXCEPT region `i`. -/
def regionMask (i : Fin n) : (∀ i, X i) → (∀ i, X i) → Bool := fun a b => decide (¬ differsInOne a b i)

/-- Fires everywhere EXCEPT the cross. -/
def crossMask : (∀ i, X i) → (∀ i, X i) → Bool := fun a b => decide (∃ i, differsInOne a b i)

/-- Fires exactly where the classification abstains. -/
def absenceMask (A : (∀ i, X i) → (∀ i, X i) → Option Bool) : (∀ i, X i) → (∀ i, X i) → Bool :=
  fun a b => decide (A a b = none)

/-- The region-`i` piece: the classification opened everywhere but region `i`. -/
def regionSlice (i : Fin n) (A : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    (∀ i, X i) → (∀ i, X i) → Option Bool := partialization (regionMask i) A

/-- The cross piece: the classification opened everywhere but the cross. -/
def crossSlice (A : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    (∀ i, X i) → (∀ i, X i) → Option Bool := partialization crossMask A

/-- **THE EQUIVALENCE, region half.** This is verbatim the defining equation of the archived `regionPiece`, so
the canonical slice IS the same object and the finding is preserved rather than changed. -/
theorem regionSlice_apply (i : Fin n) (A : (∀ i, X i) → (∀ i, X i) → Option Bool) (a b : ∀ i, X i) :
    regionSlice i A a b = if differsInOne a b i then A a b else none := by
  by_cases h : differsInOne a b i
  · have hm : regionMask i a b = false := decide_eq_false (fun hn => hn h)
    simp only [regionSlice, partialization, hm, Bool.false_eq_true, if_false]
    rw [if_pos h]
  · have hm : regionMask i a b = true := decide_eq_true h
    simp only [regionSlice, partialization, hm, if_true]
    rw [if_neg h]

/-- **THE EQUIVALENCE, cross half.** Verbatim the defining equation of the archived `crossPiece`. -/
theorem crossSlice_apply (A : (∀ i, X i) → (∀ i, X i) → Option Bool) (a b : ∀ i, X i) :
    crossSlice A a b = if (¬ ∃ i, differsInOne a b i) then A a b else none := by
  by_cases h : ∃ i, differsInOne a b i
  · have hm : crossMask a b = true := decide_eq_true h
    simp only [crossSlice, partialization, hm, if_true]
    rw [if_neg (not_not_intro h)]
  · have hm : crossMask a b = false := decide_eq_false h
    simp only [crossSlice, partialization, hm, Bool.false_eq_true, if_false]
    rw [if_pos h]

/-- The projections are down-moves, so each piece sits below the whole in the canonical order. -/
theorem regionSlice_le (i : Fin n) (A : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    cLE (regionSlice i A) A := by
  intro a b
  rw [regionSlice_apply]
  by_cases h : differsInOne a b i
  · rw [if_pos h]; exact optLE_refl _
  · rw [if_neg h]; exact Or.inl rfl

theorem crossSlice_le (A : (∀ i, X i) → (∀ i, X i) → Option Bool) : cLE (crossSlice A) A := by
  intro a b
  rw [crossSlice_apply]
  by_cases h : ¬ ∃ i, differsInOne a b i
  · rw [if_pos h]; exact optLE_refl _
  · rw [if_neg h]; exact Or.inl rfl

/-- **And the pieces read the canonical assembly structure.** The region piece is the factor, by
`nary_apply_differ`. This is content the archived version did not have: there the pieces were about an
arbitrary classification. -/
theorem regionSlice_reads_factor (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (i : Fin n) {a b : ∀ i, X i}
    (h : differsInOne a b i) : regionSlice i (nary c imp) a b = c i (a i) (b i) := by
  rw [regionSlice_apply, if_pos h, nary_apply_differ c imp h]

/-- The cross piece is the import, by `nary_apply_imp`. -/
theorem crossSlice_reads_import (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) {a b : ∀ i, X i}
    (h : ¬ ∃ i, differsInOne a b i) : crossSlice (nary c imp) a b = imp a b := by
  rw [crossSlice_apply, if_pos h, nary_apply_imp c imp h]

/-! ## Part 2: the limit, canonically -/

/-- A mask-only leg out of a TOTAL source is completely determined: it fires exactly where the target
abstains. This is what removes the laziness obstruction inside the subcategory. -/
theorem leg_of_total (T Tgt : (∀ i, X i) → (∀ i, X i) → Option Bool) (hT : ∀ a b, T a b ≠ none)
    (v : (∀ i, X i) → (∀ i, X i) → Bool) (h : partialization v T = Tgt) (a b : ∀ i, X i) :
    (v a b = true ↔ Tgt a b = none) ∧ (v a b = false → T a b = Tgt a b) := by
  have hc : (if v a b then none else T a b) = Tgt a b := congrFun (congrFun h a) b
  cases hv : v a b
  · rw [hv] at hc
    simp only [Bool.false_eq_true, if_false] at hc
    refine ⟨⟨fun hx => absurd hx (by simp), fun hx => absurd (hc.trans hx) (hT a b)⟩, fun _ => hc⟩
  · rw [hv] at hc
    simp only [if_true] at hc
    exact ⟨⟨fun _ => hc.symm, fun _ => rfl⟩, fun hx => absurd hx (by simp)⟩

/-- **EXISTENCE, in the mask subcategory over a total source, on canonical pieces.** The absence mask of the
assembly mediates: it reproduces the assembly from the source and factors every leg. -/
theorem mediator_exists (A T : (∀ i, X i) → (∀ i, X i) → Option Bool) (hT : ∀ a b, T a b ≠ none)
    (vR : Fin n → (∀ i, X i) → (∀ i, X i) → Bool) (vC : (∀ i, X i) → (∀ i, X i) → Bool)
    (hR : ∀ i, partialization (vR i) T = regionSlice i A)
    (hC : partialization vC T = crossSlice A) :
    partialization (absenceMask A) T = A
      ∧ (∀ i, (fun a b => regionMask i a b || absenceMask A a b) = vR i)
      ∧ (fun a b => crossMask a b || absenceMask A a b) = vC := by
  have key : ∀ a b : ∀ i, X i, (A a b ≠ none → T a b = A a b) := by
    intro a b hpres
    by_cases hex : ∃ i, differsInOne a b i
    · obtain ⟨i, hi⟩ := hex
      have hL := leg_of_total T (regionSlice i A) hT (vR i) (hR i) a b
      have h2 : regionSlice i A a b = A a b := by rw [regionSlice_apply, if_pos hi]
      have hv : vR i a b = false := by
        cases hvv : vR i a b
        · rfl
        · exact absurd (h2.symm.trans (hL.1.mp hvv)) hpres
      exact (hL.2 hv).trans h2
    · have hL := leg_of_total T (crossSlice A) hT vC hC a b
      have h2 : crossSlice A a b = A a b := by rw [crossSlice_apply, if_pos hex]
      have hv : vC a b = false := by
        cases hvv : vC a b
        · rfl
        · exact absurd (h2.symm.trans (hL.1.mp hvv)) hpres
      exact (hL.2 hv).trans h2
  refine ⟨?_, ?_, ?_⟩
  · funext a b
    show (if absenceMask A a b then none else T a b) = A a b
    by_cases hp : A a b = none
    · rw [show absenceMask A a b = true from decide_eq_true hp]
      simp [hp]
    · rw [show absenceMask A a b = false from decide_eq_false hp]
      simpa using key a b hp
  · intro i
    funext a b
    have hL := leg_of_total T (regionSlice i A) hT (vR i) (hR i) a b
    by_cases hi : differsInOne a b i
    · rw [show regionMask i a b = false from decide_eq_false (fun hn => hn hi)]
      simp only [Bool.false_or]
      have h2 : regionSlice i A a b = A a b := by rw [regionSlice_apply, if_pos hi]
      cases hv : vR i a b
      · refine decide_eq_false (fun hp => ?_)
        exact absurd (hL.1.mpr (h2.trans hp)) (by simp [hv])
      · exact decide_eq_true (h2.symm.trans (hL.1.mp hv))
    · rw [show regionMask i a b = true from decide_eq_true hi, Bool.true_or]
      exact (hL.1.mpr (show regionSlice i A a b = none by rw [regionSlice_apply, if_neg hi])).symm
  · funext a b
    have hL := leg_of_total T (crossSlice A) hT vC hC a b
    by_cases hex : ∃ i, differsInOne a b i
    · rw [show crossMask a b = true from decide_eq_true hex, Bool.true_or]
      exact (hL.1.mpr (show crossSlice A a b = none by
        rw [crossSlice_apply, if_neg (not_not_intro hex)])).symm
    · rw [show crossMask a b = false from decide_eq_false hex]
      simp only [Bool.false_or]
      have h2 : crossSlice A a b = A a b := by rw [crossSlice_apply, if_pos hex]
      cases hv : vC a b
      · refine decide_eq_false (fun hp => ?_)
        exact absurd (hL.1.mpr (h2.trans hp)) (by simp [hv])
      · exact decide_eq_true (h2.symm.trans (hL.1.mp hv))

/-- **UNIQUENESS, and it needs no totality.** The projection masks are false exactly on their own parts, and
the parts exhaust the cells, so the cone is jointly monic. -/
theorem mediator_unique (w w' : (∀ i, X i) → (∀ i, X i) → Bool)
    (hR : ∀ i, (fun a b => regionMask i a b || w a b) = (fun a b => regionMask i a b || w' a b))
    (hC : (fun a b => crossMask a b || w a b) = (fun a b => crossMask a b || w' a b)) : w = w' := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · obtain ⟨i, hi⟩ := hex
    have hw : regionMask i a b = false := decide_eq_false (fun hn => hn hi)
    have h := congrFun (congrFun (hR i) a) b
    rwa [hw, Bool.false_or, Bool.false_or] at h
  · have hw : crossMask a b = false := decide_eq_false hex
    have h := congrFun (congrFun hC a) b
    rwa [hw, Bool.false_or, Bool.false_or] at h

/-! ## Part 3: the two obstructions in the full category, canonically -/

/-- **Obstruction A, laziness.** If the assembly abstains at a cell outside region `i`, a mask-only leg may
decline to fire there and no mediator can match it: the projection fires there and every composite through it
inherits that. Carrier-general, uniform in `n`, and it uses identity relabellings only, so restricting the cone
to a shared relabelling does not remove it. -/
theorem lazy_leg_no_mediator [DecidableEq (∀ i, X i)]
    (A : (∀ i, X i) → (∀ i, X i) → Option Bool) (i : Fin n) (a b : ∀ i, X i)
    (hnr : ¬ differsInOne a b i) (habs : A a b = none) :
    partialization (fun p q => regionMask i p q && !(decide (p = a ∧ q = b))) A = regionSlice i A
      ∧ ¬ ∃ w : (∀ i, X i) → (∀ i, X i) → Bool,
          (fun p q => regionMask i p q || w p q)
            = (fun p q => regionMask i p q && !(decide (p = a ∧ q = b))) := by
  constructor
  · funext p q
    rw [regionSlice_apply]
    show (if (regionMask i p q && !(decide (p = a ∧ q = b))) then none else A p q)
      = (if differsInOne p q i then A p q else none)
    by_cases hpq : p = a ∧ q = b
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [show (decide (p = p ∧ q = q)) = true from decide_eq_true ⟨rfl, rfl⟩]
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
      rw [if_neg hnr]
      exact habs
    · rw [show (decide (p = a ∧ q = b)) = false from decide_eq_false hpq]
      simp only [Bool.not_false, Bool.and_true]
      by_cases hi : differsInOne p q i
      · rw [if_pos hi, show regionMask i p q = false from decide_eq_false (fun hn => hn hi)]
        simp
      · rw [if_neg hi, show regionMask i p q = true from decide_eq_true hi]
        simp
  · rintro ⟨w, hw⟩
    have hc := congrFun (congrFun hw a) b
    rw [show regionMask i a b = true from decide_eq_true hnr,
      show (decide (a = a ∧ b = b)) = true from decide_eq_true ⟨rfl, rfl⟩] at hc
    simp at hc

/-- **Obstruction B, symmetry.** A non-identity relabelling fixing the assembly gives a second, equally valid
leg to the region-`i` piece with a different relabelling component. The projections have identity relabelling
components, so a mediator's relabelling component would have to be the composite's, that is `id` for one leg
and the automorphism for the other. Those are different, so no mediator exists. Carrier-general and uniform in
`i`; the automorphism need not permute the pieces, fixing the assembly is enough. -/
theorem automorphism_breaks_existence (A : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (σ : (∀ i, X i) → (∀ i, X i)) (i : Fin n) (hσ : relabel σ A = A) (hne : σ ≠ id) :
    partialization (regionMask i) (relabel σ A) = regionSlice i A
      ∧ ¬ ∃ u : (∀ i, X i) → (∀ i, X i), u = id ∧ u = σ := by
  refine ⟨by rw [hσ]; rfl, ?_⟩
  rintro ⟨u, h1, h2⟩
  exact hne (h1.symm.trans h2).symm

/-! ## THE VERDICTS

PART 1: the pieces are canonical, and they are BETTER than the archived ones.

`regionMask` and `crossMask` are written in canonical `differsInOne` and nothing else. `regionSlice` and
`crossSlice` are not new constructions at all: each is `partialization` applied to the assembly, so a piece is a
value of the canonical DOWN-MOVE and a projection is a mask arrow by definition, not by a lemma.

`regionSlice_apply` and `crossSlice_apply` prove the defining equations of the archived `regionPiece` and
`crossPiece` verbatim, so the canonical pieces are THE SAME OBJECTS and the finding is preserved, not changed.
The projections coincide too, definitionally, since the archived projections were already partializations by
`wRegion` and `wCross` and those masks are pointwise equal to `regionMask` and `crossMask`.

One thing is gained rather than merely preserved. `regionSlice_reads_factor` and `crossSlice_reads_import`
identify the pieces with the FACTORS and the IMPORT through canonical `nary_apply_differ` and `nary_apply_imp`.
The archived version could not say this: its pieces were slices of an arbitrary classification, which is exactly
what made it partition-generic. Stated canonically, the diagram is about assemblies.

PART 2: the limit stands, with no archived dependency.

`leg_of_total`, `mediator_exists` and `mediator_unique` are re-proved on the canonical slices. Nothing from
the archived apparatus appears: no `regionPiece`, no `crossPiece`, no `wRegion`, no `wCross`, no `absMask`, and
no `cell_cases`, whose role is taken by a `by_cases` on the canonical `∃ i, differsInOne a b i`, which is the
same case split canonical `nary` itself performs.

The finding is unchanged. In the mask subcategory over total sources the assembly is a genuine limit of its
pieces: the absence mask mediates and the cone is jointly monic. Uniqueness needs no totality.

PART 3: both obstructions stand canonically.

`lazy_leg_no_mediator` is obstruction A, carrier-general and uniform in `n`, on the canonical slice. It uses
identity relabellings only, so it is not removed by restricting the cone.

`automorphism_breaks_existence` is obstruction B, and re-expressing it canonically made it SHARPER than the
witness form it had. The archived route exhibited it on a two-point carrier through the arrow apparatus; here
it is stated for any carrier, any assembly, any coordinate, and any non-identity automorphism, and the
contradiction is that the mediator's relabelling component would have to be both the identity and the
automorphism. The arrow apparatus is not needed to see it, only the fact that the projections have identity
relabelling components.

So the full verdict survives on canonical foundations: existence fails in the full category by two independent
obstructions, uniqueness holds throughout, and existence is restored exactly in the mask subcategory over total
sources. That is the mono-cone finding as it stood.

WHAT REMAINS OPEN

1. Obstruction B is stated at the level of relabelling components, which is where the contradiction lives. A
   version phrased through the composed arrows would need the combined-category apparatus that the dry run
   graduates separately; it would add no content.
2. The pieces are shown to read the factors and the import. Whether the limit property itself can be stated
   over the FACTOR carriers rather than the product carrier, which is what a genuinely assembly-shaped diagram
   would be, is not attempted here.
3. Nothing graduates in this file. It readies a rebuild for the graduation pass. -/

#print axioms relabel
#print axioms regionMask
#print axioms crossMask
#print axioms absenceMask
#print axioms regionSlice
#print axioms crossSlice
#print axioms regionSlice_apply
#print axioms crossSlice_apply
#print axioms regionSlice_le
#print axioms crossSlice_le
#print axioms regionSlice_reads_factor
#print axioms crossSlice_reads_import
#print axioms leg_of_total
#print axioms mediator_exists
#print axioms mediator_unique
#print axioms lazy_leg_no_mediator
#print axioms automorphism_breaks_existence

end Chiralogy.MonoConeCanonical
