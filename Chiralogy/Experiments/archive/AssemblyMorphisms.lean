import Chiralogy.Model.AssemblageRelations

/-! ARCHIVED (fully graduated, across two modules). Whether the framework is already non-thin.

  Model/Moves: mask_hom_iff, mask_hom_freedom, fill_has_no_identity (spec 9.4, 9.5)
  Model/InformationOrder: minMask, minMask_realizes, minMask_least, relabel_preserves_order (spec 9.7, 9.8)

SUPERSEDED: `mask_comp` and `mask_id` are `partialization_union` and `partialization_id`, the same two theorems
with the masks exchanged, which graduated from `MoveAlgebra` under the move-algebra names.

The file's own retraction stands: the combination of masks and relabellings is FORCED, not imposed, because the
transport law holds by computation. Typechecks standalone. -/

/-! # Experiment (LIVE): is the framework already non-thin?

The classification order is a poset, so every universal property collapses to a join. This asks whether that
thinness is essential or an artifact of presentation: does the structure already present induce morphisms
between assemblies richer than the order relation?

THE DISCIPLINE. A morphism that REVEALS is one already forced by present structure. A morphism that IMPOSES is
a new primitive. This build looks only for the first kind. The only candidates that count are the ones already
here: the move operators, and the relabelling action the framework already proves its coordinates invariant
under (`absenceCarried_relabel`, `absenceCarriedCount_relabel`, canonical). Nothing else is introduced.

No registers, no physics, no privileged import. Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.AssemblyMorphisms

/-! ### GRADUATED (Model/Moves pass)

Into `Model/Moves`: `mask_hom_iff`, `mask_hom_freedom`, `fill_has_no_identity`, all under the same names.

SUPERSEDED: `mask_comp` and `mask_id` are `partialization_union` and `partialization_id`, which graduated from
`MoveAlgebra` in the same pass and keep the move-algebra names.

DEFERRED: `minMask`, `minMask_realizes` and `minMask_least` mention `cLE`, so they go with the
Model/InformationOrder group. `relabel_preserves_order` likewise.

The local copies are kept only while other live results in this file still use them. -/

/-! ### GRADUATED (Model/InformationOrder pass)

Into `Model/InformationOrder`, same names: `minMask`, `minMask_realizes`, `minMask_least`,
`relabel_preserves_order`. The canonical `minMask_realizes` proof now routes through the canonical
`mask_hom_iff` graduated in the Moves pass, not through a local copy.

Nothing from this file remains shelved. -/

/-! ## Part 1: do the move operators give more than one arrow between a fixed pair? -/

section Masks

variable {Y : Type}

/-- Mask arrows compose by union: the composite of two openings is one opening. -/
theorem mask_comp (A : Y → Y → Option Bool) (w w' : Y → Y → Bool) :
    partialization w' (partialization w A) = partialization (fun x y => w' x y || w x y) A := by
  funext x y
  cases hw : w x y <;> cases hw' : w' x y <;> simp [partialization, hw, hw']

/-- And there is an identity arrow at every object. -/
theorem mask_id (A : Y → Y → Option Bool) : partialization (fun _ _ => false) A = A := by
  funext x y; simp [partialization]

/-- **The mask hom-set, characterized cellwise.** A mask carries `A` to `B` exactly when at each cell it either
fires and `B` abstains, or does not fire and `B` agrees with `A`. -/
theorem mask_hom_iff (A B : Y → Y → Option Bool) (w : Y → Y → Bool) :
    partialization w A = B
      ↔ ∀ x y, (w x y = true ∧ B x y = none) ∨ (w x y = false ∧ B x y = A x y) := by
  constructor
  · intro h x y
    have hc : partialization w A x y = B x y := congrFun (congrFun h x) y
    cases hw : w x y
    · refine Or.inr ⟨rfl, ?_⟩
      have hv : partialization w A x y = A x y := by simp [partialization, hw]
      exact hc.symm.trans hv
    · refine Or.inl ⟨rfl, ?_⟩
      have hv : partialization w A x y = none := by simp [partialization, hw]
      exact hc.symm.trans hv
  · intro h
    funext x y
    rcases h x y with ⟨hw, hb⟩ | ⟨hw, hb⟩ <;> simp [partialization, hw, hb]

/-- **The hom-set is NOT a singleton.** Two distinct masks realize the same descent: the framework's arrows
between a fixed pair are already plural. -/
theorem mask_hom_not_thin :
    ∃ (A B : Fin 2 → Fin 2 → Option Bool) (w w' : Fin 2 → Fin 2 → Bool),
      w ≠ w' ∧ partialization w A = B ∧ partialization w' A = B := by
  refine ⟨fun x y => if x = 0 ∧ y = 0 then some true else none, botC (Fin 2),
    fun x y => decide (x = 0 ∧ y = 0), fun _ _ => true, ?_, ?_, ?_⟩
  · intro h
    exact absurd (congrFun (congrFun h 1) 1) (by decide)
  · funext x y
    by_cases hx : x = 0 ∧ y = 0 <;> simp [partialization, botC, hx]
  · funext x y; simp [partialization, botC]

/-- **But the plurality is confined to cells both ends already abstain at.** Two arrows between the same pair
differ only where `A` and `B` are both absent: the extra masks open cells that are open already. -/
theorem mask_hom_freedom (A B : Y → Y → Option Bool) (w w' : Y → Y → Bool)
    (h : partialization w A = B) (h' : partialization w' A = B) (x y : Y)
    (hne : w x y ≠ w' x y) : A x y = none ∧ B x y = none := by
  rcases (mask_hom_iff A B w).1 h x y with ⟨hw, hb⟩ | ⟨hw, hb⟩ <;>
    rcases (mask_hom_iff A B w').1 h' x y with ⟨hw', hb'⟩ | ⟨hw', hb'⟩
  · exact absurd (hw.trans hw'.symm) hne
  · exact ⟨hb'.symm.trans hb, hb⟩
  · exact ⟨hb.symm.trans hb', hb'⟩
  · exact absurd (hw.trans hw'.symm) hne

/-- The canonical arrow: open exactly the cells that change. -/
def minMask (A B : Y → Y → Option Bool) : Y → Y → Bool :=
  fun x y => decide (A x y ≠ none ∧ B x y = none)

theorem minMask_realizes (A B : Y → Y → Option Bool) (h : cLE B A) :
    partialization (minMask A B) A = B := by
  rw [mask_hom_iff]
  intro x y
  by_cases hb : B x y = none
  · by_cases ha : A x y = none
    · exact Or.inr ⟨by simp [minMask, ha], by rw [hb, ha]⟩
    · exact Or.inl ⟨by simp [minMask, ha, hb], hb⟩
  · refine Or.inr ⟨by simp [minMask, hb], ?_⟩
    rcases h x y with h1 | h1
    · exact absurd h1 hb
    · exact h1

/-- **And it is least: every arrow between the pair fires wherever the canonical one does.** So the hom-set has
a canonical representative and the plurality is removable by choosing it. -/
theorem minMask_least (A B : Y → Y → Option Bool) (w : Y → Y → Bool)
    (h : partialization w A = B) (x y : Y) (hmin : minMask A B x y = true) : w x y = true := by
  have hd : A x y ≠ none ∧ B x y = none := by simpa [minMask] using hmin
  rcases (mask_hom_iff A B w).1 h x y with ⟨hw, _⟩ | ⟨_, hb⟩
  · exact hw
  · exact absurd (hb.symm.trans hd.2) hd.1

/-- **The fill arm has no identity arrow at any object carrying an absence**, because a fill is total. So the
fills do not form a category on their own: only the mask arm does. -/
theorem fill_has_no_identity (A : Y → Y → Option Bool) (x y : Y) (h : A x y = none) (s : Y → Nat) :
    totalization s A ≠ A := by
  intro he
  have hc : totalization s A x y = A x y := congrFun (congrFun he x) y
  rw [h] at hc
  exact absurd hc (by simp [totalization])

end Masks

/-! ## Part 2: the relabelling action, and automorphisms -/


theorem relabel_id {Y : Type} (A : Y → Y → Option Bool) : relabel id A = A := rfl

theorem relabel_comp {Y : Type} (σ τ : Y → Y) (A : Y → Y → Option Bool) :
    relabel σ (relabel τ A) = relabel (τ ∘ σ) A := rfl

theorem relabel_preserves_order {Y : Type} (σ : Y → Y) (A B : Y → Y → Option Bool) (h : cLE A B) :
    cLE (relabel σ A) (relabel σ B) := fun a b => h (σ a) (σ b)

abbrev Q2 := ∀ _ : Fin 2, Fin 2

theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have h : i.val < 2 := i.isLt
  by_cases h0 : i.val = 0
  · refine Or.inl (Fin.val_injective ?_)
    show i.val = 0
    omega
  · refine Or.inr (Fin.val_injective ?_)
    show i.val = 1
    omega

theorem fin2_add_two (i : Fin 2) : i + 1 + 1 = i := by revert i; decide

/-- The coordinate swap: the concrete symmetry `ImportSpace` already used. -/
def swapP (a : Q2) : Q2 := fun i => a (i + 1)

theorem swapP_involutive (a : Q2) : swapP (swapP a) = a := by
  funext i
  show a (i + 1 + 1) = a i
  rw [fin2_add_two]

theorem swapP_injective {a b : Q2} (h : swapP a = swapP b) : a = b := by
  rw [← swapP_involutive a, ← swapP_involutive b, h]

theorem swapP_ne_id : swapP ≠ id := by
  intro h
  have hc := congrFun (congrFun h ![0, 1]) 0
  exact absurd hc (by decide)

/-- The swap exchanges the two regions: a differ-in-`i` pair swaps to a differ-in-`i+1` pair. -/
theorem swap_differ {a b : Q2} {i : Fin 2} (h : differsInOne a b i) :
    differsInOne (swapP a) (swapP b) (i + 1) := by
  have e : ∀ (c : Q2) (j : Fin 2), swapP c (j + 1) = c j := by
    intro c j
    show c (j + 1 + 1) = c j
    rw [fin2_add_two]
  refine ⟨by rw [e, e]; exact h.1, fun j hj => ?_⟩
  have hj' : j + 1 ≠ i := by
    intro hc
    apply hj
    rw [← hc, fin2_add_two]
  show a (j + 1) = b (j + 1)
  exact h.2 (j + 1) hj'

/-- And it preserves the cross region. -/
theorem swap_cross {a b : Q2} (h : ¬ ∃ i, differsInOne a b i) :
    ¬ ∃ i, differsInOne (swapP a) (swapP b) i := by
  rintro ⟨j, hj⟩
  refine h ⟨j + 1, ?_⟩
  have := swap_differ hj
  rwa [swapP_involutive, swapP_involutive] at this

def csame : ∀ _ : Fin 2, Fin 2 → Fin 2 → Option Bool := fun _ x y => if x = y then some true else none
def impSym : Q2 → Q2 → Option Bool := fun a b => if a = b then some false else none

noncomputable def Asym : Q2 → Q2 → Option Bool := nary csame impSym

/-- **A non-identity automorphism of an assembly.** With equal factors and a swap-invariant import, the
coordinate swap fixes the assembly while being a different carrier map from the identity. -/
theorem Asym_swap_invariant : relabel swapP Asym = Asym := by
  funext a b
  show nary csame impSym (swapP a) (swapP b) = nary csame impSym a b
  by_cases hex : ∃ i, differsInOne a b i
  · obtain ⟨i, hi⟩ := hex
    have hs := swap_differ hi
    rw [nary_apply_differ csame impSym hs, nary_apply_differ csame impSym hi]
    have e1 : swapP a (i + 1) = a i := by
      show a (i + 1 + 1) = a i
      rw [fin2_add_two]
    have e2 : swapP b (i + 1) = b i := by
      show b (i + 1 + 1) = b i
      rw [fin2_add_two]
    rw [e1, e2]
    rfl
  · rw [nary_apply_imp csame impSym (swap_cross hex), nary_apply_imp csame impSym hex]
    show (if swapP a = swapP b then some false else none)
      = (if a = b then some false else none)
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (by rw [hab] : swapP a = swapP b)]
    · rw [if_neg hab, if_neg (fun hc => hab (swapP_injective hc))]

/-- **So the relabelling hom-set at a single object has at least two elements.** A poset has exactly one
endo-arrow per object; this has two. The thinness is a feature of the presentation, not of the structure. -/
theorem relabel_hom_not_thin :
    ∃ (A : Q2 → Q2 → Option Bool) (σ τ : Q2 → Q2),
      σ ≠ τ ∧ relabel σ A = A ∧ relabel τ A = A :=
  ⟨Asym, id, swapP, fun h => swapP_ne_id h.symm, relabel_id Asym, Asym_swap_invariant⟩

/-- The swap is a bijection, so the automorphism lies in the groupoid part of the relabelling action, not
merely in its monoid part. -/
theorem swap_is_invertible : ∀ a : Q2, swapP (swapP a) = a := swapP_involutive

/-! ## THE VERDICTS

PART 1: the moves give more than one arrow, and the mask arm gives a category.

`mask_comp` and `mask_id` make the mask arrows a category on classifications: composition is union of masks,
the identity is the all-false mask. `mask_hom_not_thin` shows a hom-set with two distinct elements, so the
category is NOT thin.

But the plurality is bookkeeping. `mask_hom_freedom` confines it exactly: two arrows between a fixed pair
differ only at cells where BOTH ends abstain, that is the extra masks open cells that are open already.
`minMask_realizes` and `minMask_least` give the hom-set a least element, the mask that opens exactly the cells
that change. So the non-thinness of the mask category is canonically REMOVABLE: choose the least arrow and the
category collapses to the order, which is `below_iff_partialization` read categorically.

The fill arm does not even reach that far. `fill_has_no_identity` shows there is no identity fill at any object
carrying an absence, since a fill is total. The fills do not form a category on their own. This is the same
arms-asymmetry the move algebra found, in categorical dress: open has an identity and composes; fill absorbs.

PART 2: the relabelling action gives automorphisms, and those are NOT removable.

`relabel_id`, `relabel_comp` and `relabel_preserves_order` make relabelling a categorical action preserving the
order. `Asym_swap_invariant` exhibits an assembly fixed by the coordinate swap, and `swapP_ne_id` shows the
swap is a different carrier map from the identity. So `relabel_hom_not_thin` gives two distinct arrows from an
object to ITSELF.

That is the load-bearing point. A poset has exactly one endo-arrow per object. An object with a non-identity
automorphism cannot be presented faithfully in a poset, and no choice of representative removes it: unlike the
mask plurality there is no least automorphism to select, because automorphisms form a group and the group is
not trivial here. `swap_is_invertible` places it in the groupoid part.

PART 3: SECRETLY NON-THIN, and forced by present structure.

The framework is already non-thin, in two independent ways, and they are not equally significant.

  The mask category is non-thin but canonically thinnable. Its extra arrows are do-nothing variations and its
  thin quotient is exactly the classification order. Nothing is lost by the poset presentation here.

  The relabelling groupoid is non-thin irreducibly. Objects with symmetry have non-trivial automorphism
  groups, and the poset presentation discards them. This is genuine structure the order cannot express.

FORCED, not imposed. Every ingredient is already present: `partialization_union` and `partialization_id` are
canonical and give the mask category; the relabelling action is canonical, the framework already proving its
coordinates invariant under it (`absenceCarried_relabel`, `absenceCarriedCount_relabel`); and the swap is the
symmetry `ImportSpace` already used. No new primitive was introduced and none is needed for either statement.

CONSEQUENCE FOR THE COPRODUCT RESULT, stated carefully. That result is a theorem about the poset and remains
true as such. But it is not the last word on universal properties, because it was computed in a presentation
that discards automorphisms. A universal property in the relabelling groupoid could differ, and the coproduct
computation says nothing about it.

WHAT REMAINS OPEN, and where imposition would begin

1. The mask category and the relabelling groupoid are two separate arrow classes on the same objects.
   COMBINING them into one category is a construction, not a derivation: the composite of a relabelling and a
   mask is not given by present structure. Building it would impose. Not done here.
2. Automorphism groups are computed at one object. Which assemblies have non-trivial symmetry, and how the
   group varies with the factors and the import, is not measured.
3. Whether the relabelling groupoid has colimits at all, and whether the coproduct of `AssemblyUniversal`
   survives in it, is untested. That is the natural next question and it needs the combined category from
   item 1, so it is currently blocked behind an imposition.
4. Nothing here is graduated. The results are categorical readings of canonical facts, and their value is the
   verdict on presentation, not new content. -/

#print axioms mask_comp
#print axioms mask_id
#print axioms mask_hom_iff
#print axioms mask_hom_not_thin
#print axioms mask_hom_freedom
#print axioms minMask_realizes
#print axioms minMask_least
#print axioms fill_has_no_identity
#print axioms relabel_id
#print axioms relabel_comp
#print axioms relabel_preserves_order
#print axioms fin2_cases
#print axioms fin2_add_two
#print axioms swapP_involutive
#print axioms swapP_injective
#print axioms swapP_ne_id
#print axioms swap_differ
#print axioms swap_cross
#print axioms Asym_swap_invariant
#print axioms relabel_hom_not_thin
#print axioms swap_is_invertible

end Chiralogy.AssemblyMorphisms
