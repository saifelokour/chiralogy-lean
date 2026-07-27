import Chiralogy.Model.AssemblageRelations

/-! ARCHIVED (fully graduated). Whether quantizing the import is a category error under the moves.

GRADUATED to `Model/NaryAssemblage`, same names: `composite_fill_writes_cross`,
`composite_fill_overwrites_absent_cross`, `composite_fill_not_a_factor_operation` (spec 9.13).

The finding stands: a fill on a composite is not a factor operation, so the import is not the kind of object the
fill acts on coordinatewise. Typechecks standalone. -/

/-! # Experiment (LIVE): what kind of object is the import, relative to the fill?

The reading to test: gravity-as-import is not a factor but the free relational content between two non-reducing
factors, and quantization acts on FACTORS, so the import may be exactly what no factor-fill reaches. Is
"quantize the import" a category error, applying a factor-operation to something that is not its kind of
target?

The build decides between two diagnoses. CATEGORY ERROR: the import is unreachable in principle by the moves,
living in a different space under a different order. SUPPLY-GAP: the import is reachable by a legitimate move
and merely unfixed, the ordinary parameter silence. These are different claims and the measurement separates
them.

Sibling of `ImportSpace` (the free region's internal order) and `PhysicsImport` (the import is unconstrained).
Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.ImportUnderMoves


/-! ### GRADUATED (Model/NaryAssemblage pass)

Into `Model/NaryAssemblage`, same names: `composite_fill_writes_cross`,
`composite_fill_overwrites_absent_cross`, `composite_fill_not_a_factor_operation`. The rest stays live. -/

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- A cell of the cross region. -/
def IsCross (a b : ∀ i, X i) : Prop := ¬ ∃ i, differsInOne a b i

theorem diagAt (a : ∀ i, X i) : IsCross a a := by
  rintro ⟨i, hne, _⟩; exact hne rfl

/-! ## Part 1: does a fill on a factor ever reach the import? -/

/-- **No change of factors reaches the cross region.** The cross cells of an assemblage are a function of the
import alone, invariant under replacing every factor by anything at all. Carrier-general, uniform in `n`. -/
theorem factor_change_fixes_cross (c c' : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) {a b : ∀ i, X i} (h : IsCross a b) :
    nary c imp a b = nary c' imp a b := by
  rw [nary_apply_imp c imp h, nary_apply_imp c' imp h]

/-- **In particular, quantizing every factor leaves the import untouched.** Filling each factor by its own
scale changes nothing in the cross region: the relational content between the factors is exactly what
factor-fills do not reach. -/
theorem factor_fill_fixes_cross (c : ∀ i, X i → X i → Option Bool) (si : ∀ i, X i → Nat)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) {a b : ∀ i, X i} (h : IsCross a b) :
    nary (fun i => totalization (si i) (c i)) imp a b = nary c imp a b :=
  factor_change_fixes_cross _ c imp h

/-- **The composite fill DOES write the cross region.** Filling the whole assemblage by one scale supplies a
verdict at every cross cell, the import's own value where it had one and the scale's verdict where it did
not. -/
theorem composite_fill_writes_cross (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (s : (∀ i, X i) → Nat)
    {a b : ∀ i, X i} (h : IsCross a b) :
    totalization s (nary c imp) a b = some ((imp a b).getD (decide (s b ≤ s a))) := by
  simp only [totalization, nary_apply_imp c imp h]

/-- Sharply: where the import abstained, the composite fill writes a verdict the import never carried. -/
theorem composite_fill_overwrites_absent_cross (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (s : (∀ i, X i) → Nat)
    {a b : ∀ i, X i} (h : IsCross a b) (habs : imp a b = none) :
    totalization s (nary c imp) a b = some (decide (s b ≤ s a)) := by
  rw [composite_fill_writes_cross c imp s h, habs, Option.getD_none]

/-- **So the two are genuinely different operations.** If the import abstains anywhere on the cross region, the
composite fill is not equal to ANY assemblage over that same import, whatever factors are used. A composite fill
cannot be presented as a factor operation. -/
theorem composite_fill_not_a_factor_operation (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (s : (∀ i, X i) → Nat)
    {a b : ∀ i, X i} (hcross : IsCross a b) (habs : imp a b = none)
    (c' : ∀ i, X i → X i → Option Bool) :
    totalization s (nary c imp) ≠ nary c' imp := by
  intro h
  have hc := congrFun (congrFun h a) b
  rw [composite_fill_overwrites_absent_cross c imp s hcross habs,
    nary_apply_imp c' imp hcross, habs] at hc
  exact absurd hc (Option.some_ne_none _)

open Finset in
/-- **And the composite fill does not decompose into factor fills.** The canonical commutation writes it as an
assemblage of the filled factors over the FILLED IMPORT, not over the original one: the import is a third thing
the joint move acts on, alongside the factors. -/
theorem composite_fill_totalizes_the_import (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    totalization (fun a => ∑ j, si j (a j)) (nary c imp)
      = nary (fun i => totalization (si i) (c i)) (totalization (fun a => ∑ j, si j (a j)) imp) :=
  nary_totalization_commutes_sum si c imp

/-! ## Part 2: what operation acts on the import? -/

/-- **Every move's action on the cross region is the SAME move on the import.** The fill arm. -/
theorem fill_on_cross_is_fill_on_import (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (s : (∀ i, X i) → Nat)
    {a b : ∀ i, X i} (h : IsCross a b) :
    totalization s (nary c imp) a b = totalization s imp a b := by
  simp only [totalization, nary_apply_imp c imp h]

/-- The mask arm, likewise. So no move on a fixed composite has a cross-action that escapes the import: every
such action is an import re-selection, to the moved import. -/
theorem mask_on_cross_is_mask_on_import (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (w : (∀ i, X i) → (∀ i, X i) → Bool)
    {a b : ∀ i, X i} (h : IsCross a b) :
    partialization w (nary c imp) a b = partialization w imp a b := by
  simp only [partialization, nary_apply_imp c imp h]

/-! ### Re-selection is not a move, and that is true of factors too -/

theorem fill_cannot_reach {Y : Type} (A B : Y → Y → Option Bool) (h : ¬ cLE A B) (s : Y → Nat) :
    totalization s A ≠ B := by
  intro he
  exact h (he ▸ c_le_totalization s A)

theorem mask_cannot_reach {Y : Type} (A B : Y → Y → Option Bool) (h : ¬ cLE B A)
    (w : Y → Y → Bool) : partialization w A ≠ B := by
  intro he
  exact h (he ▸ partialization_le_c w A)

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

theorem differ0 {a b : Q2} (h0 : a 0 ≠ b 0) (h1 : a 1 = b 1) : differsInOne a b 0 := by
  refine ⟨h0, fun j hj => ?_⟩
  rcases fin2_cases j with h | h
  · exact absurd h hj
  · subst h; exact h1

/-- Two imports disagreeing at one cross cell, with opposite verdicts. -/
def impT : Q2 → Q2 → Option Bool := fun _ _ => some true
def impF : Q2 → Q2 → Option Bool :=
  fun a b => if a = ![0, 0] ∧ b = ![0, 0] then some false else some true

/-- The two composites are INCOMPARABLE: neither sits below the other. -/
theorem imports_incomparable (c : ∀ _ : Fin 2, Fin 2 → Fin 2 → Option Bool) :
    ¬ cLE (nary c impT) (nary c impF) ∧ ¬ cLE (nary c impF) (nary c impT) := by
  have hd : IsCross (![0, 0] : Q2) ![0, 0] := diagAt _
  have hT : nary c impT ![0, 0] ![0, 0] = some true := by
    rw [nary_apply_imp c impT hd]; rfl
  have hF : nary c impF ![0, 0] ![0, 0] = some false := by
    rw [nary_apply_imp c impF hd]; decide
  constructor
  · intro h
    rcases h ![0, 0] ![0, 0] with h1 | h1
    · rw [hT] at h1; exact absurd h1 (by decide)
    · rw [hT, hF] at h1; exact absurd h1 (by decide)
  · intro h
    rcases h ![0, 0] ![0, 0] with h1 | h1
    · rw [hF] at h1; exact absurd h1 (by decide)
    · rw [hT, hF] at h1; exact absurd h1 (by decide)

/-- **Import re-selection is not a move.** No fill and no mask carries one of these composites to the other:
the two sit sideways to each other in the order, and the moves only go up or down. -/
theorem import_reselection_beyond_moves (c : ∀ _ : Fin 2, Fin 2 → Fin 2 → Option Bool) :
    (∀ s : Q2 → Nat, totalization s (nary c impT) ≠ nary c impF)
      ∧ ∀ w : Q2 → Q2 → Bool, partialization w (nary c impT) ≠ nary c impF :=
  ⟨fun s => fill_cannot_reach _ _ (imports_incomparable c).1 s,
   fun w => mask_cannot_reach _ _ (imports_incomparable c).2 w⟩

def cAllT : ∀ _ : Fin 2, Fin 2 → Fin 2 → Option Bool := fun _ _ _ => some true
def cAllF : ∀ _ : Fin 2, Fin 2 → Fin 2 → Option Bool := fun _ _ _ => some false

/-- **And re-selection is not a move for FACTORS either.** Two factor families with opposite verdicts give
incomparable composites, so the same lateral unreachability holds on the determined side. The import is not
special in this respect: nothing about it lives in a different space. -/
theorem factor_reselection_beyond_moves (imp : Q2 → Q2 → Option Bool) :
    (∀ s : Q2 → Nat, totalization s (nary cAllT imp) ≠ nary cAllF imp)
      ∧ ∀ w : Q2 → Q2 → Bool, partialization w (nary cAllT imp) ≠ nary cAllF imp := by
  have hd : differsInOne (![0, 0] : Q2) ![1, 0] 0 := differ0 (by decide) (by decide)
  have hT : nary cAllT imp ![0, 0] ![1, 0] = some true := by
    rw [nary_apply_differ cAllT imp hd]; rfl
  have hF : nary cAllF imp ![0, 0] ![1, 0] = some false := by
    rw [nary_apply_differ cAllF imp hd]; rfl
  have hnotle : ¬ cLE (nary cAllT imp) (nary cAllF imp) := by
    intro h
    rcases h ![0, 0] ![1, 0] with h1 | h1
    · rw [hT] at h1; exact absurd h1 (by decide)
    · rw [hT, hF] at h1; exact absurd h1 (by decide)
  have hnotge : ¬ cLE (nary cAllF imp) (nary cAllT imp) := by
    intro h
    rcases h ![0, 0] ![1, 0] with h1 | h1
    · rw [hF] at h1; exact absurd h1 (by decide)
    · rw [hT, hF] at h1; exact absurd h1 (by decide)
  exact ⟨fun s => fill_cannot_reach _ _ hnotle s, fun w => mask_cannot_reach _ _ hnotge w⟩

/-! ## THE VERDICTS

PART 1: factor-fills never reach the import; composite-fills overwrite it; they are different operations.

`factor_change_fixes_cross` is the strongest form of the first half: the cross cells are a function of the
import ALONE, invariant under replacing every factor by anything whatever. Filling the factors is a special
case (`factor_fill_fixes_cross`). So quantizing a component provably does not touch the relational content
between components. Carrier-general, uniform in `n`, no hypotheses.

`composite_fill_writes_cross` and `composite_fill_overwrites_absent_cross` are the second half: a fill of the
whole assemblage supplies a verdict at every cross cell, including a verdict the import never carried wherever
the import abstained.

`composite_fill_not_a_factor_operation` separates them decisively: if the import abstains anywhere on the
cross, the composite fill equals NO assemblage over that same import, for any factors at all. And
`composite_fill_totalizes_the_import` says why, in canonical terms: the joint move writes the filled factors
over the FILLED IMPORT. The import is a third thing the joint move acts on, not a by-product of acting on the
factors. So the two operations do not decompose into one another.

PART 2: what acts on the import is the composite move, and its cross-action is exactly that move on the import.

`fill_on_cross_is_fill_on_import` and `mask_on_cross_is_mask_on_import`: every move on a fixed composite has a
cross-action identical to the same move applied to the import alone. So no move's cross-action escapes the
import; each is an import re-selection, to the moved import.

Re-selection to an arbitrary other import is NOT a move (`import_reselection_beyond_moves`): two imports with
opposite verdicts at one cross cell give incomparable composites, and the moves only ascend or descend. But
`factor_reselection_beyond_moves` shows the same is true of factors. The import is NOT special in this respect,
and this is the load-bearing negative: there is no sense in which the import inhabits a different space from
the factors under the moves. Both are cells of one classification in one order.

PART 3: SUPPLY-GAP, not category error. With one real residue.

The category-error diagnosis requires the import to be unreachable in principle. It is not: the composite fill
reaches it, is a legitimate move, and acts on it exactly as the move acts on any classification. The import and
the factors sit in the same order, and neither is reachable laterally. So the strong reading is REFUTED.

What survives is precise and worth stating in its own right. The operation "quantize a factor" provably never
reaches the import, at any carrier, for any factors, with no hypotheses. So if quantization is taken to be a
component operation, it misses the relational content entirely, and the miss is structural rather than
contingent. The thing that reaches the import is the fill of the WHOLE, a different operation which does not
decompose into component fills, and whose scale nothing fixes. That last clause is the ordinary supply-gap,
already located.

So the honest diagnosis is: the import is not unreachable-in-principle, it is unreachable-by-factor-operations
and otherwise merely unfixed. The reading was half right, and the half that survives is the sharper half.

FILTER: register-neutral throughout. Every theorem quantifies over the factors and the import; no register
content, no phi, no physics enters any statement or any proof. The result is about assemblages, not about
gravity.

WHAT REMAINS OPEN

1. The lateral witnesses use opposite verdicts at one cell. Whether every pair of distinct imports is
   move-unreachable from one another, or only the incomparable ones, is not characterized; comparable imports
   are of course reachable by the appropriate move.
2. `composite_fill_totalizes_the_import` uses the sum scale, the canonical coherent one. What an incoherent
   joint scale does to the import, beyond destroying the form, is not measured.
3. The mask arm is measured only through its cross-action. Whether some mask changes the import while leaving
   every factor intact, which would be a genuine import-only move, is not settled here: the mask acts on all
   cells at once and a factor-preserving mask would have to be trivial on the regions.
4. Nothing here is graduated. The results restate canonical `nary` behaviour at the cross region; the value is
   the diagnosis, not new framework content. -/

#print axioms diagAt
#print axioms factor_change_fixes_cross
#print axioms factor_fill_fixes_cross
#print axioms composite_fill_writes_cross
#print axioms composite_fill_overwrites_absent_cross
#print axioms composite_fill_not_a_factor_operation
#print axioms composite_fill_totalizes_the_import
#print axioms fill_on_cross_is_fill_on_import
#print axioms mask_on_cross_is_mask_on_import
#print axioms fill_cannot_reach
#print axioms mask_cannot_reach
#print axioms fin2_cases
#print axioms differ0
#print axioms imports_incomparable
#print axioms import_reselection_beyond_moves
#print axioms factor_reselection_beyond_moves

end Chiralogy.ImportUnderMoves
