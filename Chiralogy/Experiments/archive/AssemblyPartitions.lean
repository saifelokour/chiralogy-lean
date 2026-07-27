import Chiralogy.Model.AssemblageRelations
import Mathlib.Data.Fintype.Pi

/-! ARCHIVED (fully graduated). Which cell-partitions arise from assemblies, the bridge between the full
automorphism group and the fibre-preserving law.

GRADUATED to `Model/NaryAssemblage`, same names: `coordCell`, `region_verdict_factors_through_coord`,
`rigid_factors_force_identity`, `mk2`, and the witness family `gC`, `qC`, `impD`, `impPin`, `Aopen`, `Apin`,
`full_group_not_determined_by_factors` (spec 9.14, 9.15).

CONSOLIDATED: `fib_forces_factor_condition` did not graduate; the canonical `rigid_factors_force_identity`
routes through `fib_fixes_iff`.

KEPT OUT deliberately: `realizable_iff` is canonical `nary_form_iff` restated and is documentation, not a
theorem beside it. The finding it belongs to stands: the blow-up forces no symmetry, and the full group is not
determined by the factors. Typechecks standalone. -/

/-! # Experiment (LIVE): which verdict-partitions arise from assemblies?

`FullAutomorphism` proved the full automorphism group is a LEVEL-SET fact about any classification, and left
open which verdict-partitions an assembly can produce. That is the bridge back to `AssemblySymmetry`'s
fibre-preserving characterization, and this measures it.

Neutral, gravity-free. Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.AssemblyPartitions


/-! ### GRADUATED (Model/NaryAssemblage pass)

Into `Model/NaryAssemblage`, same names: `coordCell`, `region_verdict_factors_through_coord`,
`rigid_factors_force_identity`, `mk2`, and the witness family `gC`, `qC`, `impD`, `impPin`, `Aopen`, `Apin`,
`full_group_not_determined_by_factors`.

CONSOLIDATED: `fib_forces_factor_condition` did not graduate; the canonical `rigid_factors_force_identity`
routes through `fib_fixes_iff` instead, so the canonical surface carries one name fewer.

STAYS OUT, deliberately: `realizable_iff` is canonical `nary_form_iff` restated and is documentation, not a
theorem beside it. `lin` and `blowup_forces_nothing` stay live as the concrete rigidity witness. -/

section General

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

abbrev Pt (X : Fin n → Type) := ∀ k, X k


def Fib (π : ∀ k, X k → X k) (a : Pt X) : Pt X := fun k => π k (a k)

/-! ## Part 1: the constraint on an assembly's verdict-partition -/

/-- The coordinate a region cell reads. -/
def coordCell (i : Fin n) (p : Pt X × Pt X) : X i × X i := (p.1 i, p.2 i)

/-- **THE BLOW-UP.** On region `i`, the verdict factors through the coordinate-`i` pair: two region-`i` cells
with the same coordinate pair carry the same verdict, however the other coordinates differ. So the region-`i`
block of the verdict-partition is the PULLBACK of the factor's own off-diagonal partition along `coordCell i`,
each factor cell blown up across the other coordinates' fibres. -/
theorem region_verdict_factors_through_coord (c : ∀ i, X i → X i → Option Bool)
    (imp : Pt X → Pt X → Option Bool) (i : Fin n) (p q : Pt X × Pt X)
    (hp : differsInOne p.1 p.2 i) (hq : differsInOne q.1 q.2 i)
    (h : coordCell i p = coordCell i q) :
    nary c imp p.1 p.2 = nary c imp q.1 q.2 := by
  have h1 : p.1 i = q.1 i := congrArg Prod.fst h
  have h2 : p.2 i = q.2 i := congrArg Prod.snd h
  exact nary_region_independent c imp hp hq h1 h2

/-- Every off-diagonal factor cell IS blown up: it is realized by at least one region cell, so the pullback
description is onto and no factor cell is invisible. -/
theorem every_factor_cell_is_realized [∀ k, Inhabited (X k)] (i : Fin n) (x y : X i) (hxy : x ≠ y) :
    ∃ p : Pt X × Pt X, differsInOne p.1 p.2 i ∧ coordCell i p = (x, y) := by
  refine ⟨(Function.update (fun j => (default : X j)) i x,
    Function.update (fun j => (default : X j)) i y), ⟨?_, fun j hj => ?_⟩, ?_⟩
  · simp only [Function.update_self]; exact hxy
  · simp only [Function.update_of_ne hj]
  · show ((Function.update (fun j => (default : X j)) i x) i,
      (Function.update (fun j => (default : X j)) i y) i) = (x, y)
    simp

/-- **The cross is unconstrained.** For any target whatever, the assembly over it as import agrees with it on
every cross cell. So the cross block of the verdict-partition is free. -/
theorem cross_is_free (c : ∀ i, X i → X i → Option Bool) (V : Pt X → Pt X → Option Bool)
    {a b : Pt X} (hcr : ¬ ∃ i, differsInOne a b i) : nary c V a b = V a b :=
  nary_apply_imp c V hcr

/-- **THE CHARACTERIZATION, and it is CANONICAL.** A verdict-assignment is assembly-realizable exactly when it
is region-independent, which is the blow-up condition of `region_verdict_factors_through_coord` stated as a
property of the assignment. This is canonical `nary_form_iff`, so Part 1's question already had an answer in
the framework; what is new here is only the partition reading of it. -/
theorem realizable_iff [∀ k, Inhabited (X k)] (V : Pt X → Pt X → Option Bool) :
    (∃ c imp, V = nary c imp) ↔ isAssemblageN V :=
  nary_form_iff V

/-! ## Part 2: does the blow-up FORCE region symmetry? -/

theorem Fib_differsInOne (π : ∀ k, X k → X k) (hinj : ∀ k, Function.Injective (π k))
    (a b : Pt X) (k : Fin n) :
    differsInOne (Fib π a) (Fib π b) k ↔ differsInOne a b k := by
  constructor
  · rintro ⟨hne, hoth⟩
    exact ⟨fun hc => hne (by show π k (a k) = π k (b k); rw [hc]), fun j hj => hinj j (hoth j hj)⟩
  · rintro ⟨hne, hoth⟩
    refine ⟨fun hc => hne (hinj k hc), fun j hj => ?_⟩
    show π j (a j) = π j (b j)
    rw [hoth j hj]

/-- The factor half of the fibre-preserving law, reproved here because live files cannot import each other.
Note what the condition mentions: one factor and one coordinate map. The blow-up MULTIPLICITY does not appear,
so the coarseness the blow-up creates is invisible to the automorphism condition. -/
theorem fib_forces_factor_condition [∀ k, Inhabited (X k)] (π : ∀ k, X k → X k)
    (hinj : ∀ k, Function.Injective (π k)) (c : ∀ k, X k → X k → Option Bool)
    (imp : Pt X → Pt X → Option Bool) (h : relabel (Fib π) (nary c imp) = nary c imp)
    (k : Fin n) (x y : X k) (hxy : x ≠ y) : c k (π k x) (π k y) = c k x y := by
  set a : Pt X := Function.update (fun j => (default : X j)) k x with ha
  set b : Pt X := Function.update (fun j => (default : X j)) k y with hb
  have hd : differsInOne a b k := by
    refine ⟨?_, fun j hj => ?_⟩
    · rw [ha, hb]; simp only [Function.update_self]; exact hxy
    · rw [ha, hb]; simp only [Function.update_of_ne hj]
  have hd' : differsInOne (Fib π a) (Fib π b) k := (Fib_differsInOne π hinj a b k).mpr hd
  have hcell : nary c imp (Fib π a) (Fib π b) = nary c imp a b := congrFun (congrFun h a) b
  rw [nary_apply_differ c imp hd', nary_apply_differ c imp hd] at hcell
  have hax : a k = x := by rw [ha]; simp
  have hbk : b k = y := by rw [hb]; simp
  show c k (π k x) (π k y) = c k x y
  rw [← hax, ← hbk]
  exact hcell

/-- **THE BLOW-UP DOES NOT FORCE SYMMETRY.** If every factor is rigid off its diagonal, the only
fibre-preserving automorphism is the identity, whatever the carrier's other fibre sizes are and however large
the blow-up multiplicity. The coarseness the blow-up creates lives in the CELL count; the automorphism
condition reads the factor's own partition, which the blow-up leaves untouched. -/
theorem rigid_factors_force_identity [∀ k, Inhabited (X k)] (π : ∀ k, X k → X k)
    (hinj : ∀ k, Function.Injective (π k)) (c : ∀ k, X k → X k → Option Bool)
    (imp : Pt X → Pt X → Option Bool)
    (hrigid : ∀ (k : Fin n) (ρ : X k → X k), (∀ x y : X k, x ≠ y → c k (ρ x) (ρ y) = c k x y) → ρ = id)
    (h : relabel (Fib π) (nary c imp) = nary c imp) : Fib π = id := by
  have hid : ∀ k, π k = id := fun k =>
    hrigid k (π k) (fun x y hxy => fib_forces_factor_condition π hinj c imp h k x y hxy)
  funext a
  funext k
  show π k (a k) = a k
  rw [hid k]
  rfl

end General

/-! ### A rigid factor, and a blow-up that forces nothing -/

def lin : Fin 3 → Fin 3 → Option Bool := fun x y => some (decide (x.val ≤ y.val))

/-- **A rigid factor exists.** The linear-order classification on three points admits only the identity off its
diagonal, so it pins its own coordinate completely. -/
theorem lin_rigid : ∀ ρ : Fin 3 → Fin 3, (∀ x y : Fin 3, x ≠ y → lin (ρ x) (ρ y) = lin x y) → ρ = id := by
  decide

abbrev P23 := ∀ _ : Fin 2, Fin 3

-- The blow-up multiplicity on this carrier is three: each off-diagonal factor cell is repeated across the
-- other coordinate's three values. Recorded output: 3.
#eval (Finset.univ.filter (fun p : P23 × P23 =>
  decide (differsInOne p.1 p.2 0 ∧ p.1 0 = 0 ∧ p.2 0 = 1))).card

/-- **And the group is trivial anyway.** With both factors rigid, no non-identity fibre-preserving map fixes
the assembly, though every region cell is blown up threefold. Forced region symmetry is refuted. -/
theorem blowup_forces_nothing (π : ∀ _ : Fin 2, Fin 3 → Fin 3)
    (hinj : ∀ k, Function.Injective (π k)) (imp : P23 → P23 → Option Bool)
    (h : relabel (Fib π) (nary (fun _ => lin) imp) = nary (fun _ => lin) imp) :
    Fib π = id :=
  rigid_factors_force_identity π hinj (fun _ => lin) imp (fun _ ρ hρ => lin_rigid ρ hρ) h

/-! ## Part 3: does the cross freedom leave the full group open? -/

abbrev Q2 := ∀ _ : Fin 2, Fin 2


theorem mk2_factor0 (c0 c1 : Fin 2 → Fin 2 → Option Bool) (imp : Q2 → Q2 → Option Bool) :
    IsFactorAt 0 (mk2 c0 c1 imp) c0 := by
  intro a b hd
  have h0 : a 0 ≠ b 0 := hd.1
  have h1 : a 1 = b 1 := hd.2 1 (by decide)
  simp [mk2, h0, h1]

theorem mk2_factor1 (c0 c1 : Fin 2 → Fin 2 → Option Bool) (imp : Q2 → Q2 → Option Bool) :
    IsFactorAt 1 (mk2 c0 c1 imp) c1 := by
  intro a b hd
  have h1 : a 1 ≠ b 1 := hd.1
  have h0 : a 0 = b 0 := hd.2 0 (by decide)
  simp [mk2, h1, h0]

def gC : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none
def qC : Fin 2 → Fin 2 → Option Bool := fun x y => some (decide (x = y))

def impD : Q2 → Q2 → Option Bool := fun a b => if a = b then some true else none

def impPin : Q2 → Q2 → Option Bool :=
  fun a b => if a = b then (if a = ![0, 0] then some true else none)
             else if a = ![0, 1] ∧ b = ![1, 0] then some false else none

def Aopen : Q2 → Q2 → Option Bool := mk2 gC qC impD
def Apin : Q2 → Q2 → Option Bool := mk2 gC qC impPin

def wreath : Q2 → Q2 := fun a => fun i => if i = 0 then a 0 else (if a 0 = 0 then a 1 else a 1 + 1)

-- Automorphism counts of two assemblies with the SAME factors, differing only in the import.
-- Recorded output: 8 and 1.
#eval (Finset.univ.filter (fun σ : Q2 → Q2 => decide (relabel σ Aopen = Aopen))).card
#eval (Finset.univ.filter (fun σ : Q2 → Q2 => decide (relabel σ Apin = Apin))).card

set_option maxRecDepth 100000 in
/-- **THE CROSS FREEDOM LEAVES THE FULL GROUP OPEN.** Two assemblies with the SAME factors, differing only in
the import, have different automorphism groups: one admits a non-identity map, the other admits none. So the
region constraint of Part 1 does not determine the full group, and knowing the factors is not enough. -/
theorem full_group_not_determined_by_factors :
    (wreath ≠ id ∧ ∀ a b : Q2, Aopen (wreath a) (wreath b) = Aopen a b)
      ∧ (∀ σ : Q2 → Q2, relabel σ Apin = Apin → σ = id) := by
  refine ⟨⟨?_, by decide⟩, by decide⟩
  intro h
  exact absurd (congrFun (congrFun h ![1, 0]) 1) (by decide)

/-! ## THE VERDICTS

PART 1: the constraint is the blow-up, and the characterization is ALREADY CANONICAL.

`region_verdict_factors_through_coord` is the structural fact: on region `i` the verdict factors through the
coordinate-`i` pair, so the region-`i` block of the verdict-partition is the PULLBACK of the factor's own
off-diagonal partition, each factor cell blown up across the other coordinates' fibres.
`every_factor_cell_is_realized` shows the pullback is onto, and `cross_is_free` shows the cross block is
unconstrained.

But the characterization of realizable partitions is canonical `nary_form_iff`, restated:
`realizable_iff` proves an assignment is assembly-realizable exactly when it is region-independent. So Part 1's
question had an answer in the framework already, and what this file adds is only the partition reading. The
class IS clean and checkable: given a verdict-assignment, test region-independence, which is a finite check per
region on a finite carrier.

PART 2: THE BLOW-UP FORCES NOTHING. The hypothesis is refuted.

The reasoning behind the hypothesis was that region cells sharing a coordinate pair must share a verdict, so
cells that must agree can be permuted. That is true at the level of CELLS and false at the level of CARRIER
MAPS, because a carrier map that exploits region `i`'s coarseness must move other coordinates, and those moves
are seen by the other factors' regions.

`fib_forces_factor_condition` makes the point visible: the condition a fibre-preserving map must satisfy
mentions one factor and one coordinate map, and the blow-up MULTIPLICITY does not appear in it at all. The
coarseness lives in the cell count; the automorphism condition reads the factor's own partition, which the
blow-up leaves untouched.

`rigid_factors_force_identity` is the theorem, carrier-general: if every factor is rigid off its diagonal, the
only fibre-preserving automorphism is the identity, at any carrier and any multiplicity. `lin_rigid` shows
rigid factors exist, and `blowup_forces_nothing` instantiates it on a carrier where every region cell is blown
up threefold and the group is trivial regardless.

So the stronger second proof that asymmetry lives only in the import is NOT available. The factors can supply
rigidity, which is `AssemblySymmetry`'s Correction 1 again, now seen from the partition side and with an
explicit rigid factor.

PART 3: the class is clean, the full group is NOT.

`full_group_not_determined_by_factors` settles it: two assemblies with the SAME factors, differing only in the
import, have different automorphism groups. One is fixed by a non-identity coordinate-mixing map; the other is
fixed by nothing but the identity, checked over all two hundred and fifty six carrier maps. Recorded counts
eight and one.

So the bridge exists but does not close the gap. Part 1 pins the REGION part of the partition exactly, and by
`fixes_iff_levels` the full group is the partition's stabilizer; but the CROSS part of the partition is free,
so the stabilizer ranges from the fibre-preserving part up to everything as the import varies. Knowing an
object is an assembly, and knowing its factors, does not determine its full automorphism group.

What the two theorems now share is precise. `fib_fixes_iff` characterizes the fibre-preserving part from the
factors and the import separately. `fixes_iff_levels` characterizes the full group from the partition. Part 1
says which partitions occur. The residual gap is exactly the cross block, which is free, and that is the same
free parameter every earlier build in this thread arrived at.

WHAT REMAINS OPEN

1. The region blocks are pullbacks; the cross block is free. Whether some coarse INVARIANT of the full group,
   short of the group itself, is determined by the factors alone is not measured.
2. `lin_rigid` is a three-point rigidity check by decision. Which classifications are rigid off their
   diagonals, carrier-generally, is not characterized; a linear order suffices but is not shown necessary.
3. `realizable_iff` is canonical restated. If any of this graduates, that theorem is not new content and the
   partition reading would be documentation on `nary_form_iff`, not a theorem beside it. -/

#print axioms region_verdict_factors_through_coord
#print axioms every_factor_cell_is_realized
#print axioms cross_is_free
#print axioms realizable_iff
#print axioms Fib_differsInOne
#print axioms fib_forces_factor_condition
#print axioms rigid_factors_force_identity
#print axioms lin_rigid
#print axioms blowup_forces_nothing
#print axioms mk2_factor0
#print axioms mk2_factor1
#print axioms full_group_not_determined_by_factors

end Chiralogy.AssemblyPartitions
