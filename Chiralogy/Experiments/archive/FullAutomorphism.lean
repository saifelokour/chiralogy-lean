import Chiralogy.Model.AssemblageRelations
import Mathlib.Data.Fintype.Pi

/-! ARCHIVED (fully graduated). The full automorphism group of an assembly.

GRADUATED to `Model/NaryAssemblage`, same names: `cellMap`, `Level`, `fixes_iff_levels`,
`aut_invariant_under_value_relabel`, and the witnesses `Q2`, `wreath`, `mixing_not_closed` (spec 9.15). They
hook nothing canonical, so the graph could not place them; they were placed with the symmetry material they
complete.

The two negative halves stand and are recorded here: absence is NOT distinguished among the level sets, and
there is no genuine value-versus-absence group decomposition, because the mixing elements are not closed under
composition. Typechecks standalone. -/

/-! # Experiment (LIVE): the full automorphism group, and whether absence governs its mixing part

`AssemblySymmetry` characterized the FIBRE-PRESERVING automorphisms of an assembly and showed the full group is
strictly larger: coordinate-mixing maps can fix an assembly, arising in the witness exactly where the assembly
abstained. This characterizes the full group and tests whether absence governs the mixing part.

Neutral, gravity-free. Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.FullAutomorphism


/-! ### GRADUATED (Model/NaryAssemblage pass)

Into `Model/NaryAssemblage`, same names: `cellMap`, `Level`, `fixes_iff_levels`,
`aut_invariant_under_value_relabel`, and the witnesses `Q2`, `wreath`, `mixing_not_closed`. Placed with the
symmetry material by construction: they hook nothing canonical, so the graph could not place them, and they
complete `fib_fixes_iff`.

NOT graduated: the value-swap witnesses and the level-set counts stay live as the record. -/

/-! ## Part 1: the full group, characterized by level sets -/

section General

variable {P : Type}


theorem relabel_comp (σ τ : P → P) (A : P → P → Option Bool) :
    relabel σ (relabel τ A) = relabel (τ ∘ σ) A := rfl

/-- The map a carrier permutation induces on CELLS. -/
def cellMap (σ : P → P) (p : P × P) : P × P := (σ p.1, σ p.2)

/-- The level sets of a classification: the cells carrying a given verdict. -/
def Level (A : P → P → Option Bool) (v : Option Bool) (p : P × P) : Prop := A p.1 p.2 = v

/-- **THE CHARACTERIZATION.** A carrier map fixes a classification exactly when the cell map it induces
preserves every level set. Carrier-general, no finiteness, and NO assemblage structure is used: the full
automorphism group is a fact about classifications, not about assemblies. -/
theorem fixes_iff_levels (σ : P → P) (A : P → P → Option Bool) :
    relabel σ A = A ↔ ∀ (v : Option Bool) (p : P × P), Level A v p → Level A v (cellMap σ p) := by
  constructor
  · intro h v p hp
    have hc : A (σ p.1) (σ p.2) = A p.1 p.2 := congrFun (congrFun h p.1) p.2
    exact hc.trans hp
  · intro h
    funext a b
    exact h (A a b) (a, b) rfl

/-- Automorphisms compose. -/
theorem aut_comp (σ τ : P → P) (A : P → P → Option Bool)
    (hσ : relabel σ A = A) (hτ : relabel τ A = A) : relabel (τ ∘ σ) A = A := by
  rw [← relabel_comp, hτ]; exact hσ

theorem aut_id (A : P → P → Option Bool) : relabel id A = A := rfl

/-! ## Part 2: is absence distinguished among the level sets? -/

/-- **NO.** Relabelling the VERDICTS by any injection leaves the automorphism group unchanged, because the
characterization reads only the level-set PARTITION and never which verdict labels which block. So a large
absence set generates exactly the symmetries a large present set of the same shape would. -/
theorem aut_invariant_under_value_relabel (g : Option Bool → Option Bool)
    (hg : Function.Injective g) (A : P → P → Option Bool) (σ : P → P) :
    relabel σ (fun a b => g (A a b)) = (fun a b => g (A a b)) ↔ relabel σ A = A := by
  constructor
  · intro h
    funext a b
    exact hg (congrFun (congrFun h a) b)
  · intro h
    funext a b
    exact congrArg g (congrFun (congrFun h a) b)

/-- The maximally symmetric classifications are the CONSTANT ones, and every verdict gives one. The order
bottom is not distinguished among them: `cTrue` and `cFalse` have the same full symmetry. -/
theorem constant_has_all_automorphisms (v : Option Bool) (σ : P → P) :
    relabel σ (fun _ _ => v) = fun _ _ => v := rfl

end General

section Assembly

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- Relabelling the verdicts of an assembly gives an assembly, with the factors and the import relabelled the
same way. So the value-relabelled witness below is still an assembly, and the comparison is fair. -/
theorem nary_value_relabel (g : Option Bool → Option Bool) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    (fun a b => g (nary c imp a b))
      = nary (fun i x y => g (c i x y)) (fun a b => g (imp a b)) := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · obtain ⟨i, hi⟩ := hex
    rw [nary_apply_differ c imp hi,
      nary_apply_differ (fun i x y => g (c i x y)) (fun a b => g (imp a b)) hi]
  · rw [nary_apply_imp c imp hex,
      nary_apply_imp (fun i x y => g (c i x y)) (fun a b => g (imp a b)) hex]

/-- Fibre-preserving maps, from `AssemblySymmetry`. -/
def Fib (π : ∀ k, X k → X k) (a : ∀ k, X k) : ∀ k, X k := fun k => π k (a k)

/-- The fibre-preserving maps are closed under composition. -/
theorem Fib_closed (π ρ : ∀ k, X k → X k) :
    (Fib π ∘ Fib ρ) = Fib (fun k => π k ∘ ρ k) := rfl

end Assembly

/-! ### The concrete comparison -/

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

def Agq : Q2 → Q2 → Option Bool := mk2 gC qC impD

/-- The value swap exchanging absence with the true verdict, fixing the false one. -/
def swapVal : Option Bool → Option Bool
  | none => some true
  | some true => none
  | some false => some false

theorem swapVal_injective : Function.Injective swapVal := by
  intro x y h
  match x, y with
  | none, none => rfl
  | none, some true => exact absurd h (by simp [swapVal])
  | none, some false => exact absurd h (by simp [swapVal])
  | some true, none => exact absurd h (by simp [swapVal])
  | some true, some true => rfl
  | some true, some false => exact absurd h (by simp [swapVal])
  | some false, none => exact absurd h (by simp [swapVal])
  | some false, some true => exact absurd h (by simp [swapVal])
  | some false, some false => rfl

/-- The same assembly with its verdicts relabelled: its LARGE level set is now the true one and its absence set
is small, the reverse of the original. -/
def AgqS : Q2 → Q2 → Option Bool := fun a b => swapVal (Agq a b)

def gCS : Fin 2 → Fin 2 → Option Bool := fun x y => swapVal (gC x y)
def qCS : Fin 2 → Fin 2 → Option Bool := fun x y => swapVal (qC x y)
def impDS : Q2 → Q2 → Option Bool := fun a b => swapVal (impD a b)

/-- And it is still an assembly, with the relabelled factors. -/
theorem AgqS_is_an_assembly : AgqS = mk2 gCS qCS impDS := by decide

def wreath : Q2 → Q2 := fun a => fun i => if i = 0 then a 0 else (if a 0 = 0 then a 1 else a 1 + 1)

-- The level-set sizes and the automorphism counts, over all 256 carrier maps. Recorded output:
--   8   absent cells of `Agq`;  4  true cells;  4  false cells
--   4   absent cells of `AgqS`; 8  true cells;  4  false cells
--   8   automorphisms of `Agq`
--   8   automorphisms of `AgqS`
-- The large level set moved from absence to presence and the count did not change.
#eval (Finset.univ.filter (fun p : Q2 × Q2 => decide (Agq p.1 p.2 = none))).card
#eval (Finset.univ.filter (fun p : Q2 × Q2 => decide (Agq p.1 p.2 = some true))).card
#eval (Finset.univ.filter (fun p : Q2 × Q2 => decide (Agq p.1 p.2 = some false))).card
#eval (Finset.univ.filter (fun p : Q2 × Q2 => decide (AgqS p.1 p.2 = none))).card
#eval (Finset.univ.filter (fun p : Q2 × Q2 => decide (AgqS p.1 p.2 = some true))).card
#eval (Finset.univ.filter (fun p : Q2 × Q2 => decide (AgqS p.1 p.2 = some false))).card
#eval (Finset.univ.filter (fun σ : Q2 → Q2 => decide (relabel σ Agq = Agq))).card
#eval (Finset.univ.filter (fun σ : Q2 → Q2 => decide (relabel σ AgqS = AgqS))).card

/-- **ABSENCE IS NOT DISTINGUISHED, measured.** The value-swapped assembly has its large level set at the TRUE
verdict rather than at absence, and the coordinate-mixing map fixes it just the same. The mixing symmetry was
never about absence. -/
theorem mixing_survives_the_value_swap :
    (∀ a b : Q2, Agq (wreath a) (wreath b) = Agq a b)
      ∧ ∀ a b : Q2, AgqS (wreath a) (wreath b) = AgqS a b :=
  ⟨by decide, by decide⟩

/-- **And the boundary break is not absence-driven either.** The mixing map carries a region-0 cell to a cross
cell in BOTH versions. In the original the two cells are absent; in the swapped one they both carry the true
verdict. What dissolves the region-cross boundary is the assembly failing to SEPARATE the two by verdict, and
absence is only the commonest way that happens. -/
theorem boundary_break_is_not_absence :
    differsInOne (![0, 0] : Q2) ![1, 0] 0
      ∧ ¬ (∃ i, differsInOne (wreath ![0, 0]) (wreath ![1, 0]) i)
      ∧ Agq ![0, 0] ![1, 0] = none
      ∧ Agq (wreath ![0, 0]) (wreath ![1, 0]) = none
      ∧ AgqS ![0, 0] ![1, 0] = some true
      ∧ AgqS (wreath ![0, 0]) (wreath ![1, 0]) = some true := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Part 3: is there a value part and an absence part? -/

/-- The mixing map is not fibre-preserving: it moves the second coordinate differently in the two fibres. -/
theorem wreath_not_fibre_preserving :
    (![0, 0] : Q2) 1 = (![1, 0] : Q2) 1 ∧ wreath ![0, 0] 1 ≠ wreath ![1, 0] 1 :=
  ⟨by decide, by decide⟩

/-- **NO DECOMPOSITION: the mixing automorphisms are not a subgroup.** The mixing map squares to the identity,
which is fibre-preserving, so the non-fibre-preserving elements are not closed under composition. There is
therefore no complement to the fibre-preserving subgroup and no product or extension splitting the group into a
value part and an absence part. -/
theorem mixing_not_closed : wreath ∘ wreath = (id : Q2 → Q2) ∧ wreath ≠ (id : Q2 → Q2) := by
  refine ⟨by decide, ?_⟩
  intro h
  exact absurd (congrFun (congrFun h ![1, 0]) 1) (by decide)

/-! ## THE VERDICTS

PART 1: the full group is characterized by LEVEL SETS, carrier-general.

`fixes_iff_levels`: a carrier map fixes a classification exactly when the induced cell map preserves every
level set. No finiteness, no hypotheses, and NO ASSEMBLAGE STRUCTURE. That last point is itself a finding: the
mixing part is not an assemblage phenomenon at all. `fib_fixes_iff` was about assemblies because it read the
factors and the import separately; the full group reads only the partition of cells by verdict, and an assembly
is just one way of producing such a partition.

`aut_comp` and `aut_id` confirm the automorphisms form a group in the usual way.

PART 2: absence is NOT distinguished. The reading is denied.

`aut_invariant_under_value_relabel` is the theorem: relabelling the verdicts by ANY injection leaves the
automorphism group unchanged, because the characterization reads the level-set PARTITION and never which
verdict labels which block. So a large absence set generates exactly the symmetries a large present set of the
same shape would, and there is nothing special about `none`.

`constant_has_all_automorphisms` makes the same point at the extreme: the maximally symmetric classifications
are the constant ones, and the order bottom is not distinguished among them. `cTrue` and `cFalse` have the same
full symmetry as `botC`.

MEASURED, and it agrees. `AgqS` is the witness assembly with absence and the true verdict exchanged, still an
assembly by `nary_value_relabel` and `AgqS_is_an_assembly`. Its large level set is now presence, not absence:
the recorded counts move from eight absent and four true, to four absent and eight true. Its automorphism count
is UNCHANGED at eight, and `mixing_survives_the_value_swap` shows the same mixing map fixes it.

THE BOUNDARY QUESTION, answered and reframed. Mixing automorphisms DO identify a region cell with a cross cell:
`boundary_break_is_not_absence` shows the map carrying a region-0 pair to a cross pair. But it happens in BOTH
versions, at absence in one and at the true verdict in the other. So the mechanism is not that absence dissolves
the region-cross boundary. It is that the boundary is invisible to the object wherever the object fails to
SEPARATE the two sides by verdict. Absence is the commonest way that happens, not the reason it happens.

PART 3: no genuine decomposition. The split is a description, not group structure.

The fibre-preserving automorphisms form a subgroup (`Fib_closed` with `aut_comp`). The mixing ones do NOT:
`mixing_not_closed` shows the mixing map squares to the identity, which is fibre-preserving, so the
non-fibre-preserving elements are not closed under composition. A set that is not closed cannot be a subgroup,
so there is no complement, no semidirect product, and no extension splitting the group into two parts.

So the proposed reading fails twice over. The mixing part is not governed by absence (Part 2), and it is not a
group-theoretic part at all (Part 3). The only genuine structure is: the fibre-preserving automorphisms are a
subgroup of the full automorphism group, and the full group is cut out by the level-set partition. Calling the
one part "said" and the other "unsaid" would be a description laid over a subgroup and its complement, and the
complement is not an object.

WHAT REMAINS OPEN

1. Whether the fibre-preserving subgroup is NORMAL in the full automorphism group is not settled. On the
   four-point carrier used here it is, since the product maps there form the Klein four-group inside the
   symmetric group on four points, but that is a coincidence of two-by-two and no general claim is made.
2. `fixes_iff_levels` characterizes the group by the level-set partition. Which partitions of the cell set
   arise from assemblies, and how the assembly structure constrains them, is not measured; that is the question
   that would connect the full group back to `fib_fixes_iff`.
3. The counts are decide-bound observations on one carrier. The level-set characterization and the
   value-relabel invariance are the carrier-general theorems; the counts illustrate them and prove nothing on
   their own. -/

#print axioms relabel_comp
#print axioms fixes_iff_levels
#print axioms aut_comp
#print axioms aut_id
#print axioms aut_invariant_under_value_relabel
#print axioms constant_has_all_automorphisms
#print axioms nary_value_relabel
#print axioms Fib_closed
#print axioms mk2_factor0
#print axioms mk2_factor1
#print axioms swapVal_injective
#print axioms AgqS_is_an_assembly
#print axioms mixing_survives_the_value_swap
#print axioms boundary_break_is_not_absence
#print axioms wreath_not_fibre_preserving
#print axioms mixing_not_closed

end Chiralogy.FullAutomorphism
