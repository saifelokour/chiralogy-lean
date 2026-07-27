import Chiralogy.Model.AssemblageRelations
import Chiralogy.Protocol.Membership

/-! ARCHIVED (partly graduated; the register sort recorded here). GR and QM as an assemblage, built kernel
outward under the phi = 1 filter.

NAMED `PhysicsRegisterAssemblage` because `archive/PhysicsRegister.lean` is a different and earlier
investigation (does physics instantiate Chiralogy), which stays as it is.

GRADUATED, both under mechanism names rather than register names:
  completeness_does_not_kill_content -> Model/Moves as nondegeneracy_survives_every_fill, with cResist
      (spec 9.6)
  fills_at_different_cells_commute, fills_at_same_cell_absorb -> Model/InformationOrder, carrier-general
      (spec 9.11)

NOT GRADUATED, by the phi = 1 filter: everything a register with all distinctions absence-carried would also
produce is an artifact of absence-carriage, not physics, and is recorded here only. The register reading itself
stays a READING in the spec's Registers section and enters no derived layer. Typechecks standalone. -/

/-! # Experiment (LIVE): the physics register, GR and QM as an assemblage

A MODELING build, kernel outward. It constructs GR and QM as classifications in the framework and tests which
structural claims are FORCED and which are decorative.

THE FILTER, governing everything below. A conclusion that any phi = 1 register would also produce is an
ARTIFACT of absence-carriage, not a physics finding, and is flagged as such. Only conclusions that use the
register's SPECIFIC structure count as physics. The GR stand-in built here is deliberately phi = 1 (every
distinction absence-carried) and the QM stand-in is phi = 0 (every distinction present-carried), so the filter
has something to bite on.

A register construction, not canonical. Small finite carriers throughout. Live experiment. No canonical edit,
nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.PhysicsRegister

/-! ### GRADUATED (Model/InformationOrder pass)

Into `Model/InformationOrder`, same names and now carrier-general: `fills_at_different_cells_commute` and
`fills_at_same_cell_absorb`. This clears the deferral recorded in the Moves-pass note above.

`same_cell_order_matters` stays live as the witness that the absorption is order-sensitive. -/

/-! ### GRADUATED (Model/Moves pass)

Into `Model/Moves`: `cResist` under the same name, and `completeness_does_not_kill_content` renamed to
`nondegeneracy_survives_every_fill`, which states the mechanism rather than the register claim it refutes.

DEFERRED: `fills_at_different_cells_commute` and `fills_at_same_cell_absorb` use `fillCell`, which lives in
Model/InformationOrder, so they go with that group.

The local copies are kept only while other live results in this file still use them. -/

/-! ## Kernel layer: is the impossibility reflexive, and does it sit at the center? -/

/-- **Background-independence as a reflexive demand.** A classifier over backgrounds is background-independent
when it realizes every description of backgrounds, its own included: a surjection onto the description space. -/
def BackgroundIndependent {B : Type} (desc : B → B → Bool) : Prop := Function.Surjective desc

/-- **It hits the acentric center, at every carrier.** The demand is exactly the forced-empty
self-classification the diagonal forbids. Kernel-level and carrier-level: no finiteness, no model, no choice of
background space rescues it. -/
theorem background_independence_impossible {B : Type} (desc : B → B → Bool) :
    ¬ BackgroundIndependent desc :=
  no_total_internal_self_description desc

/-- The equivalence form: no background space is its own description space. -/
theorem background_independence_no_fixed_form {B : Type} : ¬ Nonempty (B ≃ (B → Bool)) :=
  no_self_description_equiv

/-- **The filter, applied at once.** The theorem is the diagonal. It uses nothing about gravity, geometry, or
quantum mechanics; every reflexive demand at every carrier produces it. So the physics content is entirely in
the IDENTIFICATION of background-independence with a reflexive demand, and none of it is in the proof. Flagged:
FORCED at the kernel, but forced for any reflexive demand whatever. -/
theorem background_independence_is_generic {B : Type} (desc : B → B → Bool)
    (anything : B → B → Bool) :
    ¬ BackgroundIndependent desc ∧ ¬ Function.Surjective anything :=
  ⟨background_independence_impossible desc, no_total_internal_self_description anything⟩

/-! ### The problem of time -/

/-- An evolution parameter realized internally: the classification's own rows ARE the comparison the parameter
induces. -/
def RealizesOwnEvolution {B : Type} (g : B → B → Bool) (s : B → Nat) : Prop :=
  ∀ x y, g x y = decide (s y ≤ s x)

/-- **The problem of time is NOT the same impossibility.** Realizing one's own evolution parameter is
SATISFIABLE at every carrier: the comparison classification realizes its own scale. Background-independence
fails for every classifier; this succeeds for every scale. The two are distinct demands, and only the first is
an impossibility. -/
theorem evolution_realizable {B : Type} (s : B → Nat) :
    RealizesOwnEvolution (fun x y => decide (s y ≤ s x)) s := fun _ _ => rfl

/-- The difference, stated as the contrast it is: universally impossible against universally satisfiable. -/
theorem time_differs_from_background {B : Type} (desc : B → B → Bool) (s : B → Nat) :
    ¬ BackgroundIndependent desc
      ∧ RealizesOwnEvolution (fun x y => decide (s y ≤ s x)) s :=
  ⟨background_independence_impossible desc, evolution_realizable s⟩

/-! ## Protocol layer: two Members, forced not chosen -/

/-- GR's stand-in carrier: three curvature classes. Each geometry recognizes itself and abstains on the others,
so every distinction is absence-carried: this register is phi = 1 by construction. -/
def grC : Fin 3 → Fin 3 → Option Bool := fun x y => if x = y then some true else none

/-- QM's stand-in carrier: three spectra, sharply distinguished. Total, so every distinction is present-carried:
this register is phi = 0. -/
def qmC : Fin 3 → Fin 3 → Option Bool := fun x y => some (decide (x = y))

theorem grC_nondegenerate : NonDegenerate grC := ⟨0, 1, by decide⟩
theorem qmC_nondegenerate : NonDegenerate qmC := ⟨0, 1, by decide⟩

/-- GR's register is phi = 1: no distinction is present-carried. -/
theorem grC_phi_one (x x' : Fin 3) : ¬ presentCarried grC x x' := by
  rintro ⟨z, b, b', h1, h2, hb⟩
  have hb1 : b = true := by
    by_cases hx : x = z
    · simp only [grC, if_pos hx] at h1; exact (Option.some_inj.mp h1).symm
    · simp only [grC, if_neg hx] at h1; exact absurd h1.symm (Option.some_ne_none b)
  have hb2 : b' = true := by
    by_cases hx : x' = z
    · simp only [grC, if_pos hx] at h2; exact (Option.some_inj.mp h2).symm
    · simp only [grC, if_neg hx] at h2; exact absurd h2.symm (Option.some_ne_none b')
  exact hb (hb1.trans hb2.symm)

/-- QM's register is phi = 0 on its distinct rows: every distinction is present-carried, so no fill can merge
them. -/
theorem qmC_present_carried (x x' : Fin 3) (h : x ≠ x') : presentCarried qmC x x' :=
  ⟨x, true, false, by simp [qmC], by simp [qmC, Ne.symm h], by decide⟩

def GR : Member where
  X := Fin 3
  B := Option Bool
  canDiffer := ⟨none, some true, by decide⟩
  classify := grC
  nondegenerate := ⟨0, 1, by decide⟩

def QM : Member where
  X := Fin 3
  B := Option Bool
  canDiffer := ⟨none, some true, by decide⟩
  classify := qmC
  nondegenerate := ⟨0, 1, by decide⟩

/-- Both conform: the payload fires on each, so each carries the hole. -/
theorem both_conform : ¬ Function.Surjective GR.classify ∧ ¬ Function.Surjective QM.classify :=
  ⟨payload GR, payload QM⟩

/-! ### The forcing -/

/-- A register together with the background each of its carrier points presupposes. -/
structure Register (C B : Type) where
  bg : C → B
  classify : C → C → Option Bool

/-- QM's reading: all states presuppose ONE background. -/
def BackgroundFixed {C B : Type} (R : Register C B) : Prop := ∀ x y : C, R.bg x = R.bg y

/-- GR's reading: distinct carrier points ARE distinct backgrounds. -/
def BackgroundVaried {C B : Type} (R : Register C B) : Prop := Function.Injective R.bg

/-- **The two-Member structure is FORCED, not chosen.** A single register that both fixes and varies the
background is a subsingleton: each carrier point presupposes the same background, and distinct backgrounds
force distinct points, so there is only one point. -/
theorem one_carrier_collapses {C B : Type} (R : Register C B)
    (hfix : BackgroundFixed R) (hvar : BackgroundVaried R) (x y : C) : x = y :=
  hvar (hfix x y)

/-- **And a subsingleton register is degenerate, so it is not a Member.** No single carrier serves both
readings. The assemblage reading cannot collapse to one Member with two poles. -/
theorem two_members_forced {C B : Type} (R : Register C B)
    (hfix : BackgroundFixed R) (hvar : BackgroundVaried R) : ¬ NonDegenerate R.classify := by
  rintro ⟨x, y, hne⟩
  exact hne (by rw [one_carrier_collapses R hfix hvar x y])

/-- The two readings are each realized, so the forcing is not vacuous: both hypotheses are satisfiable
separately and only their conjunction collapses. -/
def grReg : Register (Fin 3) (Fin 3) := ⟨id, grC⟩
def qmReg : Register (Fin 3) (Fin 3) := ⟨fun _ => 0, qmC⟩

theorem readings_realized :
    BackgroundVaried grReg ∧ ¬ BackgroundFixed grReg
      ∧ BackgroundFixed qmReg ∧ ¬ BackgroundVaried qmReg := by
  refine ⟨fun x y h => h, ?_, fun _ _ => rfl, ?_⟩
  · intro h
    have hb : (0 : Fin 3) = (1 : Fin 3) := h 0 1
    exact absurd hb (by decide)
  · intro h
    have hb : (0 : Fin 3) = (1 : Fin 3) := h rfl
    exact absurd hb (by decide)

/-! ## Model layer: the assemblage, and the hole in the cross region -/

abbrev P3 := ∀ _ : Fin 2, Fin 3

def pair (A B : Fin 3 → Fin 3 → Option Bool) : ∀ _ : Fin 2, Fin 3 → Fin 3 → Option Bool :=
  fun i => if i = 0 then A else B

theorem pair_zero (A B : Fin 3 → Fin 3 → Option Bool) : pair A B 0 = A := by simp [pair]
theorem pair_one (A B : Fin 3 → Fin 3 → Option Bool) : pair A B 1 = B := by simp [pair]

/-- The unified theory: the assemblage of the two registers over an import. -/
noncomputable def Unified (imp : P3 → P3 → Option Bool) : P3 → P3 → Option Bool :=
  nary (pair grC qmC) imp

theorem unified_is_assemblage (imp : P3 → P3 → Option Bool) : isAssemblageN (Unified imp) :=
  fun _ _ _ _ _ hd hd' ha hb => nary_region_independent _ _ hd hd' ha hb

theorem unified_factors (imp : P3 → P3 → Option Bool) :
    IsFactorAt 0 (Unified imp) grC ∧ IsFactorAt 1 (Unified imp) qmC := by
  constructor
  · rw [← pair_zero grC qmC]; exact IsFactorAt_of_nary 0 (pair grC qmC) imp
  · rw [← pair_one grC qmC]; exact IsFactorAt_of_nary 1 (pair grC qmC) imp

/-! ### The hole lands in the cross region -/

def face {Y : Type} (T : Y → Y → Option Bool) : Y → Y → Bool := fun x y => (T x y).getD false

def diagWitness {Y : Type} (g : Y → Y → Bool) : Y → Bool := fun y => !(g y y)

theorem diagWitness_not_realized {Y : Type} (g : Y → Y → Bool) (x : Y) : g x ≠ diagWitness g := by
  intro h
  have hx := congrFun h x
  cases hb : g x x <;> rw [hb] at hx <;> simp [diagWitness, hb] at hx

theorem diagWitness_reads_diagonal {Y : Type} (g g' : Y → Y → Bool) (h : ∀ y, g y y = g' y y) :
    diagWitness g = diagWitness g' := by
  funext y; simp [diagWitness, h y]

/-- **Every diagonal cell is a cross cell.** No point differs from itself in any coordinate, so the diagonal is
import territory, owned by neither factor. -/
theorem diagonal_is_cross (a : P3) : ¬ ∃ i, differsInOne a a i := by
  rintro ⟨i, hne, _⟩; exact hne rfl

theorem unified_diagonal_is_import (imp : P3 → P3 → Option Bool) (a : P3) :
    Unified imp a a = imp a a :=
  nary_apply_imp (pair grC qmC) imp (diagonal_is_cross a)

/-- **The hole of the complete-and-faithful self-classification lands in the cross region.** The completed
unified theory misses a description, and that description is manufactured entirely from diagonal cells, which
are import territory. Neither factor contributes: replacing both registers by anything else, with the same
import, misses the SAME description. Read: the Planck regime sits exactly where each theory's carrier is asked
to include the other's precondition, and neither theory speaks there. -/
theorem hole_is_in_the_cross_region (imp : P3 → P3 → Option Bool) (s : P3 → Nat)
    (c' : ∀ _ : Fin 2, Fin 3 → Fin 3 → Option Bool) :
    (∀ x, face (totalization s (Unified imp)) x ≠ diagWitness (face (totalization s (Unified imp))))
      ∧ diagWitness (face (totalization s (Unified imp)))
          = diagWitness (face (totalization s (nary c' imp))) := by
  refine ⟨fun x => diagWitness_not_realized _ x, ?_⟩
  apply diagWitness_reads_diagonal
  intro a
  simp only [face, totalization, Unified, nary_apply_imp _ _ (diagonal_is_cross a)]

/-- **FILTER VERDICT on the cross-region hole: ARTIFACT.** The proof uses no property of `grC` or `qmC`, no
phi, and no physics: `diagonal_is_cross` holds for every product carrier and every pair of factors, so every
two-factor assemblage of every two registers produces the identical conclusion. Stated as the generic theorem
it is. -/
theorem cross_region_hole_is_generic (imp : P3 → P3 → Option Bool) (s : P3 → Nat)
    (c c' : ∀ _ : Fin 2, Fin 3 → Fin 3 → Option Bool) :
    diagWitness (face (totalization s (nary c imp)))
      = diagWitness (face (totalization s (nary c' imp))) := by
  apply diagWitness_reads_diagonal
  intro a
  simp only [face, totalization, nary_apply_imp _ _ (diagonal_is_cross a)]

/-! ### Peers, and whether the claim is physics -/

/-- **GR and QM are peers.** Factors of the same composite at distinct coordinates. -/
theorem gr_qm_are_peers (imp : P3 → P3 → Option Bool) :
    ArePeersIn (Unified imp) 0 1 grC qmC :=
  ⟨by decide, (unified_factors imp).1, (unified_factors imp).2⟩

/-- **Neither reduces to the other.** Two composites sharing their coordinate-0 factor have different
coordinate-1 factors, so knowing GR's factor determines nothing about QM's. The unified theory is their
assemblage, not a derivation of one from the other. -/
theorem neither_reduces (imp : P3 → P3 → Option Bool) :
    IsFactorAt 0 (Unified imp) grC
      ∧ IsFactorAt 0 (nary (pair grC grC) imp) grC
      ∧ IsFactorAt 1 (Unified imp) qmC
      ∧ IsFactorAt 1 (nary (pair grC grC) imp) grC
      ∧ qmC ≠ grC := by
  refine ⟨(unified_factors imp).1, ?_, (unified_factors imp).2, ?_, ?_⟩
  · rw [← pair_zero grC grC]; exact IsFactorAt_of_nary 0 (pair grC grC) imp
  · rw [← pair_one grC grC]; exact IsFactorAt_of_nary 1 (pair grC grC) imp
  · intro h
    exact absurd (congrFun (congrFun h 0) 1) (by decide)

/-- **FILTER VERDICT on peers-do-not-reduce: ARTIFACT.** The statement uses only that the two occupy distinct
coordinates of an assemblage; any two registers whatever, phi = 1 or not, give it. Stated generically. -/
theorem peers_do_not_reduce_is_generic (A B : Fin 3 → Fin 3 → Option Bool)
    (imp : P3 → P3 → Option Bool) : ArePeersIn (nary (pair A B) imp) 0 1 A B := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [← pair_zero A B]; exact IsFactorAt_of_nary 0 (pair A B) imp
  · rw [← pair_one A B]; exact IsFactorAt_of_nary 1 (pair A B) imp

/-! ## The demoted claims

### The commutator reading, tested -/

/-- **Fills at DIFFERENT cells commute exactly.** Each cell receives its own scale's verdict, and the order in
which the two are applied is irrelevant. -/
theorem fills_at_different_cells_commute {Y : Type} [DecidableEq Y] (s s' : Y → Nat) (p q : Y × Y)
    (hpq : p ≠ q) (c : Y → Y → Option Bool) :
    fillCell s q (fillCell s' p c) = fillCell s' p (fillCell s q c) := by
  funext x y
  by_cases hq : (x, y) = q
  · have hp : ¬ ((x, y) = p) := by rw [hq]; exact fun h => hpq h.symm
    simp only [fillCell, if_pos hq, if_neg hp]
  · by_cases hp : (x, y) = p
    · simp only [fillCell, if_pos hp, if_neg hq]
    · simp only [fillCell, if_neg hp, if_neg hq]

/-- **Fills at the SAME cell absorb, and the FIRST one wins.** The second fill finds the cell present and
leaves it alone. -/
theorem fills_at_same_cell_absorb {Y : Type} [DecidableEq Y] (s s' : Y → Nat) (p : Y × Y)
    (c : Y → Y → Option Bool) :
    fillCell s p (fillCell s' p c) = fillCell s' p c := by
  funext x y
  by_cases hp : (x, y) = p
  · simp only [fillCell, if_pos hp, Option.getD_some]
  · simp only [fillCell, if_neg hp]

/-- **So the order matters only at the SAME cell.** Two fills of one cell with scales that disagree there give
different verdicts depending on which went first. -/
theorem same_cell_order_matters :
    fillCell (fun _ : Fin 3 => 0) (0, 1) (fillCell (fun x : Fin 3 => x.val) (0, 1) (botC (Fin 3)))
      ≠ fillCell (fun x : Fin 3 => x.val) (0, 1) (fillCell (fun _ : Fin 3 => 0) (0, 1) (botC (Fin 3))) := by
  intro h
  have hc := congrFun (congrFun h 0) 1
  simp [fillCell, botC] at hc

/-- **VERDICT on the commutator reading: REFUTED, and refuted with structure.** The framework's pattern is the
MIRROR of the commutator's. In quantum mechanics different observables fail to commute while repeating one
observable is reproducible. Here different cells commute exactly and repeating one cell is where order decides
the verdict. So the match is not merely absent, it is inverted: the reading is decorative. -/
theorem commutator_reading_is_inverted {Y : Type} [DecidableEq Y] (s s' : Y → Nat) (p q : Y × Y)
    (hpq : p ≠ q) (c : Y → Y → Option Bool) :
    fillCell s q (fillCell s' p c) = fillCell s' p (fillCell s q c) :=
  fills_at_different_cells_commute s s' p q hpq c

/-! ### Completeness-kills-content, tested -/

/-- A phi = 1 register whose content NO completion destroys: two rows, each present exactly where the other
abstains, carrying `some false`. -/
def cResist : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some false else none

theorem cResist_phi_one : ¬ presentCarried cResist 0 1 := by
  rintro ⟨z, b, b', h1, h2, hb⟩
  have hb1 : b = false := by
    by_cases hx : (0 : Fin 2) = z
    · simp only [cResist, if_pos hx] at h1; exact (Option.some_inj.mp h1).symm
    · simp only [cResist, if_neg hx] at h1; exact absurd h1.symm (Option.some_ne_none b)
  have hb2 : b' = false := by
    by_cases hx : (1 : Fin 2) = z
    · simp only [cResist, if_pos hx] at h2; exact (Option.some_inj.mp h2).symm
    · simp only [cResist, if_neg hx] at h2; exact absurd h2.symm (Option.some_ne_none b')
  exact hb (hb1.trans hb2.symm)

theorem cResist_nondegenerate : NonDegenerate cResist := ⟨0, 1, by decide⟩

/-- **VERDICT on completeness-kills-content: REFUTED, not merely an artifact.** The claim does not follow from
phi = 1, because it is FALSE at phi = 1. `cResist` has every distinction absence-carried, yet EVERY scale
leaves it non-degenerate: to merge the two rows a scale would have to order the two points both ways at once.
Absence of presence-protection does not imply destroyability; the scale's own consistency protects what
presence does not. The physics claim rested on a converse the framework never proved. -/
theorem completeness_does_not_kill_content (s : Fin 2 → Nat) :
    NonDegenerate (totalization s cResist) := by
  refine ⟨0, 1, fun h => ?_⟩
  by_cases hs : s 0 ≤ s 1
  · have h0 := congrFun h 0
    simp [totalization, cResist, hs] at h0
  · have h1 := congrFun h 1
    have hs' : s 1 ≤ s 0 := by omega
    simp [totalization, cResist, hs'] at h1

/-- What IS true at phi = 1, kept for contrast: presence protects, so a present-carried distinction survives
every scale. The failed claim was the converse. -/
theorem present_carried_survives_every_scale {Y : Type} (c : Y → Y → Option Bool) (x x' : Y)
    (hp : presentCarried c x x') (s : Y → Nat) : NonDegenerate (totalization s c) :=
  ⟨x, x', survives_totalization c s x x' hp⟩

/-! ## The shared silence -/

/-- **The shape of a supply gap.** An action of a parameter space on a state space where the parameter MATTERS
(so something is genuinely supplied) and is NOT RECOVERABLE from the outcome (so nothing internal fixes it).
Totality is carried by the type: `act` has no precondition, so no state rules any parameter out. -/
structure SupplyGap (P S : Type) where
  act : P → S → S
  nonFaithful : ∃ p p' : P, p ≠ p' ∧ ∀ s, act p s = act p' s
  nonTrivial : ∃ (p p' : P) (s : S), act p s ≠ act p' s

/-- **No canonical selector.** For any candidate map from states to parameters, another candidate gives a
different result somewhere: nothing in the state space picks the parameter out. This is the shared
impossibility, proved once for the shape and inherited by every instance. -/
theorem no_canonical_selector {P S : Type} (G : SupplyGap P S) (σ : S → P) :
    ∃ (σ' : S → P) (s : S), G.act (σ s) s ≠ G.act (σ' s) s := by
  obtain ⟨p, p', s₀, hne⟩ := G.nonTrivial
  by_cases h : G.act (σ s₀) s₀ = G.act p s₀
  · exact ⟨fun _ => p', s₀, by rw [h]; exact hne⟩
  · exact ⟨fun _ => p, s₀, h⟩

/-- The framework's silence: who supplies the scale. -/
def scaleGap : SupplyGap (Fin 2 → Nat) (Fin 2 → Fin 2 → Option Bool) where
  act := totalization
  nonFaithful := by
    refine ⟨fun _ => 0, fun _ => 1, ?_, ?_⟩
    · intro h; exact absurd (congrFun h 0) (by decide)
    · intro c; funext x y; simp [totalization]
  nonTrivial := by
    refine ⟨fun _ => 0, fun x => x.val, botC (Fin 2), ?_⟩
    intro h
    have hc := congrFun (congrFun h 0) 1
    simp [totalization, botC] at hc

/-- The register's silence: what selects the measurement basis. The parameter is which observable is read and
which verdict the reading writes, that is a cell together with a scale; the action is the single-cell fill. -/
def basisGap : SupplyGap ((Fin 2 × Fin 2) × (Fin 2 → Nat)) (Fin 2 → Fin 2 → Option Bool) where
  act := fun p c => fillCell p.2 p.1 c
  nonFaithful := by
    refine ⟨((0, 1), fun _ => 0), ((0, 1), fun _ => 1), ?_, ?_⟩
    · intro h
      exact absurd (congrFun (congrArg Prod.snd h) 0) (by decide)
    · intro c; funext x y; simp [fillCell]
  nonTrivial := by
    refine ⟨((0, 1), fun _ => 0), ((0, 1), fun x => x.val), botC (Fin 2), ?_⟩
    intro h
    have hc := congrFun (congrFun h 0) 1
    simp [fillCell, botC] at hc

/-- **VERDICT on the shared silence: SAME STRUCTURE, and the impossibility transfers.** Both gaps instantiate
one shape, and `no_canonical_selector` therefore holds for both by a single proof: nothing in the framework
selects the scale, nothing in the register selects the basis, for the same reason. This is a shared
impossibility of a selector, not an analogy. The honest qualification: the shape has two clauses and any
parameterized non-faithful action instantiates it, so what is shared is generic in form even though the
transfer is real. -/
theorem shared_silence_same_structure (σ : (Fin 2 → Fin 2 → Option Bool) → (Fin 2 → Nat))
    (τ : (Fin 2 → Fin 2 → Option Bool) → ((Fin 2 × Fin 2) × (Fin 2 → Nat))) :
    (∃ (σ' : (Fin 2 → Fin 2 → Option Bool) → (Fin 2 → Nat)) (c : Fin 2 → Fin 2 → Option Bool),
        scaleGap.act (σ c) c ≠ scaleGap.act (σ' c) c)
      ∧ (∃ (τ' : (Fin 2 → Fin 2 → Option Bool) → ((Fin 2 × Fin 2) × (Fin 2 → Nat)))
          (c : Fin 2 → Fin 2 → Option Bool),
        basisGap.act (τ c) c ≠ basisGap.act (τ' c) c) :=
  ⟨no_canonical_selector scaleGap σ, no_canonical_selector basisGap τ⟩

/-! ## THE SORT

FORCED-PHYSICS (uses the register's specific structure):

  `one_carrier_collapses`, `two_members_forced`, `readings_realized`. The two-Member structure is forced, and
  the forcing uses the SPECIFIC content of the two readings: QM's carrier fixes the background, GR's varies it,
  and a carrier doing both is a subsingleton hence not a Member. No generic assemblage argument gives this; it
  is the only load-bearing physics step in the build. `grC_phi_one` and `qmC_present_carried` are the specific
  contents that make the filter applicable at all.

ARTIFACT (any assemblage of any two registers produces it, phi irrelevant):

  `hole_is_in_the_cross_region`, with `cross_region_hole_is_generic` as its own refutation as physics. The hole
  lands on the diagonal because no point differs from itself, not because of anything about gravity or
  measurement. The Planck-regime reading is an identification laid over a generic fact.

  `gr_qm_are_peers`, `neither_reduces`, with `peers_do_not_reduce_is_generic` as their refutation as physics.
  Peers-do-not-reduce is the register's boldest claim and it is generic: it says only that two things occupy
  distinct coordinates of an assemblage.

  `background_independence_impossible` is FORCED at the kernel but generic in the same way
  (`background_independence_is_generic`): the theorem is the diagonal, and the physics is in the
  identification.

DECORATIVE or REFUTED:

  The commutator reading: REFUTED, and inverted. `fills_at_different_cells_commute` and
  `fills_at_same_cell_absorb` show different observables commute exactly while repeating one observable is
  where order decides (`same_cell_order_matters`). Quantum mechanics has the opposite pattern. Not a rhyme, a
  mirror.

  Completeness-kills-content: REFUTED, and more strongly than predicted. It is not a phi = 1 artifact, because
  it is FALSE at phi = 1 (`completeness_does_not_kill_content`). The framework proves presence protects
  (`present_carried_survives_every_scale`); the converse, that absence exposes, was never proved and is false.

  The problem of time as an impossibility: REFUTED. `evolution_realizable` shows realizing one's own evolution
  parameter is satisfiable at every carrier, so it is not the diagonal seen sideways. It relocates as a
  silence, which is where the last section finds it.

SHARED SILENCE: same structure, transfer real, shape generic. `shared_silence_same_structure`.

WHAT REMAINS OPEN

1. The carriers are three-point stand-ins. Whether the two-Member forcing survives a carrier rich enough to
   carry a genuine background dependence, rather than a bare `bg` map, is not tested.
2. The import is left free everywhere. Whether any physically motivated import exists, and whether the choice
   is itself forced, is untouched; the cross-region result holds for all of them, which is exactly why it is an
   artifact.
3. `SupplyGap` has two clauses. A sharper shape, one that distinguishes the scale gap from an arbitrary
   parameterized action, would decide whether the shared silence is more than generic. Not built here.
4. Nothing here is graduated, and nothing here should be: the build is a register, and its one forced step is
   about the register, not about the framework. -/

#print axioms background_independence_impossible
#print axioms background_independence_no_fixed_form
#print axioms background_independence_is_generic
#print axioms evolution_realizable
#print axioms time_differs_from_background
#print axioms grC_nondegenerate
#print axioms qmC_nondegenerate
#print axioms grC_phi_one
#print axioms qmC_present_carried
#print axioms both_conform
#print axioms one_carrier_collapses
#print axioms two_members_forced
#print axioms readings_realized
#print axioms pair_zero
#print axioms pair_one
#print axioms unified_is_assemblage
#print axioms unified_factors
#print axioms diagWitness_not_realized
#print axioms diagWitness_reads_diagonal
#print axioms diagonal_is_cross
#print axioms unified_diagonal_is_import
#print axioms hole_is_in_the_cross_region
#print axioms cross_region_hole_is_generic
#print axioms gr_qm_are_peers
#print axioms neither_reduces
#print axioms peers_do_not_reduce_is_generic
#print axioms fills_at_different_cells_commute
#print axioms fills_at_same_cell_absorb
#print axioms same_cell_order_matters
#print axioms commutator_reading_is_inverted
#print axioms cResist_phi_one
#print axioms cResist_nondegenerate
#print axioms completeness_does_not_kill_content
#print axioms present_carried_survives_every_scale
#print axioms no_canonical_selector
#print axioms shared_silence_same_structure

end Chiralogy.PhysicsRegister
