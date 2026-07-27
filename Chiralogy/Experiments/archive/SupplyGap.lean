import Chiralogy.Model.AssemblageRelations

/-! ARCHIVED (partly graduated, negative finding recorded here). SupplyGap as a candidate third kernel
condition.

GRADUATED to `Model/InformationOrder`, same names: `OperatorFaithful`, `open_operator_faithful`,
`fill_operator_ext_iff` (spec 9.10). They sharpen canonical `totalization_not_faithful` rather than repeating
it: that one is about the object, these are about the parameter.

NOT GRADUATED, and this is the finding: there is no third kernel condition. The two-clause form of
`no_canonical_selector` is below kernel level (`no_canonical_selector_trivial` holds for an arbitrary function
of two arguments), and the genuine gap is a corollary of the extremes, not an independent condition. The
instruction was not to manufacture one, and none was. Typechecks standalone. -/

/-! # Experiment (LIVE): is the supply-gap a third kernel condition, and where does gravity sit?

Two linked questions.

FIRST: the framework has two named forced kernel conditions, THE HOLE (what a classification cannot contain)
and THE FLOOR (what a Member cannot lose). The candidate third is the SUPPLY-GAP: what a move cannot recover,
namely its own parameter. This file tests whether it is forced and independent, or a corollary.

SECOND: gravity's placement in the GR/QM reading, which Part 1's verdict decides. Candidate A is the import
(the cross region neither factor owns); candidate B is the missing selector (the account of what fixes the
joint move's parameter). The phi = 1 filter still applies: a conclusion any register would produce is not
physics.

Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.SupplyGapExperiment

/-! ### GRADUATED (Model/InformationOrder pass)

Into `Model/InformationOrder`, same names: `OperatorFaithful`, `open_operator_faithful`,
`fill_operator_ext_iff`. They sharpen canonical `totalization_not_faithful` rather than repeating it: that one
is about the object, these are about the parameter.

NOT graduated: `fill_operator_not_faithful` follows from `fill_operator_ext_iff` and stays live; the
supply-gap framing results stay live as the record of a negative. -/

/-! ## Part 1: is the supply-gap forced and independent? -/

/-- The parameter is RECOVERABLE when some map reads it back off the outcome, uniformly in the state. -/
def ParamRecoverable {P S T : Type} (f : P → S → T) : Prop := ∃ r : T → P, ∀ p s, r (f p s) = p

/-- The parameter is determined by the whole OPERATOR: distinct parameters act differently somewhere. -/
def OperatorFaithful {P S : Type} (f : P → S → S) : Prop :=
  ∀ p p' : P, (∀ s, f p s = f p' s) → p = p'

/-! ### The build's clause is a triviality -/

/-- **`no_canonical_selector` is below kernel level.** The two-clause form proves only this, and this holds for
an ARBITRARY function of two arguments that is not constant in the first: no actions, no classifications, no
absence, no diagonal. It says that a map into the parameter space is not unique when two parameters differ
somewhere. That is not an incompleteness. -/
theorem no_canonical_selector_trivial {P S T : Type} (f : P → S → T)
    (h : ∃ (p p' : P) (s : S), f p s ≠ f p' s) (σ : S → P) :
    ∃ (σ' : S → P) (s : S), f (σ s) s ≠ f (σ' s) s := by
  obtain ⟨p, p', s₀, hne⟩ := h
  by_cases hc : f (σ s₀) s₀ = f p s₀
  · exact ⟨fun _ => p', s₀, by rw [hc]; exact hne⟩
  · exact ⟨fun _ => p, s₀, hc⟩

/-! ### The real content: recoverability, and where it fails -/

/-- **An absorbing state blocks recovery.** If some state is insensitive to the parameter, the parameter cannot
be read off outcomes. Two lines, no diagonal, no cardinality. -/
theorem absorbing_state_blocks_recovery {P S T : Type} (f : P → S → T) (s₀ : S)
    (hab : ∀ p p' : P, f p s₀ = f p' s₀) (p p' : P) (hne : p ≠ p') : ¬ ParamRecoverable f := by
  rintro ⟨r, hr⟩
  exact hne ((hr p s₀).symm.trans ((congrArg r (hab p p')).trans (hr p' s₀)))

/-- **Unrecoverability is NOT forced for parameterized actions.** A parameterized map whose parameter IS
recoverable exists, so the supply-gap fails the forcedness test the hole and the floor pass: those hold for
every classification and every Member, this holds only for actions with absorbing states. -/
theorem recoverable_action_exists : ParamRecoverable (fun (b : Bool) (_ : Unit) => b) :=
  ⟨id, fun _ _ => rfl⟩

/-! ### Both arms, at both levels -/

theorem partialization_absorbs_at_bot {X : Type} (w : X → X → Bool) :
    partialization w (botC X) = botC X := by
  funext x y; cases hw : w x y <;> simp [partialization, botC, hw]

theorem totalization_absorbs_at_total {X : Type} (s : X → Nat) (c : X → X → Option Bool)
    (h : isTotal c) : totalization s c = c := (totalization_fixed_iff_total s c).2 h

/-- **The open arm's parameter is not recoverable from an outcome**, because the order-bottom absorbs every
mask. -/
theorem open_param_not_recoverable :
    ¬ ParamRecoverable (partialization : (Fin 2 → Fin 2 → Bool) →
        (Fin 2 → Fin 2 → Option Bool) → (Fin 2 → Fin 2 → Option Bool)) := by
  refine absorbing_state_blocks_recovery _ (botC (Fin 2)) ?_ (fun _ _ => false) (fun _ _ => true) ?_
  · intro p p'
    rw [partialization_absorbs_at_bot, partialization_absorbs_at_bot]
  · intro h
    exact absurd (congrFun (congrFun h 0) 0) (by decide)

/-- **The fill arm's parameter is not recoverable from an outcome either**, because every order-maximum absorbs
every scale. Same lemma, different absorbing state: the bottom for one arm, the maxima for the other. -/
theorem fill_param_not_recoverable :
    ¬ ParamRecoverable (totalization : (Fin 2 → Nat) →
        (Fin 2 → Fin 2 → Option Bool) → (Fin 2 → Fin 2 → Option Bool)) := by
  have htot : isTotal (cTrue : Fin 2 → Fin 2 → Option Bool) := fun _ _ => by simp [cTrue]
  refine absorbing_state_blocks_recovery _ cTrue ?_ (fun _ => 0) (fun x => x.val) ?_
  · intro p p'
    rw [totalization_absorbs_at_total p cTrue htot, totalization_absorbs_at_total p' cTrue htot]
  · intro h
    exact absurd (congrFun h 1) (by decide)

/-- **The open arm IS operator-faithful**: the mask is determined by the operator, tested on the all-present
classification. -/
theorem open_operator_faithful {X : Type} : OperatorFaithful
    (partialization : (X → X → Bool) → (X → X → Option Bool) → (X → X → Option Bool)) := by
  intro w w' h
  funext x y
  have hc : (if w x y then none else (some true : Option Bool))
      = (if w' x y then none else (some true : Option Bool)) :=
    congrFun (congrFun (h cTrue) x) y
  cases hw : w x y <;> cases hw' : w' x y
  · rfl
  · rw [hw, hw'] at hc; simp at hc
  · rw [hw, hw'] at hc; simp at hc
  · rfl

/-- **The fill arm is NOT operator-faithful**: two distinct scales act identically on every classification. So
the two arms differ at the operator level. -/
theorem fill_operator_not_faithful :
    ¬ OperatorFaithful (totalization : (Fin 2 → Nat) →
        (Fin 2 → Fin 2 → Option Bool) → (Fin 2 → Fin 2 → Option Bool)) := by
  intro h
  have hne : (fun _ : Fin 2 => 0) ≠ (fun _ : Fin 2 => 1) := by
    intro hc; exact absurd (congrFun hc 0) (by decide)
  refine hne (h _ _ (fun c => ?_))
  funext x y
  simp [totalization]

/-- **The fill arm is faithful exactly up to the induced comparison.** The operator determines the scale's
ordering of the carrier and nothing more, so "who supplies the scale" is partly a non-question: only the
comparison is at stake. -/
theorem fill_operator_ext_iff {X : Type} (s s' : X → Nat) :
    (∀ c : X → X → Option Bool, totalization s c = totalization s' c)
      ↔ ∀ x y, decide (s y ≤ s x) = decide (s' y ≤ s' x) := by
  constructor
  · intro h x y
    have hc : totalization s (botC X) x y = totalization s' (botC X) x y :=
      congrFun (congrFun (h (botC X)) x) y
    simpa [totalization, botC] using hc
  · intro h c
    funext x y
    simp only [totalization, h x y]

/-! ### The tightest shape -/

/-- **The tightest non-trivial form.** The parameter is pinned by the whole operator yet revealed by no single
outcome: determined globally, invisible locally. This is not "non-injective", because operator-faithfulness is
an injectivity requirement, and it is not trivially instantiated. -/
def GenuineSupplyGap {P S : Type} (f : P → S → S) : Prop :=
  OperatorFaithful f ∧ ¬ ParamRecoverable f

/-- **The open arm has a genuine supply gap.** -/
theorem open_has_genuine_gap :
    GenuineSupplyGap (partialization : (Fin 2 → Fin 2 → Bool) →
      (Fin 2 → Fin 2 → Option Bool) → (Fin 2 → Fin 2 → Option Bool)) :=
  ⟨open_operator_faithful, open_param_not_recoverable⟩

/-- **The fill arm does not.** Its parameter is not even pinned by the operator, so there is no determinate
thing left unrecovered: the scale's gap is a quotient, not a hidden datum. The supply-gap is an ARMS-ASYMMETRY
at the operator level, not a uniform condition. -/
theorem fill_lacks_genuine_gap :
    ¬ GenuineSupplyGap (totalization : (Fin 2 → Nat) →
      (Fin 2 → Fin 2 → Option Bool) → (Fin 2 → Fin 2 → Option Bool)) :=
  fun h => fill_operator_not_faithful h.1

/-- **And the outcome-level gap is a corollary of the order's extremes.** Both arms fail recovery, and both
failures come from `absorbing_state_blocks_recovery` applied to canonical structure: the order-bottom for the
open arm, the order-maxima for the fill arm. So within the framework the gap is unavoidable, but it is
DERIVATIVE: it follows from the order having a bottom and having maxima, which are already canonical, and needs
neither the diagonal nor non-degeneracy. -/
theorem gap_is_a_corollary_of_the_extremes :
    (∀ w : Fin 2 → Fin 2 → Bool, partialization w (botC (Fin 2)) = botC (Fin 2))
      ∧ (∀ s : Fin 2 → Nat, totalization s (cTrue : Fin 2 → Fin 2 → Option Bool) = cTrue) := by
  refine ⟨fun w => partialization_absorbs_at_bot w, fun s => ?_⟩
  exact totalization_absorbs_at_total s cTrue (fun _ _ => by simp [cTrue])

/-- **Independent of the floor, and not because it is deeper.** The open arm's gap is exhibited entirely at
`botC`, which is degenerate: the floor has already failed there and the gap is present anyway. Membership plays
no part, so the two conditions are about different things, but that does not make the gap a peer of the
floor. -/
theorem gap_lives_below_the_floor :
    ¬ NonDegenerate (botC (Fin 2)) ∧ (∀ w : Fin 2 → Fin 2 → Bool,
      partialization w (botC (Fin 2)) = botC (Fin 2)) := by
  refine ⟨?_, fun w => partialization_absorbs_at_bot w⟩
  rintro ⟨x, x', hne⟩
  exact hne rfl

/-! ## Part 2: gravity's placement -/

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- Every diagonal cell of a product carrier is a cross cell: no point differs from itself. -/
theorem diagonal_is_cross (a : ∀ k, X k) : ¬ ∃ i, differsInOne a a i := by
  rintro ⟨i, hne, _⟩; exact hne rfl

/-- **Candidate A is available and generic.** The cross region exists and the diagonal lies in it, for every
product carrier and every pair of factors. The statement quantifies over the factors, so no register content
enters: placing gravity here inherits the artifact verdict. -/
theorem cross_region_available (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (a : ∀ k, X k) :
    nary c imp a a = imp a a :=
  nary_apply_imp c imp (diagonal_is_cross a)

/-- **The joint move absorbs**, so candidate B's gap is the same corollary as Part 1's: once the composite is
driven to its pole, no further scale is visible in it. Generic in the composite. -/
theorem joint_fill_absorbs (A : (∀ k, X k) → (∀ k, X k) → Option Bool) (s s' : (∀ k, X k) → Nat) :
    totalization s (totalization s' A) = totalization s' A :=
  totalization_absorbs_at_total s (totalization s' A) (totalization_isTotal s' A)

/-- **The joint parameter is CONSTRAINED on the region cells.** Commutation forces the composite scale to agree
with a per-coordinate scale at every absent differ-in-one cell (canonical). -/
theorem region_cells_constrained (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (h : totalization s (nary c imp) = nary (fun i => totalization (si i) (c i)) (totalization s imp))
    (a b : ∀ i, X i) (hex : ∃ i, differsInOne a b i)
    (hc : c hex.choose (a hex.choose) (b hex.choose) = none) :
    decide (s b ≤ s a) = decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose)) :=
  nary_totalization_commutation_forces_absence_coherence s si c imp h a b hex hc

/-- **And FREE on the cross region.** At a cell differing in no coordinate or in more than one, the commutation
equation holds unconditionally: both sides totalize the same import by the same scale, so no condition on the
parameter arises there. -/
theorem cross_cells_unconstrained (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (si : ∀ i, X i → Nat) (s : (∀ i, X i) → Nat)
    {a b : ∀ i, X i} (hne : ¬ ∃ i, differsInOne a b i) :
    totalization s (nary c imp) a b
      = nary (fun i => totalization (si i) (c i)) (totalization s imp) a b := by
  rw [nary_apply_imp (fun i => totalization (si i) (c i)) (totalization s imp) hne]
  simp only [totalization, nary_apply_imp c imp hne]

/-- **A and B are the same object, seen twice.** The joint move's parameter is bound exactly where the regions
are and free exactly where the cross region is. So "gravity is the territory neither factor owns" and "gravity
is what would select the joint parameter" name one thing: the cross region IS the locus of the selector's
freedom. The two placements collapse. -/
theorem placements_collapse (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (si : ∀ i, X i → Nat) (s : (∀ i, X i) → Nat) :
    (∀ a b : ∀ i, X i, ¬ (∃ i, differsInOne a b i) →
        totalization s (nary c imp) a b
          = nary (fun i => totalization (si i) (c i)) (totalization s imp) a b)
      ∧ (∀ a : ∀ i, X i, nary c imp a a = imp a a) :=
  ⟨fun _ _ hne => cross_cells_unconstrained c imp si s hne, fun a => cross_region_available c imp a⟩

/-! ## THE VERDICTS

PART 1.

INDEPENDENCE. The supply-gap is not derivable from the hole and not derivable from the floor, but neither is it
their peer. The build's clause reduces to `no_canonical_selector_trivial`, which holds for an arbitrary
two-argument function that is not constant in its first argument: no diagonal, no classification, no absence.
The real content, `¬ ParamRecoverable`, reduces to `absorbing_state_blocks_recovery`, a two-line argument from
the existence of a parameter-insensitive state. Both are below the hole, not beside it.

FORCEDNESS. It is NOT forced. `recoverable_action_exists` gives a parameterized action whose parameter is
recoverable, so unrecoverability is a property of particular actions, not of parameterized action as such. The
hole holds for every classification and the floor is required of every Member; the supply-gap holds only where
an absorbing state exists. Within the framework it is nonetheless unavoidable, because both arms have one
(`gap_is_a_corollary_of_the_extremes`): the order-bottom absorbs every mask, every order-maximum absorbs every
scale. So it is UNAVOIDABLE BUT DERIVATIVE, a corollary of the order having a bottom and having maxima. It is
not a third kernel condition and this file does not manufacture one.

ARMS-ASYMMETRY. The two arms differ, and the asymmetry is at the operator level, not the outcome level. The
open arm is operator-faithful (`open_operator_faithful`) and its parameter is invisible in outcomes
(`open_param_not_recoverable`), so it has the tightest form of the gap (`open_has_genuine_gap`). The fill arm is
not operator-faithful (`fill_operator_not_faithful`): distinct scales are the same operator, and
`fill_operator_ext_iff` says the operator determines exactly the induced comparison. So the fill arm has no
determinate hidden datum to fail to recover; its gap is a quotient (`fill_lacks_genuine_gap`). The framework's
silence is usually told about the scale, and at the sharpest reading it is the MASK that has the genuine gap.

THE SHAPE. The tightest non-trivial form is `GenuineSupplyGap`: operator-faithful and outcome-unrecoverable.
It is not "just non-injective", because operator-faithfulness is an injectivity REQUIREMENT that the fill arm
fails. It is a genuine structural predicate, and exactly one of the two arms satisfies it.

PART 2.

CANDIDATE A is available and generic. `cross_region_available` quantifies over the factors, so the placement
inherits the artifact verdict already recorded: any two-register assemblage on any product carrier has the same
cross region carrying the same diagonal.

CANDIDATE B is generic too, and by Part 1's verdict it is also derivative. `joint_fill_absorbs` shows the joint
move's gap is the same absorbing-state corollary, with no term from the two-carrier structure. Gravity-as-
selector is the generic gap.

THE DISCRIMINATOR: THEY COLLAPSE. `placements_collapse` locates the joint parameter's constraint exactly on the
region cells (`region_cells_constrained`) and its freedom exactly on the cross region
(`cross_cells_unconstrained`). The cross region IS where the unrecoverable parameter would have to act. So A
and B are one object seen statically and dynamically, not two competing placements.

THE FILTER. Neither placement uses the forced two-member structure. That forcing is about CARRIERS, that no one
carrier both fixes and varies the background; nothing in the cross-region fact or the supply-gap fact mentions
any carrier property, and both are stated with the factors universally quantified. The one physics result that
survived the earlier filter does not reach the placement question. Both placements are ARTIFACTS.

WHAT REMAINS OPEN

1. `GenuineSupplyGap` is satisfied by the open arm. Whether it is satisfied by anything else in the framework,
   and whether the class of actions satisfying it has a characterization, is not measured.
2. The fill arm's quotient (scales modulo induced comparison) is a genuine parameter space. Whether THAT
   quotient has a genuine supply gap, and whether it is operator-faithful by construction, is not built here.
3. The collapse of A and B is proved as a co-location of constraint and freedom. Whether some finer reading
   separates them again, for instance by asking where the parameter's EFFECT lands rather than where its
   freedom lies, is not tested.
4. Nothing here is graduated, and the corollary verdict is the reason: a derived fact does not join the
   articulation set. -/

#print axioms no_canonical_selector_trivial
#print axioms absorbing_state_blocks_recovery
#print axioms recoverable_action_exists
#print axioms partialization_absorbs_at_bot
#print axioms totalization_absorbs_at_total
#print axioms open_param_not_recoverable
#print axioms fill_param_not_recoverable
#print axioms open_operator_faithful
#print axioms fill_operator_not_faithful
#print axioms fill_operator_ext_iff
#print axioms open_has_genuine_gap
#print axioms fill_lacks_genuine_gap
#print axioms gap_is_a_corollary_of_the_extremes
#print axioms gap_lives_below_the_floor
#print axioms diagonal_is_cross
#print axioms cross_region_available
#print axioms joint_fill_absorbs
#print axioms region_cells_constrained
#print axioms cross_cells_unconstrained
#print axioms placements_collapse

end Chiralogy.SupplyGapExperiment
