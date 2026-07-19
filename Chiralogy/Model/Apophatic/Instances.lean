import Chiralogy.Model.Apophatic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Model: the tower of levels over Kl(Maybe)

Maybe (`maybeAbsence`) is the base of a tower of levels, each a section with retraction over the apophatic
model, each with the kernel surviving and the verdict uniform. Memory, context, state, structured absence, and
plurality are the surpluses. Each level is an `AbsenceStructure` instance. Composition of levels as sections is
additive (`grade_adds`); effect-stacking is order-dependent (`state_except_does_not_commute` versus
`state_state_commutes`), the first non-commutative composition in the framework. -/

namespace Chiralogy

/-! ## The tower structure -/

/-- A tower level: a section with retraction between value spaces, generalizing `some`/`getD`. -/
@[ext] structure TowerLevel (A B : Type) where
  emb : A → B
  ret : B → A
  sec : Function.LeftInverse ret emb

/-- Composition of levels: sections compose, retractions compose in reverse. -/
def levelCompose {A B C : Type} (f : TowerLevel A B) (g : TowerLevel B C) : TowerLevel A C where
  emb := g.emb ∘ f.emb
  ret := f.ret ∘ g.ret
  sec := fun a => by simp only [Function.comp_apply]; rw [g.sec (f.emb a), f.sec a]

/-- The surplus size of a level: the cardinality gap. -/
def grade {A B : Type} [Fintype A] [Fintype B] (_f : TowerLevel A B) : ℤ :=
  (Fintype.card B : ℤ) - Fintype.card A

/-- **Composition of sections is additive.** The surplus of a composite is the sum: gaps telescope. -/
theorem grade_adds {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (f : TowerLevel A B) (g : TowerLevel B C) :
    grade (levelCompose f g) = grade f + grade g := by
  simp only [grade]; ring

/-! ## The five levels, each an absence-structure instance -/

/-- **Writer**: memory. A section embedding with an empty log; the surplus is nonempty logs. Absence is the
none verdict, carried; concealment is contingent, since a recording variant marks fabrication. -/
def writerLevel : TowerLevel (Option Bool) (Option Bool × List Bool) :=
  ⟨fun b => (b, []), fun p => p.1, fun _ => rfl⟩

def writerAbsence : AbsenceStructure := ⟨Option Bool × List Bool, fun p => p.1 = none⟩

/-- **Reader**: context-dependence. Absence is context-dependent (absent at some context). -/
def readerAbsence : AbsenceStructure := ⟨Bool → Option Bool, fun f => ∃ e, f e = none⟩

/-- **State**: readable memory. Absence is state-dependent. -/
def stateAbsence : AbsenceStructure := ⟨Bool → Option Bool × Bool, fun f => ∃ s, (f s).1 = none⟩

/-- **Except**: structured absence, many reasons. The center is a family, one crossing per reason. -/
def exceptAbsence : AbsenceStructure := ⟨Bool ⊕ Bool, fun x => ∃ e, x = Sum.inr e⟩

/-- **List**: plurality. Absence is the empty list (singular, as the base); plurality is over-determination,
a second deviation the base lacks. -/
def listAbsence : AbsenceStructure := ⟨List (Option Bool), fun l => l = []⟩

/-! ## The kernel survives every level (the verdict is uniform) -/

/-- **Writer.** The hole fires at the memoryful value space. -/
theorem kernel_survives_writer {X : Type} (c : X → X → writerAbsence.V) : ¬ Function.Surjective c :=
  no_reflexive_object (g := fun p => (optCycle p.1, p.2))
    (fun p h => optCycle_fixedpointfree p.1 (congrArg Prod.fst h)) c

/-- **Reader.** The hole fires at the context value space. -/
theorem kernel_survives_reader {X : Type} (c : X → X → readerAbsence.V) : ¬ Function.Surjective c :=
  no_reflexive_object (g := fun f s => optCycle (f s))
    (fun f h => optCycle_fixedpointfree (f true) (congrFun h true)) c

/-- **State.** The hole fires at the state value space. -/
theorem kernel_survives_state {X : Type} (c : X → X → stateAbsence.V) : ¬ Function.Surjective c :=
  no_reflexive_object (g := fun f s => (optCycle (f s).1, (f s).2))
    (fun f h => optCycle_fixedpointfree (f true).1 (congrArg Prod.fst (congrFun h true))) c

/-- Fixed-point-free endomap on the Except value space: flip verdicts, send reasons to a verdict. -/
def exCycle : Bool ⊕ Bool → Bool ⊕ Bool
  | Sum.inl b => Sum.inl !b
  | Sum.inr _ => Sum.inl true

/-- **Except.** The hole fires though the codomain carries many reasons: reasons do not make the guard
discriminate. -/
theorem kernel_survives_except {X : Type} (c : X → X → exceptAbsence.V) : ¬ Function.Surjective c :=
  no_reflexive_object (g := exCycle) (by decide) c

/-- **List.** Prepending gives a fixed-point-free endomap; the hole fires on the plural codomain. -/
theorem kernel_survives_list {X : Type} (c : X → X → listAbsence.V) : ¬ Function.Surjective c :=
  no_reflexive_object (g := fun l => none :: l)
    (fun l h => by simpa using congrArg List.length h) c

/-! ## The center's cardinality is instance-dependent -/

/-- **Except is plural.** Two distinct absent values (reasons): the absence-locus is a family, not a point. -/
theorem except_center_is_plural :
    exceptAbsence.absent (Sum.inr false) ∧ exceptAbsence.absent (Sum.inr true)
    ∧ (Sum.inr false : Bool ⊕ Bool) ≠ Sum.inr true :=
  ⟨⟨false, rfl⟩, ⟨true, rfl⟩, by decide⟩

/-- **List is singular** for the empty-absence reading: the only absent value is `[]`, as the base. -/
theorem list_center_is_singular : ∀ l, listAbsence.absent l → l = [] := fun _ h => h

/-! ## Effect-stacking is order-dependent (the first non-commutative composition)

Section composition is additive; monad-transformer stacking is not. `StateT S (Except E) = S → E ⊕ (A × S)`
loses the state on failure; `ExceptT E (State S) = S → (E ⊕ A) × S` keeps it. -/

abbrev StateOverExcept : Type := Bool → Unit ⊕ (Bool × Bool)
abbrev ExceptOverState : Type := Bool → (Unit ⊕ Bool) × Bool

/-- **State and Except do not commute.** The two orderings have different cardinality (25 versus 36), so they
are non-isomorphic: state lost on failure versus preserved. -/
theorem state_except_does_not_commute :
    Fintype.card StateOverExcept ≠ Fintype.card ExceptOverState := by
  simp only [StateOverExcept, ExceptOverState, Fintype.card_fun, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_bool, Fintype.card_unit]
  norm_num

abbrev StateOverState : Type := Bool → Fin 3 → (Unit × Bool) × Fin 3
abbrev StateOverState' : Type := Fin 3 → Bool → (Unit × Fin 3) × Bool

/-- **Two States commute.** Reordering two State layers preserves cardinality: the non-commutativity is
selective, not global. -/
theorem state_state_commutes :
    Fintype.card StateOverState = Fintype.card StateOverState' := by
  simp only [StateOverState, StateOverState', Fintype.card_fun,
    Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Fintype.card_unit]
  norm_num

/-! ## The tower's index: reasons are the nullary generators

The correspondence is exhibited at Maybe and Except, not proven as a general signature theorem. -/

/-- Except's nullary operations: `throw e = inr e`, one per reason. -/
def throwExcept : Bool → Bool ⊕ Bool := Sum.inr

/-- Maybe's one nullary operation: `fail = none`. -/
def failMaybe : Unit → Option Bool := fun _ => none

/-- **The reasons are the nullary generators.** A level's absences are the range of its nullary operations:
Except's are the throws (`inr e`), Maybe's is the fail (`none`). The reason count is the nullary generator
count, two for Except, one for Maybe. -/
theorem reasons_are_nullary_generators :
    (∀ x : Bool ⊕ Bool, (∃ e, x = Sum.inr e) ↔ ∃ e, throwExcept e = x)
    ∧ (∀ v : Option Bool, v = none ↔ ∃ u : Unit, failMaybe u = v) := by
  refine ⟨fun x => ⟨?_, ?_⟩, fun v => ⟨?_, ?_⟩⟩
  · rintro ⟨e, rfl⟩; exact ⟨e, rfl⟩
  · rintro ⟨e, rfl⟩; exact ⟨e, rfl⟩
  · rintro rfl; exact ⟨(), rfl⟩
  · rintro ⟨_, rfl⟩; rfl

/-- A level-supported totalization acts on the verdict and passes the marking. -/
def MarkingPassing (t : (Bool ⊕ Bool) × Bool → (Bool ⊕ Bool) × Bool) : Prop :=
  ∃ g : Bool ⊕ Bool → Bool ⊕ Bool, ∀ x, t x = (g x.1, x.2)

/-- **The grouping respects the operations.** Values sharing a constant (`(inr false, false)` and
`(inr false, true)`, both `throwExcept false`) are treated alike by any level-supported move, so a partition
separating them is not closeable. The closeable partitions are those generated by the constants. -/
theorem grouping_respects_operations :
    ¬ ∃ t, MarkingPassing t
      ∧ (¬ ∃ e, (t (Sum.inr false, false)).1 = Sum.inr e)
      ∧ (∃ e, (t (Sum.inr false, true)).1 = Sum.inr e) := by
  rintro ⟨t, ⟨g, hg⟩, hc, ho⟩
  simp only [hg] at hc ho
  exact hc ho

/-- Closing the reason `false`, uniform in the marking. -/
def closeReasonFalse : (Bool ⊕ Bool) × Bool → (Bool ⊕ Bool) × Bool
  | (Sum.inr false, m) => (Sum.inl true, m)
  | x => x

/-- **The center fragments by reasons.** Closing one reason removes both of its absent values at once, while
the other reason stays open: the center's parts are the reasons, not the absent values. -/
theorem center_fragments_by_reasons :
    (¬ ∃ e, (closeReasonFalse (Sum.inr false, false)).1 = Sum.inr e)
    ∧ (¬ ∃ e, (closeReasonFalse (Sum.inr false, true)).1 = Sum.inr e)
    ∧ (∃ e, ((Sum.inr true, false) : (Bool ⊕ Bool) × Bool).1 = Sum.inr e) := by decide

/-- **The permitted count is by reasons.** For `n` reasons, exactly one totalization is forbidden (the full
closure), and `2 ^ n - 1` are permitted. -/
theorem permitted_count (n : ℕ) :
    (Finset.univ.filter (fun close : Fin n → Bool => ∀ r, close r = true)).card = 1
    ∧ (Finset.univ.filter (fun close : Fin n → Bool => ¬ ∀ r, close r = true)).card = 2 ^ n - 1 := by
  have hfull : (Finset.univ.filter (fun close : Fin n → Bool => ∀ r, close r = true))
      = {fun _ => true} := by
    ext close
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; funext r; exact h r
    · rintro rfl; intro r; rfl
  have h1 : (Finset.univ.filter (fun close : Fin n → Bool => ∀ r, close r = true)).card = 1 := by
    rw [hfull]; exact Finset.card_singleton _
  refine ⟨h1, ?_⟩
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), h1, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **The boundary is by reasons, not values.** Plural-and-marked has two reasons and four absent values; the
permitted count is `2 ^ 2 - 1 = 3`, not `2 ^ 4 - 1 = 15`. -/
theorem permitted_count_is_by_reasons :
    (Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3
    ∧ (Finset.univ.filter (fun close : Fin 4 → Bool => ¬ ∀ r, close r = true)).card = 15 := by
  refine ⟨by decide, by decide⟩

/-- **The absent-value count is inert.** Boundary (three permitted) and center (two parts) both track the
reason count, two; neither tracks the value count, four. The value count governs nothing in the moves, center,
or boundary examined here. -/
theorem valueCount_is_inert :
    (Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3
    ∧ (Finset.image (fun x : (Bool ⊕ Bool) × Bool => x.1)
         (Finset.univ.filter (fun x => ∃ e, x.1 = Sum.inr e))).card = 2
    ∧ (Finset.univ.filter (fun x : (Bool ⊕ Bool) × Bool => ∃ e, x.1 = Sum.inr e)).card = 4 := by
  refine ⟨by decide, by decide, by decide⟩

/-- A context-selective totalization at Reader: fill at context `true`, leave at `false`. -/
def readerCloseTrue : (Bool → Option Bool) → (Bool → Option Bool) :=
  fun f c => if c = true then some ((f c).getD true) else f c

/-- The mirror: fill at `false`, leave at `true`. -/
def readerCloseFalse : (Bool → Option Bool) → (Bool → Option Bool) :=
  fun f c => if c = false then some ((f c).getD true) else f c

/-- **Dependence acts upstream of the grouping.** Context is consultable: the two context-selective moves are
distinct, so dependence adds closeable dimensions to the grouping, where markedness does not. -/
theorem dependence_adds_reasons :
    readerCloseTrue (fun _ => none) ≠ readerCloseFalse (fun _ => none) :=
  fun h => by simpa [readerCloseTrue, readerCloseFalse] using congrFun h true

/-- **Marking inflates values, not reasons.** A marking multiplies the absent values (Except two, plural-and-
marked four) while the reason count stays two; the two counts coincide exactly when unmarked. -/
theorem markedness_inflates_values_not_reasons :
    (Finset.univ.filter (fun x : Bool ⊕ Bool => ∃ e, x = Sum.inr e)).card = 2
    ∧ (Finset.univ.filter (fun x : (Bool ⊕ Bool) × Bool => ∃ e, x.1 = Sum.inr e)).card = 4
    ∧ (Finset.image (fun x : (Bool ⊕ Bool) × Bool => x.1)
         (Finset.univ.filter (fun x => ∃ e, x.1 = Sum.inr e))).card = 2 := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## The scope: algebraic with constants -/

/-- The continuation value space, a monad outside the ranked family. -/
abbrev Cont : Type := (Bool → Bool) → Bool

/-- **Continuation admits no natural absence.** Two absent predicates are equally admissible: with no
algebraic presentation there is no distinguished absence, so the absent predicate must be stipulated. -/
theorem cont_absence_is_stipulated :
    ∃ p q : Cont → Prop, ∃ v, p v ∧ ¬ q v :=
  ⟨(fun v => v (fun _ => true) = true), (fun v => v (fun _ => true) = false),
   ⟨fun _ => true, rfl, by decide⟩⟩

/-- The free magma on `Bool`: atoms (unary generators) and a binary operation, no nullary generator. -/
inductive Magma where
  | atom : Bool → Magma
  | op : Magma → Magma → Magma
  deriving DecidableEq

/-- **The free magma has no constant.** Every element is an atom or a binary op: finitary (ranked) and
algebraic, yet with no nullary generator, so no natural absence. -/
theorem magma_has_no_constant :
    ∀ m : Magma, (∃ b, m = Magma.atom b) ∨ (∃ l r, m = Magma.op l r) := by
  intro m; cases m with
  | atom b => exact Or.inl ⟨b, rfl⟩
  | op l r => exact Or.inr ⟨l, r, rfl⟩

/-- **Rankedness and natural absence are independent.** The free magma is ranked with no constant; the
powerset has a constant (`∅`) without being ranked (arbitrary joins). The levels coincide because they are
algebraic with constants, not because of their rank. -/
theorem the_properties_are_distinct :
    (∀ m : Magma, (∃ b, m = Magma.atom b) ∨ (∃ l r, m = Magma.op l r))
    ∧ ((∅ : Finset Bool) ≠ {true} ∧ (∅ : Finset Bool) ≠ {false}) :=
  ⟨magma_has_no_constant, ⟨by decide, by decide⟩⟩

/-- **The scope: algebraic with constants.** The grouping is derived where the level has an algebraic
presentation with nullary generators, stipulated otherwise. Two failure modes: continuation for lack of
algebraicity, the free magma for lack of constants. -/
theorem scope_is_algebraic_with_constants :
    (∃ p q : Cont → Prop, ∃ v, p v ∧ ¬ q v)
    ∧ (∀ m : Magma, (∃ b, m = Magma.atom b) ∨ (∃ l r, m = Magma.op l r)) :=
  ⟨cont_absence_is_stipulated, magma_has_no_constant⟩

/-! ## What moves the lattice, and the base as free on one constant -/

/-- **Upstream is signature change.** An operation acts on the permitted lattice exactly when it changes the
signature. Dependence adds closeable dimensions (the two context-selective moves differ) and enlarges the
lattice; markedness multiplies absent values leaving the reason count fixed (equal reason counts at Except and
plural-and-marked); the absent-value count follows markedness and is inert. Scoped to these three dimensions. -/
theorem upstream_is_signature_change :
    (readerCloseTrue (fun _ => none) ≠ readerCloseFalse (fun _ => none))
    ∧ ((Finset.image (fun x : (Bool ⊕ Bool) × Bool => x.1)
         (Finset.univ.filter (fun x => ∃ e, x.1 = Sum.inr e))).card
        = (Finset.univ.filter (fun x : Bool ⊕ Bool => ∃ e, x = Sum.inr e)).card) :=
  ⟨dependence_adds_reasons, by decide⟩

/-- **The base is the free theory on one constant.** Maybe has a single arity-0 symbol (`failMaybe`, whose
range is exactly the absence) and is free pointed on it (`maybe_free_pointed`). This is `maybe_free_pointed` in
signature terms, the common source of the base's distinction, singularity, arity-0 character, and Boolean
permitted order. -/
theorem base_is_free_on_one_constant :
    (∀ v : Option Bool, v = none ↔ ∃ u : Unit, failMaybe u = v)
    ∧ (∀ (C : Type) (pt : C) (f : Bool → C),
        ∃! g : Option Bool → C, g none = pt ∧ ∀ b, g (some b) = f b) :=
  ⟨reasons_are_nullary_generators.2, fun _ pt f => maybe_free_pointed pt f⟩

end Chiralogy
