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

end Chiralogy
