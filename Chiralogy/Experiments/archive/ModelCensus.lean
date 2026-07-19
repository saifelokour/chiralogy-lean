import Chiralogy

/-! # Experiment: the model tower's census and composition law

`Kl(Maybe)` is a base with Writer above it (`memLevel`). Census which monads sit above `Maybe` as levels,
what each buys, whether the kernel survives, then test whether their composition is additive or
order-dependent. The literature: only ranked monads admit canonical transformers (State, Writer, Reader,
Exception); ordering matters (StateT over ExceptT differs from ExceptT over StateT), while two StateTs commute;
nondeterminism can fail (Bowler, Zwart).

The tower machinery is re-derived locally (the experiments are not compiled). Stays in `Experiments/`;
canonical untouched; nothing about P vs NP resolved. -/

open Chiralogy

namespace Chiralogy.ModelCensus

@[ext] structure TowerLevel (A B : Type) where
  emb : A → B
  ret : B → A
  sec : Function.LeftInverse ret emb

/-! ## Part 1: the census

Each candidate is a level over the apophatic distinction space `Option Bool`, with section, retraction, and
surplus. Writer is `memLevel` (done). Below: Reader, State, Except. For each, the kernel survives, the hole
firing at the extended codomain with a fixed-point-free endomap; the verdict stays uniform. -/

/-- **Reader** (context `Bool`): buys context-dependence. Surplus: classifications varying with context. -/
def readerLevel : TowerLevel (Option Bool) (Bool → Option Bool) :=
  ⟨fun b _ => b, fun f => f true, fun _ => rfl⟩

theorem kernel_survives_reader {X : Type} (c : X → X → (Bool → Option Bool)) :
    ¬ Function.Surjective c :=
  no_reflexive_object (g := fun f s => optCycle (f s))
    (fun f h => optCycle_fixedpointfree (f true) (congrFun h true)) c

/-- **State** (state `Bool`): buys readable memory, the classification consulting its history. Surplus:
state-dependent verdicts. -/
def stateLevel : TowerLevel (Option Bool) (Bool → Option Bool × Bool) :=
  ⟨fun b s => (b, s), fun f => (f true).1, fun _ => rfl⟩

theorem kernel_survives_state {X : Type} (c : X → X → (Bool → Option Bool × Bool)) :
    ¬ Function.Surjective c :=
  no_reflexive_object (g := fun f s => (optCycle (f s).1, (f s).2))
    (fun f h => optCycle_fixedpointfree (f true).1 (congrArg Prod.fst (congrFun h true))) c

/-- **Except** (reasons `Bool`): buys reasons for absence. `Maybe` has one absence; `Except` has many (the
non-singular version of 5.a.2). Verdict maps to `inl`, absence to a chosen reason `inr false`. -/
def exEmb : Option Bool → Bool ⊕ Bool
  | some b => Sum.inl b
  | none => Sum.inr false

def exRet : Bool ⊕ Bool → Option Bool
  | Sum.inl b => some b
  | Sum.inr _ => none

def exceptLevel : TowerLevel (Option Bool) (Bool ⊕ Bool) :=
  ⟨exEmb, exRet, fun o => by cases o <;> rfl⟩

/-- **The surplus of Except: the other reasons.** `inr true` is an absence-reason outside the image: many
reasons where `Maybe` had one. -/
theorem except_surplus : ∀ o, exEmb o ≠ Sum.inr true := by decide

/-- A fixed-point-free endomap on the Except codomain: flip verdicts, send reasons to a verdict. -/
def exCycle : Bool ⊕ Bool → Bool ⊕ Bool
  | Sum.inl b => Sum.inl !b
  | Sum.inr _ => Sum.inl true

/-- **The kernel survives Except.** The hole fires though the codomain carries many reasons: carrying reasons
does not make the guard discriminate, since the hole is about surjectivity, not the codomain's content. -/
theorem kernel_survives_except {X : Type} (c : X → X → (Bool ⊕ Bool)) :
    ¬ Function.Surjective c :=
  no_reflexive_object (g := exCycle) (by decide) c

/-! ## Part 2: the composition law

Monad transformers are the first candidate for a non-additive composition. The section abstraction is too
coarse to see effect-ordering (section composition is function composition, additive), so the ordering is
tested on the transformer types directly. `StateT S (Except E) A = S → E ⊕ (A × S)` loses the state on
failure; `ExceptT E (State S) A = S → (E ⊕ A) × S` keeps it. -/

abbrev StateOverExcept : Type := Bool → Unit ⊕ (Bool × Bool)
abbrev ExceptOverState : Type := Bool → (Unit ⊕ Bool) × Bool

/-- **State and Except do not commute.** The two orderings give types of different cardinality (25 versus 36),
so they are not isomorphic: state lost on failure versus state preserved. The first non-commutative
composition in the framework, shown on the term. -/
theorem state_except_does_not_commute :
    Fintype.card StateOverExcept ≠ Fintype.card ExceptOverState := by
  simp only [StateOverExcept, ExceptOverState, Fintype.card_fun, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_bool, Fintype.card_unit]
  norm_num

abbrev StateOverState : Type := Bool → Fin 3 → (Unit × Bool) × Fin 3
abbrev StateOverState' : Type := Fin 3 → Bool → (Unit × Fin 3) × Bool

/-- **Two States commute.** Reordering two State layers preserves cardinality (both 46656): consistent with
the isomorphism the literature notes. The non-commutativity is selective, not global. -/
theorem state_state_commutes :
    Fintype.card StateOverState = Fintype.card StateOverState' := by
  simp only [StateOverState, StateOverState', Fintype.card_fun,
    Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Fintype.card_unit]
  norm_num

/-! ## Part 3: nondeterminism -/

/-- **List** is a lawful section: embed as a singleton, retract as the head. Surplus: lists of length not one
(plurality). -/
def listLevel : TowerLevel (Option Bool) (List (Option Bool)) :=
  ⟨fun b => [b], fun l => l.headI, fun _ => rfl⟩

/-- **The kernel survives List.** Prepending gives a fixed-point-free endomap; the hole fires on the plural
codomain. The literature's no-go (list does not distribute over itself, Zwart) is at the monad-multiplication
level, finer than the section, so the tower does not see it: List is a lawful level, its pathology invisible
here. -/
theorem kernel_survives_list {X : Type} (c : X → X → List (Option Bool)) :
    ¬ Function.Surjective c :=
  no_reflexive_object (g := fun l => none :: l)
    (fun l h => by simpa using congrArg List.length h) c

/-! ## The verdict

Part 1: the census. Reader, State, Except each give a genuine section/retraction level over `Option Bool`
(`readerLevel`, `stateLevel`, `exceptLevel`), with nonempty surplus (context-varying, state-dependent, extra
reasons, `except_surplus`). The kernel survives each (`kernel_survives_reader`, `_state`, `_except`): the hole
fires at every extended codomain, and Except's many reasons do not make the guard discriminate.

Part 2: the composition law is non-commutative, selectively. State over Except and Except over State have
different cardinality (`state_except_does_not_commute`, 25 versus 36), so they are non-isomorphic: the first
non-additive composition in the framework, shown on the term, not cited. Two States commute
(`state_state_commutes`, both 46656). The grade is not blind to the order: the composite cardinalities differ
(25 versus 36), so the cardinality-gap grade differs by order too (22 versus 33). Section composition of a
chain still telescopes additively, but effect-stacking is order-dependent, and the grade records it.

Part 3: List is a lawful section level (`listLevel`, `kernel_survives_list`), not a tower no-go. The
literature's failure of nondeterminism is at the monad-distribution level, which the section abstraction does
not test, so the pathology is invisible here rather than a level failure.

The verdict: the model tower's census is Reader, State, Except, Writer, and List, each a genuine level with a
surviving kernel; and its composition law is non-commutative for state and exceptions, the first non-additive
composition in the framework. Nothing here is about P vs NP; no complexity class, no separation. -/

end Chiralogy.ModelCensus
