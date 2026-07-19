import Chiralogy.Protocol.Membership
import Chiralogy.Model.Boundary
import Mathlib.Tactic.DeriveFintype

/-! # Register: a type system (at a level)   [READING]

The framework's second register and its first at a level. Physics sits at the base with one ground and a
binary lattice; this register classifies terms into a level with three grounds of absence, and its inherited
structure does recognisable work.

The three grounds are IMPORTED domain content: a term may have no type because it is ill-formed (syntax or
scoping), because inference does not resolve (no principal type, a constraint unsolved), or because checking
would diverge (type-level evaluation not terminating). The conformance and inheritance are THEOREMS; the
grounds' prerequisite order, the placement of the language stances, and the readings of the permitted moves are
READINGS with defeasible mappings, stated not asserted (`def : Prop`), as the physics register states its
fidelity. No claim is made about type theory beyond what the register carries. -/

namespace Chiralogy.TypeSystem

/-- The three grounds of untypedness, IMPORTED. -/
inductive TypeGround | illFormed | unresolved | divergent
  deriving DecidableEq, Fintype

/-- The classification: four terms, a typed one and one per ground, so each ground is reached and distinct. -/
def typeClassify : Fin 4 → Fin 4 → Bool ⊕ TypeGround := fun x _ =>
  if x = 0 then Sum.inl true
  else if x = 1 then Sum.inr .illFormed
  else if x = 2 then Sum.inr .unresolved
  else Sum.inr .divergent

/-- **The type register**: carrier of terms, classification into a three-ground level. -/
def typeRegister : Member where
  X := Fin 4
  B := Bool ⊕ TypeGround
  canDiffer := ⟨Sum.inl true, Sum.inr .illFormed, by decide⟩
  classify := typeClassify
  nondegenerate := ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩

/-- **Three genuinely distinct grounds.** Each ground is reached by a term, there is a typed verdict, and the
three grounds are pairwise distinct: three grounds, not one tripled. -/
theorem three_grounds_reachable_distinct :
    typeClassify 1 0 = Sum.inr TypeGround.illFormed
    ∧ typeClassify 2 0 = Sum.inr TypeGround.unresolved
    ∧ typeClassify 3 0 = Sum.inr TypeGround.divergent
    ∧ typeClassify 0 0 = Sum.inl true
    ∧ TypeGround.illFormed ≠ TypeGround.unresolved
    ∧ TypeGround.unresolved ≠ TypeGround.divergent
    ∧ TypeGround.illFormed ≠ TypeGround.divergent :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide, by decide⟩

/-- **Conforms and inherits.** The register passes the unchanged protocol and the payload fires; it inherits
the level's structure by conforming: `2 ^ 3 - 1 = 7` permitted totalizations (via the general count), three
reasons, one prohibition. -/
theorem conforms_and_inherits :
    ¬ Function.Surjective typeRegister.classify
    ∧ (Finset.univ.filter (fun close : TypeGround → Bool => ¬ ∀ g, close g = true)).card = 2 ^ 3 - 1
    ∧ (Finset.univ.filter (fun close : TypeGround → Bool => ∀ g, close g = true)).card = 1
    ∧ Fintype.card TypeGround = 3 := by
  refine ⟨payload typeRegister, ?_, by decide, by decide⟩
  have h := (permitted_lattice_from_reason_count TypeGround).2
  rwa [show Fintype.card TypeGround = 3 from by decide] at h

/-! ## The readings (defeasible, stated not asserted)

The grounds and stances are IMPORTED; each mapping below is a reading, a `def : Prop` stated as the physics
register states its fidelity, not a theorem. -/

/-- A closure is coherent when it respects the prerequisite order: closing inference presupposes
well-formedness, closing divergence presupposes inference. -/
abbrev coherent (close : TypeGround → Bool) : Prop :=
  (close .unresolved = true → close .illFormed = true)
  ∧ (close .divergent = true → close .unresolved = true)

/-- The dynamic stance: close nothing. -/
def stanceDynamic : TypeGround → Bool := fun _ => false

/-- The partial-but-typed stance: close ill-formedness and inference, leave divergence open. -/
def stancePartialInfer : TypeGround → Bool
  | .divergent => false
  | _ => true

/-- The totality stance: close every ground. -/
def stanceTotal : TypeGround → Bool := fun _ => true

/-- **The grounds are ordered** (READING, defeasible). The grounds carry a prerequisite order, IMPORTED:
closing inference alone or divergence alone is incoherent, each presupposing an earlier ground. Stated, not
asserted. -/
def grounds_are_ordered : Prop :=
  (¬ coherent (fun g => decide (g = TypeGround.unresolved)))
    ∧ (¬ coherent (fun g => decide (g = TypeGround.divergent)))

/-- **The three stances are three closures** (READING, defeasible). Three imported language stances, dynamic,
partial-but-typed, and total, land on three distinct closures; the first two are permitted, the totality ideal
lands on the full closure, the prohibition. Stated, not asserted. -/
def three_stances_are_three_closures : Prop :=
  stanceDynamic ≠ stancePartialInfer ∧ stancePartialInfer ≠ stanceTotal ∧ stanceDynamic ≠ stanceTotal
    ∧ (¬ ∀ g, stanceDynamic g = true) ∧ (¬ ∀ g, stancePartialInfer g = true) ∧ (∀ g, stanceTotal g = true)

/-- **The readings of the permitted** (READING, defeasible). Three of the seven permitted moves are coherent and
read as positions; the other four would close a later ground while leaving an earlier one open, incoherent, not
merely unread. Stated, not asserted. -/
def readings_of_the_permitted : Prop :=
  (Finset.univ.filter (fun close : TypeGround → Bool => coherent close ∧ ¬ ∀ g, close g = true)).card = 3
    ∧ (Finset.univ.filter (fun close : TypeGround → Bool => ¬ ∀ g, close g = true)).card = 7

end Chiralogy.TypeSystem
