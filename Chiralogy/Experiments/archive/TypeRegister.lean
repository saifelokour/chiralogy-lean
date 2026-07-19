import Chiralogy
import Mathlib.Tactic.DeriveFintype

/-! # Experiment: a type-system register at a level

Physics sits at the base with one ground. A type system offers three distinguishable grounds and would be the
first register at a level whose inherited lattice does recognisable work. Build it and test whether the reading
survives being made precise.

The three grounds are IMPORTED domain content: a term may have no type because it is ill-formed (syntax or
scoping), because inference fails to resolve (no principal type, a constraint left unsolved), or because
checking would diverge (type-level evaluation not terminating). The language stances are IMPORTED: a
totality-requiring checker closes divergence, a partial-but-typed system closes inference and leaves divergence
open, a dynamic system closes nothing. No claim is made about type theory beyond what the register carries; the
entailment is a theorem, the grounds and stances imported, each mapping fidelity a READING. Stays in
`Experiments/`; canonical untouched; the protocol is not extended; nothing resolved. -/

open Chiralogy

namespace Chiralogy.TypeRegister

/-- The three grounds of untypedness, IMPORTED as domain content. -/
inductive TypeGround | illFormed | unresolved | divergent
  deriving DecidableEq, Fintype

/-! ## Part 1: the register -/

/-- The classification: four terms, one well-typed and one per ground, so each ground is reachable and the
three are distinct (not one absence tripled). -/
def typeClassify : Fin 4 → Fin 4 → Bool ⊕ TypeGround := fun x _ =>
  if x = 0 then Sum.inl true
  else if x = 1 then Sum.inr .illFormed
  else if x = 2 then Sum.inr .unresolved
  else Sum.inr .divergent

/-- A register whose carrier is terms and whose classification lands in a three-reason level. -/
def typeRegister : Member where
  X := Fin 4
  B := Bool ⊕ TypeGround
  canDiffer := ⟨Sum.inl true, Sum.inr .illFormed, by decide⟩
  classify := typeClassify
  nondegenerate := ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩

/-- **Three genuinely distinct grounds.** Each ground is reached by a term and there is a typed verdict; the
three grounds are pairwise distinct. Not one absence tripled. -/
theorem three_grounds_reachable_distinct :
    typeClassify 1 0 = Sum.inr TypeGround.illFormed
    ∧ typeClassify 2 0 = Sum.inr TypeGround.unresolved
    ∧ typeClassify 3 0 = Sum.inr TypeGround.divergent
    ∧ typeClassify 0 0 = Sum.inl true
    ∧ TypeGround.illFormed ≠ TypeGround.unresolved
    ∧ TypeGround.unresolved ≠ TypeGround.divergent
    ∧ TypeGround.illFormed ≠ TypeGround.divergent :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide, by decide⟩

/-- **Conforms and inherits.** The register passes the unchanged protocol and the payload fires; it receives
the level's structure by conforming: `2 ^ 3 - 1 = 7` permitted totalizations (via the canonical general
theorem), one prohibition, three reasons. -/
theorem conforms_and_inherits :
    ¬ Function.Surjective typeRegister.classify
    ∧ (Finset.univ.filter (fun close : TypeGround → Bool => ¬ ∀ g, close g = true)).card = 2 ^ 3 - 1
    ∧ (Finset.univ.filter (fun close : TypeGround → Bool => ∀ g, close g = true)).card = 1
    ∧ Fintype.card TypeGround = 3 := by
  refine ⟨payload typeRegister, ?_, by decide, by decide⟩
  have h := (permitted_lattice_from_reason_count TypeGround).2
  rwa [show Fintype.card TypeGround = 3 from by decide] at h

/-! ## Part 2: do the seven read?

The grounds carry a prerequisite order, IMPORTED: inference presupposes well-formedness, and termination
checking presupposes a type, so closing a later ground while leaving an earlier one open is incoherent. A
closure reads only if it respects the order. -/

/-- The dynamic stance: close nothing, all grounds open. -/
def stanceDynamic : TypeGround → Bool := fun _ => false

/-- The partial-but-typed stance: close ill-formedness and inference, leave divergence open. -/
def stancePartialInfer : TypeGround → Bool
  | .divergent => false
  | _ => true

/-- The totality stance: close every ground. -/
def stanceTotal : TypeGround → Bool := fun _ => true

/-- Close well-formedness only: a parsed but untyped language. -/
def closeWellFormed : TypeGround → Bool
  | .illFormed => true
  | _ => false

/-- A closure is coherent when it respects the prerequisite order (IMPORTED): closing inference requires
closing well-formedness, closing divergence requires closing inference. -/
abbrev coherent (close : TypeGround → Bool) : Prop :=
  (close .unresolved = true → close .illFormed = true)
  ∧ (close .divergent = true → close .unresolved = true)

/-- **The readable closures are the coherent ones.** The three readings that pass the gate are coherent
permitted moves: the dynamic stance (close nothing), the well-formed-only stance, and the partial-but-typed
stance. The incoherent closures (inference without well-formedness, divergence without inference) are not
positions: they close a ground whose prerequisite is left open. -/
theorem readings_of_the_permitted :
    (coherent stanceDynamic ∧ ¬ ∀ g, stanceDynamic g = true)
    ∧ (coherent closeWellFormed ∧ ¬ ∀ g, closeWellFormed g = true)
    ∧ (coherent stancePartialInfer ∧ ¬ ∀ g, stancePartialInfer g = true)
    ∧ (¬ coherent (fun g => decide (g = TypeGround.unresolved)))
    ∧ (¬ coherent (fun g => decide (g = TypeGround.divergent))) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by decide⟩

/-- **The three stances are three distinct closures.** Dynamic (close nothing), partial-but-typed (close
ill-formedness and inference), and total (close all) are pairwise distinct; the first two are permitted, the
third is the full closure. The imported positions occupy distinct points, and the totality ideal lands on the
prohibition. -/
theorem three_stances_are_three_closures :
    stanceDynamic ≠ stancePartialInfer
    ∧ stancePartialInfer ≠ stanceTotal
    ∧ stanceDynamic ≠ stanceTotal
    ∧ (¬ ∀ g, stanceDynamic g = true)
    ∧ (¬ ∀ g, stancePartialInfer g = true)
    ∧ (∀ g, stanceTotal g = true) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, by decide, by decide, fun _ => rfl⟩
  · have := congrFun h .illFormed; simp [stanceDynamic, stancePartialInfer] at this
  · have := congrFun h .divergent; simp [stancePartialInfer, stanceTotal] at this
  · have := congrFun h .illFormed; simp [stanceDynamic, stanceTotal] at this

/-- **The prohibition reads.** Closing all three grounds while remaining faithful, a checker total on every
term that yet keeps an absence, is the full closure and the unique prohibited totalization: the base's attempt
generalized to three grounds. -/
theorem the_prohibition_reads :
    (∀ g, stanceTotal g = true)
    ∧ (Finset.univ.filter (fun close : TypeGround → Bool => ∀ g, close g = true)).card = 1 :=
  ⟨fun _ => rfl, by decide⟩

/-! ## Part 3: the verdict -/

/-- **How many read.** Of the seven permitted moves, three are coherent and read as positions; the other four
close a ground without its prerequisite and do not read. The reading survives being made precise, but only on
the coherent sublattice, the up-sets of the prerequisite order. -/
theorem how_many_read :
    (Finset.univ.filter (fun close : TypeGround → Bool => coherent close ∧ ¬ ∀ g, close g = true)).card = 3
    ∧ (Finset.univ.filter (fun close : TypeGround → Bool => ¬ ∀ g, close g = true)).card = 7 :=
  ⟨by decide, by decide⟩

/-- **The first levelled register that reads.** A chart at a level, not at the base: its classification carries
three distinct grounds, the payload fires, and three of the inherited seven moves do recognisable work. What
physics is not: physics has one ground and a binary lattice, this register has three grounds and a lattice
whose coherent sublattice is occupied by real positions. -/
theorem first_levelled_register :
    ¬ Function.Surjective typeRegister.classify
    ∧ Fintype.card TypeGround = 3
    ∧ (Finset.univ.filter (fun close : TypeGround → Bool => coherent close ∧ ¬ ∀ g, close g = true)).card = 3 :=
  ⟨payload typeRegister, by decide, by decide⟩

/-! ## The verdict

Part 1: the register conforms with three genuinely distinct grounds. Each ground is reached by a term and the
three are pairwise distinct (`three_grounds_reachable_distinct`), so it is a three-reason level, not one
absence tripled; it passes the unchanged protocol, the payload fires, and it inherits the seven permitted
moves, one prohibition, three reasons (`conforms_and_inherits`).

Part 2: three of the seven read, and the reading survives only on a sublattice. The grounds carry a prerequisite
order (IMPORTED): inference presupposes well-formedness, termination presupposes a type. The coherent closures,
those respecting the order, are the dynamic, well-formed-only, and partial-but-typed stances
(`readings_of_the_permitted`); the four incoherent closures (a ground closed without its prerequisite) are not
positions, only restatements. The three imported stances land on three distinct closures, two permitted and the
totality ideal on the prohibition (`three_stances_are_three_closures`); closing all three is the attempt
generalized (`the_prohibition_reads`). This is the framework's forcing at a register: a forced level whose
readable moves are the up-sets, the Heyting sublattice that `forcing_gives_heyting` describes.

Part 3: three of seven read (`how_many_read`); this is the first levelled register whose structure does
recognisable work (`first_levelled_register`). It is what physics is not, a chart at a level with real
positions at distinct points. The reading survived being made precise, but refined: not seven clean readings,
three, ordered by an imported prerequisite the free count did not see. All mappings are READINGS with defeasible
fidelity; the grounds and stances are IMPORTED; only the entailments are theorems. Nothing here is resolved. -/

end Chiralogy.TypeRegister
