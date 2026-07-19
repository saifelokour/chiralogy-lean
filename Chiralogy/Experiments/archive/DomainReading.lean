import Chiralogy
import Mathlib.Tactic.DeriveFintype

/-! # Experiment: does any domain read its inherited lattice?

The ethics abstracts over levels: a register receives its permitted lattice and contributes only the reading of
what the reasons are. At `n` reasons there are `2 ^ n - 1` permitted totalizations. Test across candidate
domains whether the permitted moves have substantive readings, as the base physics reading is substantive (a
practitioner could accept or dispute it), or whether the extra structure is domain-inert.

Grounds of absence per domain are IMPORTED: modelling a domain as offering `k` distinguishable grounds asserts
that content, no more. The counts, distinctness, and permitted moves are THEOREMS. Whether a partial move READS
as a recognisable position is a READING, defeasible, argued in prose against the gate: a reading must be
something a practitioner could accept or dispute; a restatement of the move is not a reading. No claim is made
about any subject matter. Stays in `Experiments/`; canonical untouched; the protocol is not extended; nothing
resolved. -/

open Chiralogy

namespace Chiralogy.DomainReading

/-! ## Part 1: the survey

For each candidate, the grounds it offers (IMPORTED), and whether they are several distinguishable grounds (a).
The permitted lattice is inherited from the level by `permitted_lattice_from_reason_count`. -/

/-- Physics: the one natural ground of absence, kept superposition. A second physically distinguishable ground
is not forced; inventing one to populate the survey is declined. -/
inductive PhysAbsence | superposition
  deriving DecidableEq, Fintype

/-- **Physics fails (a): one ground, no partial structure.** At one reason the permitted count is
`2 ^ 1 - 1 = 1`: the only permitted move is keep-open (the base's kept superposition), the only prohibited the
full closure (the base's totalizing demand). There is no intermediate totalization, so the levelled structure
is absent and (b) does not arise. The levelled physics register would be stipulated. -/
theorem physics_one_ground :
    Fintype.card PhysAbsence = 1
    ∧ (Finset.univ.filter (fun close : PhysAbsence → Bool => ¬ ∀ r, close r = true)).card = 1 :=
  ⟨by decide, by decide⟩

/-- A type system: grounds on which a term has no type. Ill-formedness, unresolved inference, divergence. -/
inductive TypeGround | illFormed | unresolved | divergent
  deriving DecidableEq, Fintype

/-- A measurement: grounds on which an observation returns nothing. Below threshold, instrument failure, the
quantity undefined for that object. -/
inductive MeasAbsence | belowThreshold | instrumentFailure | undefinedForObject
  deriving DecidableEq, Fintype

/-- A preference domain: grounds of incomparability. Insufficient information (the corpus's Aumann ancestry),
genuine incommensurability (its Mandler ancestry), undefined on the pair. -/
inductive PrefAbsence | insufficientInfo | incommensurable | undefinedOnPair
  deriving DecidableEq, Fintype

/-- A database (the further domain): grounds of a null field. Unknown-but-applicable and inapplicable (Codd's
A-marks and I-marks), withheld. -/
inductive DataAbsence | unknownApplicable | inapplicable | withheld
  deriving DecidableEq, Fintype

/-- **Four domains pass (a): three distinguishable grounds each.** Each offers three grounds the domain itself
distinguishes (IMPORTED), so each inherits the `2 ^ 3 - 1 = 7` permitted lattice from the level. Distinctness
is a theorem; that the grounds are the domain's is imported. -/
theorem grounds_are_several :
    Fintype.card TypeGround = 3
    ∧ Fintype.card MeasAbsence = 3
    ∧ Fintype.card PrefAbsence = 3
    ∧ Fintype.card DataAbsence = 3 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **The lattice is inherited, not rebuilt.** For each passing domain the permitted count is the level's
`2 ^ (card grounds) - 1`, via the canonical general theorem: the register receives the structure by conforming.
Shown for the type-system grounds; identical for the other three by their card. -/
theorem lattice_inherited :
    (Finset.univ.filter (fun close : TypeGround → Bool => ¬ ∀ r, close r = true)).card = 2 ^ 3 - 1 := by
  have h := (permitted_lattice_from_reason_count TypeGround).2
  rwa [show Fintype.card TypeGround = 3 from by decide] at h

/-! ## Part 2: the readings, where (a) passes

For each passing domain, a named partial move: close one ground while leaving another open. Each is a permitted
totalization (not the full closure, not the empty one). Whether it READS as a recognisable position is stated
per domain and graded, against the gate. -/

/-- Type system: totalize checking (ill-formedness and inference) while leaving divergence open. -/
def typeTotalizeChecking : TypeGround → Bool
  | .illFormed => true
  | .unresolved => true
  | .divergent => false

/-- Measurement: substitute a value below threshold, leaving failure and undefined open. -/
def measSubstituteBelow : MeasAbsence → Bool
  | .belowThreshold => true
  | _ => false

/-- Preference: complete the informational gaps, leaving incommensurability and undefined open. -/
def prefCompleteInfo : PrefAbsence → Bool
  | .insufficientInfo => true
  | _ => false

/-- Database: materialise the inapplicable fields to a default, leaving unknown and withheld null. -/
def dataMaterialiseInapplicable : DataAbsence → Bool
  | .inapplicable => true
  | _ => false

/-- **Each passing domain has a genuine partial move.** Each named closure is permitted (not the prohibited
full closure) and non-trivial (not the empty keep-open move): a real intermediate totalization exists in every
domain that passes (a). This is the structural precondition for a reading; substantiveness is the prose verdict
below. -/
theorem partial_moves_exist :
    ((¬ ∀ r, typeTotalizeChecking r = true) ∧ (∃ r, typeTotalizeChecking r = true))
    ∧ ((¬ ∀ r, measSubstituteBelow r = true) ∧ (∃ r, measSubstituteBelow r = true))
    ∧ ((¬ ∀ r, prefCompleteInfo r = true) ∧ (∃ r, prefCompleteInfo r = true))
    ∧ ((¬ ∀ r, dataMaterialiseInapplicable r = true) ∧ (∃ r, dataMaterialiseInapplicable r = true)) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **The prohibition reads in every passing domain.** The full closure is the unique prohibited totalization
in each: closing every ground while remaining faithful is the attempt, generalising the base's totalizing
demand. This move reads wherever the base reads, since it is the base move at more grounds. -/
theorem the_prohibition_reads :
    ((Finset.univ.filter (fun close : TypeGround → Bool => ∀ r, close r = true)).card = 1)
    ∧ ((Finset.univ.filter (fun close : MeasAbsence → Bool => ∀ r, close r = true)).card = 1)
    ∧ ((Finset.univ.filter (fun close : PrefAbsence → Bool => ∀ r, close r = true)).card = 1)
    ∧ ((Finset.univ.filter (fun close : DataAbsence → Bool => ∀ r, close r = true)).card = 1) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ## Part 3: the verdict -/

/-- **Which domains pass (a).** Physics offers one ground; type systems, measurement, preference, and databases
offer three each. So four register domains carry the levelled lattice non-degenerately; the base's own domain,
physics, does not. -/
theorem which_domains_read :
    Fintype.card PhysAbsence = 1
    ∧ Fintype.card TypeGround = 3
    ∧ Fintype.card MeasAbsence = 3
    ∧ Fintype.card PrefAbsence = 3
    ∧ Fintype.card DataAbsence = 3 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **The structure reaches some domain.** In the type-system domain there is a permitted move distinct from
both the prohibited full closure and the empty keep-open one: a genuine intermediate totalization. Reading
(graded, defeasible): this move, totalizing checking while leaving divergence open, is the total-checker over a
partial language, a design stance a practitioner accepts or disputes (against a totality-requiring checker), so
it passes the gate. The inherited lattice does recognisable work in at least one register, not only labelling.
Substantiveness is the READING; the structural non-degeneracy is the theorem. -/
theorem structure_reaches_some_domain :
    (¬ ∀ r, typeTotalizeChecking r = true)
    ∧ (∃ r, typeTotalizeChecking r = true)
    ∧ (typeTotalizeChecking ≠ fun _ => true)
    ∧ (typeTotalizeChecking ≠ fun _ => false) := by
  refine ⟨by decide, by decide, fun h => ?_, fun h => ?_⟩
  · have := congrFun h .divergent; simp [typeTotalizeChecking] at this
  · have := congrFun h .illFormed; simp [typeTotalizeChecking] at this

/-! ## The verdict, per domain

The gate: a reading is substantive if a practitioner could accept or dispute the position; a restatement of the
move ("close the first ground") is not a reading. All verdicts on (b) are READINGS, defeasible.

Physics. (a) FAILS. One natural ground (superposition); a second physically distinguishable ground is not
forced, and inventing one to keep the survey alive is declined. At one reason the lattice is the base's binary
(`physics_one_ground`): keep-open or totalize, no partial move. (b) does not arise. The base's own domain does
not support the levelled structure.

Type systems. (a) PASSES: ill-formedness, unresolved inference, divergence are distinguished failure modes.
(b) PASSES. Closing checking while leaving divergence open (`typeTotalizeChecking`) reads as a total-checked
but partial language, disputable against a totality-requiring checker; closing all three is the total language.
Independent of the framework, so a genuine reading, not a restatement. The clearest positive.

Databases. (a) PASSES: unknown-but-applicable, inapplicable, withheld are distinguished (Codd's marks plus
withholding). (b) PASSES. Materialising the inapplicable while keeping the unknown null
(`dataMaterialiseInapplicable`) reads as splitting the null, disputable against SQL's single null. A genuine
reading with its own literature.

Measurement. (a) PASSES: below threshold, instrument failure, undefined for the object are distinguished.
(b) PASSES, weaker. Substituting below threshold while leaving failure open (`measSubstituteBelow`) reads as a
censoring choice (substitute versus treat as missing), a methodological stance more than a named position, but
still one a practitioner disputes.

Preference. (a) PASSES: insufficient information, genuine incommensurability, undefined on the pair are
distinguished (the corpus's Aumann and Mandler ancestry). (b) PASSES, moderate. Completing on information while
leaving incommensurability open (`prefCompleteInfo`) reads as a bounded-rational completion that respects value
incommensurability, a recognisable stance, though drawn from the corpus's own sources rather than independent.

The verdict: the inherited lattice is NOT domain-inert. It reads in four of five domains tried, clearest in
type systems and databases where a partial closure maps to an independently recognised, disputable position;
the readings in measurement and preference are genuine but weaker. The one domain where the levelled structure
does not read is physics, the base's own domain, which offers a single natural ground: the base has exactly one
prohibition because physics has exactly one ground, and the extra structure earns its keep in the registers,
not in the base. Reported per domain, not averaged. Every (b) verdict is a READING and defeasible. Nothing here
is resolved. -/

end Chiralogy.DomainReading
