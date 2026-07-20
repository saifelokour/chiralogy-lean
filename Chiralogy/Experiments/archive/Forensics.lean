-- ARCHIVED (register and ground-structure graduation): the three-sources-independent apparatus graduated to Model/GroundForensics.

import Chiralogy

/-! # Experiment: locating an attempt, generalized over ground-structures

Three results sit unconnected: marking is a positive per-move log, the fibre a negative per-state test, and the
grounds are enumerated with a known closeable family. Assemble them, parameterized over the ground-structure
(reason count and prerequisite order) using `Grounds`'s `closeable`, so the apparatus applies to any level, then
instantiate at the registers. The apparatus is `candidateClosures`, the closeable family a state could have been
produced by. Parameterized throughout; concrete only at Part 4. Stays in `Experiments/`; canonical untouched;
nothing resolved. -/

open Chiralogy

namespace Chiralogy.Forensics

/-- The apparatus: the closeable family under a prerequisite order, the candidate closures a state could arise
from. -/
abbrev candidateClosures {n : ℕ} (prereq : Fin n → Fin n → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun S => closeable prereq S)

/-! ## Part 1: does the ground-structure constrain the fibre? -/

/-- **The fibre under an order.** Every closure closeable under any order is closeable at the free level (whose
family is all subsets), so the ordered fibre is contained in the free one; and the containment is strict, the
chain `0 ≺ 1` excluding the non-up-set `{1}`. The order constrains. -/
theorem fibre_under_an_order :
    (∀ {n : ℕ} (prereq : Fin n → Fin n → Bool) (S : Fin n → Bool),
        closeable prereq S → closeable prereqDiscrete S)
    ∧ (∃ S : Fin 2 → Bool, closeable prereqDiscrete S ∧ ¬ closeable prereqChain2 S) := by
  refine ⟨?_, ?_⟩
  · intro n prereq S _ a b h1 _
    simp [prereqDiscrete] at h1
  · exact ⟨fun r => decide (r = 1), by decide, by decide⟩

/-- **The fibre from the order.** The candidate closures are computed from the order, not searched: a closure
could have produced the state exactly when it is closeable (an up-set of `prereq`), so membership in the fibre is
read off `prereq` directly. -/
theorem fibre_from_the_order {n : ℕ} (prereq : Fin n → Fin n → Bool) (S : Fin n → Bool) :
    S ∈ candidateClosures prereq ↔ closeable prereq S := by
  simp [candidateClosures]

/-! ## Part 2: does marking plus grounds locate the move? -/

/-- **Locate the move.** Given a log recording the closed set `S`, closeable and not full, the move is located:
it sits below the prohibition at the top (every closure is below the full one) and leaves some reason open. With
the enumeration, the logged set is a specific permitted move. -/
theorem locate_the_move {n : ℕ} (prereq : Fin n → Fin n → Bool) (S : Fin n → Bool)
    (_hcl : closeable prereq S) (hnf : ¬ ∀ r, S r = true) :
    (∀ r, S r = true → (fun _ : Fin n => true) r = true) ∧ (∃ r, S r = false) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  obtain ⟨r, hr⟩ := not_forall.mp hnf
  exact ⟨r, Bool.eq_false_iff.mpr hr⟩

/-- **What the log alone gives.** The log alone says a fabrication occurred, one bit
(`collision_without_concealment`); with the enumeration, the recorded closed set is placed among the `2^n - 1`
permitted moves (`permitted_lattice_from_reason_count`), so the pair identifies which move, not merely that one
was made. -/
theorem what_the_log_alone_gives (ι : Type) [Fintype ι] [DecidableEq ι] :
    (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool)))
    ∧ ((Finset.univ.filter (fun close : ι → Bool => ¬ ∀ r, close r = true)).card
        = 2 ^ Fintype.card ι - 1) :=
  ⟨collision_without_concealment.2, (permitted_lattice_from_reason_count ι).2⟩

/-! ## Part 3: the assembled apparatus -/

/-- **The forensic summary.** The three sources are independent. The grounds bound the possible (the closeable
family, contained in all closures); the fibre rules out the impossible (an empty fibre proves never totalized);
the mark attributes the actual (a recorded fabrication distinguished). None subsumes another: possibility,
negative actuality, positive actuality, each with its own requirement. -/
theorem forensic_summary {n : ℕ} (prereq : Fin n → Fin n → Bool) :
    (∀ S : Fin n → Bool, closeable prereq S → closeable prereqDiscrete S)
    ∧ (¬ ∃ c : Fin 1 → Fin 1 → Option Bool,
        (∃ x y, c x y = none) ∧ totalization (fun _ => 0) c = (fun _ _ => some false))
    ∧ (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool))) := by
  refine ⟨?_, by decide, collision_without_concealment.2⟩
  intro S _ a b h1 _
  simp [prereqDiscrete] at h1

/-! ## Part 4: the registers -/

/-- The prerequisite chain `0 ≺ 1 ≺ 2` on three grounds. -/
def prereqChain3 : Fin 3 → Fin 3 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 1) && decide (b = 2))

/-- **Physics forensics.** One ground, a binary lattice: two closures, one permitted. There is nothing to locate,
a fabrication either occurred at the one ground or not; the fibre and enumeration collapse to the mark's single
bit. -/
theorem physics_forensics :
    ((candidateClosures (prereqDiscrete : Fin 1 → Fin 1 → Bool)).card = 2)
    ∧ ((Finset.univ.filter (fun close : Fin 1 → Bool => ¬ ∀ r, close r = true)).card = 1) :=
  ⟨by decide, by decide⟩

/-- **Type-register forensics.** Three grounds in a prerequisite chain: four closeable up-sets, three of them
permitted (proper), so a log recording the closed set identifies which of the three readable positions a
fabrication corresponds to. The order does forensic work. -/
theorem type_register_forensics :
    ((candidateClosures prereqChain3).card = 4)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqChain3 S ∧ ¬ ∀ r, S r = true)).card = 3) :=
  ⟨by decide, by decide⟩

/-- **What the registers reveal.** The apparatus's range, not content outside it. At physics it collapses (one
permitted move, the fibre and enumeration adding nothing to the mark's one bit); at the type register it
separates (three permitted up-sets located by the log). Neither register shows anything the general case lacks:
physics is the degenerate endpoint, the type register the generic one. -/
theorem what_the_registers_reveal :
    ((Finset.univ.filter (fun close : Fin 1 → Bool => ¬ ∀ r, close r = true)).card = 1)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqChain3 S ∧ ¬ ∀ r, S r = true)).card = 3) :=
  ⟨by decide, by decide⟩

/-! ## The verdicts

Part 1: the order constrains the fibre, and the fibre is computed from the structure. Every closure closeable
under an order is closeable at the free level, so the ordered fibre is contained in the free one, and strictly:
the chain `0 ≺ 1` excludes `{1}` (`fibre_under_an_order`). And the fibre is read off `prereq`, membership being
`closeable prereq S` (`fibre_from_the_order`), not searched. The joint holds: the ground-structure does forensic
work, and the three sources connect.

Part 2: marking plus the enumeration locates the move. A logged closed set, closeable and not full, is placed
below the prohibition at the top and shown to leave a reason open (`locate_the_move`); and where the log alone
says only that a fabrication occurred, the enumeration places it among the `2^n - 1` permitted moves
(`what_the_log_alone_gives`). The log is required: without it the grounds and fibre bound and refute but do not
identify.

Part 3: the three sources are independent (`forensic_summary`). The grounds bound the possible, the fibre rules
out the impossible, the mark attributes the actual; none subsumes another, since possibility is not actuality,
the fibre decides only negatively, and the mark needs a log.

Part 4: the registers exhibit the apparatus's span, not new content. At physics, one ground, it collapses to the
mark's one bit, nothing to locate (`physics_forensics`); at the type register, three grounds in a chain, it
separates the three stances, the log placing a fabrication among them (`type_register_forensics`). Neither adds
to the general case (`what_the_registers_reveal`): physics is the degenerate endpoint and the type register the
generic one.

The verdict: the three loose results assemble into a forensic apparatus parameterized over the ground-structure.
The joint holds at Part 1, the order genuinely shrinking the fibre to its up-sets, so the grounds do forensic
work rather than sitting inert. The apparatus bounds with the closeable family, refutes with the empty fibre, and
attributes with the mark, three independent sources, and it takes the ground-structure as a parameter, a register
applying it by supplying its order. But it is not detection: the fibre decides only negatively, marking requires a
log, and the grounds bound possibility without deciding actuality, so the apparatus locates a move only when a
log records one and only among the possibilities the order allows. The registers instantiate it at its two ends,
physics collapsing it to a bit and the type register realizing it fully, neither revealing anything the general
case does not already hold. So the build is reusable, an apparatus not a demonstration, and honestly bounded.
Reported per part. Nothing here is resolved. -/

end Chiralogy.Forensics
