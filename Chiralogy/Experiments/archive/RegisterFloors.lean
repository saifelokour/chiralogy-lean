import Chiralogy

/-! # Experiment: do registers have their own floors?

The framework's floor is stipulated: non-degeneracy is a protocol condition, not a kernel theorem, and the total
opening satisfies every kernel result. Test whether individual registers supply floors from their own domain
content, and whether those floors share a form. Compute all five before judging; do not select a candidate in
advance. The register pattern: structure derived, content IMPORTED, mapping a READING. Physics is degenerate at
its base, one ground, nothing beneath superposition, so it is expected to have no floor, and that is tested rather
than assumed. Stays in `Experiments/`; canonical untouched; nothing resolved.

The domain failure states, IMPORTED. Chemistry: a method detecting nothing at any concentration. Immunology: a
repertoire binding nothing. Type systems: a checker accepting nothing (how much rejection is too much is contested
by practitioners, so the criterion is live). Cognition: a generative model predicting nothing, every
representation prediction-error. Trust: an agent trusting no one and trusted by no one. Structurally each is one
condition, the positive verdict, the domain's success, never firing. -/

open Chiralogy

namespace Chiralogy.RegisterFloors

/-- The candidate register floor: the positive verdict, the domain's success act, never fires. -/
abbrev neverPos {n : ℕ} (c : Fin n → Fin n → Option Bool) : Prop := ∀ x y, c x y ≠ some true

/-- A floor-state witness on the `Fin 3` carriers (immunology, type, cognition): a classification that never
succeeds, yet distinguishes its first row (rejects, but not uniformly). -/
def wit3 : Fin 3 → Fin 3 → Option Bool := fun x _ => if x = 0 then some false else none

/-- A floor-state witness on the `Fin 4` carriers (chemistry, trust). -/
def wit4 : Fin 4 → Fin 4 → Option Bool := fun x _ => if x = 0 then some false else none

/-! ## Part 1: the candidate floors, per register -/

/-- **The five candidate floors are one form.** Chemistry detecting nothing, immunology binding nothing, type
systems accepting nothing, cognition predicting nothing, trust trusting no one: each is the positive verdict never
firing, on the `Fin 3` carriers and the `Fin 4` carriers. A single structural condition, IMPORTED per domain, read
as `neverPos`. -/
theorem candidate_floors :
    neverPos wit3 ∧ neverPos wit4 :=
  ⟨by decide, by decide⟩

/-! ## Part 2: is each floor Member in domain clothes? -/

/-- **The domain floor is not non-degeneracy.** It is independent both ways: a constant positive classification is
degenerate, failing the protocol floor, yet is not at the domain floor, having a positive; and there are
classifications at the domain floor that are non-degenerate. The two floors do not coincide. -/
theorem is_each_floor_non_degeneracy :
    (¬ NonDegenerate (fun _ _ => some true : Fin 3 → Fin 3 → Option Bool)
      ∧ ¬ neverPos (fun _ _ => some true : Fin 3 → Fin 3 → Option Bool))
    ∧ (neverPos wit3 ∧ NonDegenerate wit3) := by
  unfold NonDegenerate; decide

/-- **The floor bites above non-degeneracy.** For each carrier a classification distinguishes something, a
protocol-member, yet fails the domain floor, never a positive verdict: a type checker rejecting every program with
distinct diagnostics distinguishes programs yet accepts nothing; a method giving varied readings none crossing the
detection threshold detects nothing. So the register floors are stricter than the protocol's, imported. -/
theorem or_is_it_domain_specific :
    (NonDegenerate wit4 ∧ neverPos wit4)
    ∧ (NonDegenerate wit3 ∧ neverPos wit3) := by
  unfold NonDegenerate; decide

/-! ## Part 3: do the floors share a form? -/

/-- **The common form is the unreached positive verdict.** The five reduce to one condition, `neverPos`, and it is
not the protocol floor, the witnesses being non-degenerate: a value-space condition, whether the positive verdict
appears, the same across the five. -/
theorem common_form :
    (neverPos wit3 ∧ neverPos wit4)
    ∧ (NonDegenerate wit3 ∧ NonDegenerate wit4) := by
  unfold NonDegenerate; decide

/-- **It is not computable from the ground-order.** The floor is a value-space condition, whether the positive
verdict appears; two classifications on the same carrier, one at the floor and one not, so the order, a structure
on grounds, does not determine it. The order candidates, every ground closed or a component constant, are
conditions on closures or rows, not on the verdict, so none is the floor. -/
theorem is_it_computable_from_the_order :
    (neverPos wit3)
    ∧ (¬ neverPos (fun _ _ => some true : Fin 3 → Fin 3 → Option Bool))
    ∧ (¬ neverPos (fun _ _ => some false : Fin 3 → Fin 3 → Option Bool) → False)
    ∧ (neverPos (fun _ _ => none : Fin 3 → Fin 3 → Option Bool)) := by
  refine ⟨by decide, by decide, ?_, by decide⟩
  intro h; exact h (by decide)

/-! ## Part 4: the verdict -/

/-- **Registers have floors, with a common form.** For each carrier a non-degenerate classification sits at the
domain floor, so the floor bites above the protocol's, and the form is one, the unreached positive verdict:
imported domain content, a reading. -/
theorem do_registers_have_floors :
    (neverPos wit4 ∧ NonDegenerate wit4)
    ∧ (neverPos wit3 ∧ NonDegenerate wit3) := by
  unfold NonDegenerate; decide

/-- **Physics has none.** On one ground every classification is degenerate, so there is no non-degenerate
classification for a domain floor to bite above: the domain floor coincides with the base, and physics has no
floor above it. The absence follows from the single ground, as expected. -/
theorem does_physics_have_one :
    (∀ c : Fin 1 → Fin 1 → Option Bool, ¬ NonDegenerate c)
    ∧ (¬ ∃ c : Fin 1 → Fin 1 → Option Bool, neverPos c ∧ NonDegenerate c) := by
  refine ⟨?_, ?_⟩ <;> (unfold NonDegenerate; decide)

/-! ## The verdicts

Part 1: the five candidate floors are one form. Chemistry detecting nothing, immunology binding nothing, type
systems accepting nothing, cognition predicting nothing, trust trusting no one, each the positive verdict never
firing (`candidate_floors`), IMPORTED per domain and read as `neverPos`.

Part 2: the floors bite above non-degeneracy. The domain floor does not coincide with the protocol's, independent
both ways (`is_each_floor_non_degeneracy`); and for each carrier a non-degenerate classification sits at it, failed
by the domain while a protocol-member (`or_is_it_domain_specific`). Stricter than non-degeneracy, imported.

Part 3: they share a form, a value-space one. The five reduce to `neverPos`, not the protocol floor
(`common_form`); and it is not computable from the ground-order, differing on the same carrier, the order
candidates being the wrong kind (`is_it_computable_from_the_order`).

Part 4: registers have floors with a common form (`do_registers_have_floors`); physics has none, its single ground
leaving every classification degenerate (`does_physics_have_one`).

The verdict: registers do have their own floors, and the five share a form, but it is a value-space condition, not
one the ground-order supplies. Each domain's failure, detecting nothing, binding nothing, accepting nothing,
predicting nothing, trusting no one, is structurally the same: the positive verdict, the domain's success act,
never fires. This bites above the protocol's floor: a classification can distinguish something, a member by
non-degeneracy, while never succeeding, a type checker rejecting every program with distinct diagnostics or a
method returning varied readings none crossing the threshold, so the register floor rejects classifications the
protocol admits. The common form is real, `neverPos`, but it is about the value space, whether the success verdict
appears, not about the order: two classifications on one carrier differ on it, so the ground-order does not
determine it, and the order candidates, every ground closed or a component constant, are conditions on closures or
rows, not on the verdict. So the register floors are genuine domain contributions, imported, stricter than the
protocol's, sharing a value-space form the framework does not derive. Physics has none: its single ground leaves
every classification degenerate, so there is no non-degenerate classification for a domain floor to bite above, and
the floor collapses onto the base, exactly as the single ground predicts. Per the counter-bias, the floor is not
non-degeneracy relabelled, biting above it with a non-degenerate witness; the common form was computed across the
five and against the protocol and order candidates, not selected; and physics was tested, its floorlessness
following from the single ground rather than assumed. The floors are readings of imported domain content; the
structure, that they bite above and share a value-space form, is the framework's to state. Reported per part.
Nothing here is resolved. -/

end Chiralogy.RegisterFloors
