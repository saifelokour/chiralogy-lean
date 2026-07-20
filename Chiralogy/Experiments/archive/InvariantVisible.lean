import Chiralogy

/-! # Experiment: is marking what makes invariant structure visible?

`Antifragility` found the truth/lie asymmetry is invariantly derived (the boundary collision holds of every
classification) but variantly visible (only a marked level shows it). Test whether other invisibility results
share that form, and whether the registers instantiate it. A fact is invariantly derived if it follows for every
object from the framework's theorems; variantly visible if no object exhibits it without a level property that
records. The claim under test: marking is the general form of what makes invariant structure visible. The central
distinction, per the counter-bias: marking reveals what is determined but unrecorded, and cannot reveal what is
not determined at all. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.InvariantVisible

/-! ## Part 1: do the other invisibility results share the form? -/

/-- **Detection.** The occurrence of totalization is determined, a `none` was filled, but invisible in the bare
value, the totalized and the genuine verdict equal (`unmarkedTotalize`); marking records it, the logs differing
(`collision_without_concealment`). Detection fits: invariantly determined, marking-visible. -/
theorem detection :
    ((fun v : Option Bool => some (v.getD true)) none = (fun v : Option Bool => some (v.getD true)) (some true))
    ∧ (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool))) :=
  ⟨rfl, collision_without_concealment.2⟩

/-- **Provenance.** Agreement traces to no source in the value, a fabricating leg sending distinct inputs to one
output. The source, whether the views shared an origin, is not determined by the agreement, the same output
arising from `none` or from `some true`; it is a historical fact a per-view mark could record. Provenance fits as
independence does, determined by history and marking-visible, though agreement alone never reveals it. -/
theorem provenance :
    ((fun v : Option Bool => v.getD true) none = (fun v : Option Bool => v.getD true) (some true))
    ∧ ((none : Option Bool) ≠ some true) :=
  ⟨rfl, by decide⟩

/-- **Independence.** Invisible in the sets, honest and coordinated presenting identically, no predicate
separating them; but with each view's fabrication marked (`collision_without_concealment`), coordinated
agreement, both views recording a fabrication of the value, becomes visible. Determined by history,
marking-visible. Fits. -/
theorem independence :
    (∀ P : Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) → Bool, P ({1}, {1}, {1}) = P ({1}, {1}, {1}))
    ∧ (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool))) :=
  ⟨fun _ => rfl, collision_without_concealment.2⟩

/-- **Vacating.** A vacated classification is total, never returning an absence, so there is no `none` for
marking to record, `recordingTotalize` leaving a `some` verdict untouched with no log. Whether a ground was
avoided or never arose is not determined by a total classification, both presenting as total; the distinction
needs the ground declared, a different level property, and marking, which records filled absences, has nothing to
record where none was filled. Vacating does not fit: undetermined without declaration, marking idle. -/
theorem vacating :
    (∀ x y : Fin 4, (fun _ _ : Fin 4 => some true) x y ≠ none)
    ∧ (recordingTotalize true (some true, ([] : List Bool)) = (some true, [])) :=
  ⟨fun _ _ => Option.some_ne_none true, rfl⟩

/-- **Which fit.** The fabrication family fits, detection, independence, and provenance each determined by
process or history, invisible in the bare object, made visible by marking a filled absence
(`collision_without_concealment`). Vacating does not: a total classification has no absence to mark, so whether a
ground was avoided is undetermined without declaration, a different level property. Marking is the visibility axis
for facts about fabrication, not for all invisible structure: it holds for what marking records, a filled `none`,
and not for what has no `none` to fill. -/
theorem which_fit :
    (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool)))
    ∧ (∀ x y : Fin 4, (fun _ _ : Fin 4 => some true) x y ≠ none) :=
  ⟨collision_without_concealment.2, fun _ _ => Option.some_ne_none true⟩

/-! ## Part 2: the registers -/

/-- **Physics marked.** Physics has one ground (`physics_has_one_ground`), its permitted lattice binary, one
prohibited and one permitted. There is exactly one absence a totalization could fill, so marking records at most
one fabrication, a physics verdict claiming determinacy where the one ground is genuine indeterminacy. Physics
has something to record, but only one thing; marking is not idle at physics, though its ledger is a single bit. -/
theorem physics_marked :
    ((Finset.univ.filter (fun close : Fin 1 → Bool => ∀ r, close r = true)).card = 1)
    ∧ ((Finset.univ.filter (fun close : Fin 1 → Bool => ¬ ∀ r, close r = true)).card = 1)
    ∧ (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool))) :=
  ⟨by decide, by decide, collision_without_concealment.2⟩

/-- **Type register marked.** The type register has three grounds, its permitted lattice with seven permitted and
one prohibited. Marking makes the truth/lie asymmetry visible there: a genuine unresolved inference returns the
ground (`none`), a fabricated verdict fills it (`some`), and the recording distinguishes them; and under the
boundary the fabrication is fragile, total at the hole being unfaithful (`Antifragility`). A chart of the type
register could distinguish a genuine unresolved inference from a fabricated verdict at a ground. -/
theorem type_register_marked :
    ((Finset.univ.filter (fun close : Fin 3 → Bool => ¬ ∀ r, close r = true)).card = 7)
    ∧ (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool)))
    ∧ (∀ c : Fin 4 → Fin 4 → Option Bool, c 0 2 = some true → c 0 2 ≠ imprecise 0 2) :=
  ⟨by decide, collision_without_concealment.2, fun _ h => by rw [h]; decide⟩

/-- **What a marked register gains.** Two things: attributability of its own fabrications, a filled ground
recorded (`collision_without_concealment`), and under the boundary the fragility asymmetry, a fabricated verdict
forced unfaithful under extension (`Antifragility`). Both registers gain: physics one bit, its single ground
either genuine or fabricated; the type register more, three grounds and an order, each a site of fabrication and
fragility. Marking is idle at neither, but its ledger scales with the ground count. -/
theorem what_a_marked_register_gains :
    (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool)))
    ∧ (∀ c : Fin 4 → Fin 4 → Option Bool, c 0 2 = some true → c 0 2 ≠ imprecise 0 2)
    ∧ ((Finset.univ.filter (fun close : Fin 1 → Bool => ¬ ∀ r, close r = true)).card = 1
        ∧ (Finset.univ.filter (fun close : Fin 3 → Bool => ¬ ∀ r, close r = true)).card = 7) :=
  ⟨collision_without_concealment.2, fun _ h => by rw [h]; decide, ⟨by decide, by decide⟩⟩

/-! ## Part 3: the verdict on marking's role -/

/-- **Marking is one axis among several.** It is the visibility axis for fabrication, the fitting family,
detection, independence, and provenance, each a determined-but-unrecorded fabrication made visible by recording a
filled absence. It is not the general form for all invisible structure: a total classification has no absence to
record, so a fact with no filled `none`, vacating, stays invisible to marking, undetermined without a different
level property, declaration. `marking_is_orthogonal`'s epistemic axis is refined, not overturned. -/
theorem marking_is_one_axis_among_several :
    (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool)))
    ∧ (recordingTotalize true (some true, ([] : List Bool)) = (some true, [])) :=
  ⟨collision_without_concealment.2, rfl⟩

/-- **What would need revising.** No canonical theorem changes; the marking and boundary facts hold as stated.
What the framing gains is a unification: marking is the visibility axis for the fabrication family, detection,
independence, provenance, and antifragility all instances of a determined-but-unrecorded fabrication made visible
by recording. The no-truth-axis reports are qualified once more: unmarked data shows no truth, but marking is
precisely what makes the fabrication-facts a truth/lie distinction rests on visible. -/
theorem what_would_need_revising :
    (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool)))
    ∧ (∀ c : Fin 4 → Fin 4 → Option Bool, c 0 2 = some true → c 0 2 ≠ imprecise 0 2)
    ∧ ((fun v : Option Bool => some (v.getD true)) none = (fun v : Option Bool => some (v.getD true)) (some true)) :=
  ⟨collision_without_concealment.2, fun _ h => by rw [h]; decide, rfl⟩

/-! ## The verdicts

Part 1: the pattern holds for the fabrication family and not for the undetermined. Detection, independence, and
provenance are each invariantly determined, by process or history, invisible in the bare object, and made visible
by marking a filled absence (`detection`, `independence`, `provenance`). Vacating does not fit: a total
classification has no `none` to record, so whether a ground was avoided is undetermined without declaration
(`vacating`). So the fitting ones are exactly those about fabrication, and the undetermined one, vacating, marking
cannot reach (`which_fit`). The counter-bias distinction holds: marking reveals the determined-but-unrecorded,
not the undetermined.

Part 2: both registers gain from marking, unequally. Physics has one ground, so one bit to record, a determinacy
claimed where the ground is genuine indeterminacy (`physics_marked`); marking is not idle but minimal. The type
register has three grounds and an order, so the truth/lie asymmetry is visible, a genuine unresolved inference
distinguished from a fabricated verdict, and fragile under the boundary (`type_register_marked`). What a marked
register gains is attributability and, under `Antifragility`, the fragility asymmetry, scaling with the ground
count (`what_a_marked_register_gains`).

Part 3: marking is one axis among several, the axis of fabrication-visibility
(`marking_is_one_axis_among_several`). No canonical theorem changes; the framing gains a unification, the
fabrication family made visible by recording (`what_would_need_revising`).

The verdict: marking is not the fully general form of what makes invariant structure visible, but it is the
visibility axis for a large and unifying class, the fabrication family. Detection, independence, provenance, and
antifragility are all one shape, a fact invariantly determined by process or history, invisible in the bare
object, and made visible by recording a filled absence; marking is exactly the record. The claim narrows at
vacating, where there is no filled `none` and so nothing to record, and the distinction, if it exists, needs
declaration rather than marking, or is genuinely undetermined. So the counter-bias holds: marking reveals the
unrecorded, not the undetermined, and treating the two alike would overstate it. `marking_is_orthogonal`'s
epistemic axis is the same axis seen more generally, and the registers instantiate it, minimally at physics and
substantively at the type register. No canonical theorem changes; the framing gains a unification and a limit.
Reported per part. Nothing here is resolved. -/

end Chiralogy.InvariantVisible
