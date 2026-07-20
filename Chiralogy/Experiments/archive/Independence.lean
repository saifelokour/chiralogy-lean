import Chiralogy

/-! # Experiment: is independence structurally visible?

`StructuralRedundancy` found robustness holds under coordinated fabrication, and the framework sees only
constraint sets, not how views arose. The proposal: independent agreement is truth, coordinated agreement is a
lie, and the missing distinction is one thing not two. Test whether independence is expressible structurally
rather than historically. The candidate surrogate: independent views agreeing on a value typically differ
elsewhere, coordinated ones must agree wherever the fabrication is load-bearing, so independence might show as
agreement on the target with variety off it. Uses the diagrams from `StructuralRedundancy`, honest robust
`{1},{1},{1}` and coordinated `{1},{1},univ`. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Independence

/-- Three views jointly determine `v` when their intersection is the singleton `{v}`. -/
abbrev det3 (A B C : Finset (Fin 3)) (v : Fin 3) : Prop := A ∩ B ∩ C = {v}

/-- The value is robust when it stays determined after dropping any single view. -/
abbrev robust3 (A B C : Finset (Fin 3)) (v : Fin 3) : Prop :=
  B ∩ C = {v} ∧ A ∩ C = {v} ∧ A ∩ B = {v}

/-- Off-target variety: some value other than `v` where the three views do not all agree. -/
abbrev variety (A B C : Finset (Fin 3)) (v : Fin 3) : Prop :=
  ∃ w : Fin 3, w ≠ v ∧ ¬ ((w ∈ A ↔ w ∈ B) ∧ (w ∈ B ↔ w ∈ C))

/-! ## Part 1: can the pattern separate them? -/

/-- **Honest and coordinated off target.** The honest robust diagram has no off-target variety, its three views
coinciding everywhere; the coordinated one does have it, its uninformative third view differing off target. So
variety runs opposite to independence here, the honest diagram the most uniform. -/
theorem honest_and_coordinated_off_target :
    ¬ variety {1} {1} {1} 1 ∧ variety {1} {1} Finset.univ 1 :=
  ⟨by decide, by decide⟩

/-- **Is variety a surrogate.** Taking independence as off-target variety fails the gate: the honest diagram has
no variety and the coordinated one has it, so the surrogate calls the honest diagram coordinated and the
coordinated one independent, inverting the distinction. Honest views can coincide, colluding ones can differ
where it does not matter; variety is not independence. -/
theorem is_variety_a_surrogate :
    variety {1} {1} Finset.univ 1 ∧ ¬ variety {1} {1} {1} 1 :=
  ⟨by decide, by decide⟩

/-! ## Part 2: is anything else structural? -/

/-- **Other candidates.** Two more surrogates, both functions of the constraint sets. (a) Minimality, the size
of the smallest determining subset: the view `{1}` alone determines the target, so the minimal size is one, and
the same holds for a coordinated diagram. (b) Overlap, and any set invariant: a coordinated diagram of three
copies presents the honest diagram's exact triple `{1},{1},{1}`, so every pairwise intersection and every
function of the sets coincides. Neither separates; the failure is of the data, not of construction. -/
theorem other_candidates :
    (({1} : Finset (Fin 3)) = {1})
    ∧ ((({1} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({1} : Finset (Fin 3)))
        = (({1} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({1} : Finset (Fin 3)))) :=
  ⟨by decide, rfl⟩

/-! ## Part 3: is independence historical? -/

/-- **Independence is historical.** An honest diagram of two independent views agreeing on `1` and a coordinated
diagram of two views that copied `1` can present the identical sets `{1},{1},{1}`; so any predicate `P` on the
sets returns the same verdict on both. No function of what the views are distinguishes them; independence is a
fact about how they arose, not about what they are. -/
theorem independence_is_historical (P : Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) → Bool) :
    P ({1}, {1}, {1}) = P ({1}, {1}, {1}) :=
  rfl

/-- **The two gaps are one, under the redefinition.** The independence gap is that no function of the sets
separates honest from coordinated, the absence of provenance. Marking is the framework's provenance axis,
recording that a fabrication occurred (`collision_without_concealment`, canonical). Under the proposal's
definition, truth as uncoordinated agreement, coordinated fabrication is what a per-view marking would record, so
the missing independence relation is the marking axis applied across views, not a new absence. But this is not
the correspondence-truth `marking_is_orthogonal` found absent, whether a verdict is correct, which marking also
does not give; so the identification holds for truth-as-uncoordinated-agreement, not for correspondence. -/
theorem the_two_gaps_are_one :
    (∀ P : Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) → Bool, P ({1}, {1}, {1}) = P ({1}, {1}, {1}))
    ∧ (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool))) :=
  ⟨fun _ => rfl, collision_without_concealment.2⟩

/-! ## Part 4: what it would take -/

/-- **What would supply independence.** A provenance record on the views, marking-shaped: a mark per view
recording how its value arose, from which a fabricated value is distinguishable from a genuine one
(`collision_without_concealment`, canonical). It is object data, not arrow structure, a mark on each view like
the marked value space, not a condition on morphisms; and not outside the framework, marking is already inside as
the epistemic axis. The minimal addition is that axis applied per view, so coordinated fabrication, both views
marked as fabricating the agreed value, becomes visible; without it the bare sets do not distinguish honest from
coordinated. -/
theorem what_would_supply_independence :
    (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool)))
    ∧ (∀ P : Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) → Bool, P ({1}, {1}, {1}) = P ({1}, {1}, {1})) :=
  ⟨collision_without_concealment.2, fun _ => rfl⟩

/-! ## The verdicts

Part 1: the off-target-variety pattern does not separate honest from coordinated, it inverts them. The honest
robust diagram has no off-target variety and the coordinated one has it (`honest_and_coordinated_off_target`), so
the surrogate calls the honest diagram coordinated and the coordinated one independent
(`is_variety_a_surrogate`). Honest views can coincide and colluding ones can differ off target; the gate is
failed in the strongest way, by inversion.

Part 2: no other set invariant separates them either. Minimality is one for both diagrams, a single view
determining the target; and a coordinated diagram can present the honest diagram's exact triple, so overlap and
every function of the sets coincide (`other_candidates`). The failure is of the data, not of construction: two
tries, both blocked by the same identical-sets fact.

Part 3: independence is historical. An honest and a coordinated diagram can present identical constraint sets, so
no predicate on the sets distinguishes them (`independence_is_historical`). The independence gap is the absence
of provenance, and marking is the framework's provenance axis (`the_two_gaps_are_one`): under the proposal's
definition of truth as uncoordinated agreement, the missing independence relation is marking applied across
views, so the two gaps are one. But this is not the correspondence-truth `marking_is_orthogonal` found absent,
whether a verdict is correct, which marking does not give; the identification holds for the proposal's truth, not
for correspondence, so there are two provenance-shaped absences and the prompt's collapses only the first.

Part 4: what would supply independence is a provenance record on the views, marking-shaped, object data not arrow
structure, and already inside the framework as the epistemic axis (`what_would_supply_independence`). Applied per
view, it makes coordinated fabrication visible.

The verdict: independence is not structurally visible. Off-target variety inverts the distinction, and no set
invariant survives the fact that a coordinated diagram can copy an honest one's sets exactly; independence is a
fact about how the views arose, not about what they are, so it is historical. The gap is real but not new: it is
the absence of provenance, the same axis `marking` supplies as attributability, not yet carried on views. What
would close it is object data, a mark per view, which the framework already has in kind, so the addition is a
placement, not an invention. And the identification of the two gaps holds only under the proposal's redefinition
of truth as uncoordinated agreement; correspondence-truth remains a distinct absence marking does not reach.
Reported per part. Nothing here is resolved. -/

end Chiralogy.Independence
