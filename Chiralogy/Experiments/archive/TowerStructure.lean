import Chiralogy

/-! # Experiment: the moves, center, and boundary at each level of the model tower

Five levels sit over `Option Bool` (Reader, State, Except, Writer, List). At the base the moves are
totalization and partialization, the chiasm crosses at the none, and the boundary is
`complete_and_faithful_is_impossible`, all stated over a singular absence (5.a.2). A level with different
absence-structure has its own moves, center, and boundary. Describe them in their own right; the base is one
instance among several, not the standard.

Works with the codomain types directly. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.TowerStructure

/-! ## Except: structured absence (many reasons)

The codomain is `Bool ⊕ Bool`: a verdict `inl b`, an absence with reason `inr e`. -/

/-- A per-reason totalization: total everywhere except at `(0,2)`, where it keeps reason `e`. -/
def exClass (e : Bool) : Fin 4 → Fin 4 → Bool ⊕ Bool :=
  fun x y => if x = 0 ∧ y = 2 then Sum.inr e else Sum.inl true

/-- **The center fragments.** With several reasons, the absence points are a family, not one: `inr false` and
`inr true` are distinct crossing points. The chiasm crosses at each reason separately. -/
theorem except_center_is_a_family : (Sum.inr false : Bool ⊕ Bool) ≠ Sum.inr true := by decide

/-- Distinct reasons give distinct partial totalizations: the family of crossings is genuine. -/
theorem except_reasons_give_distinct_classes : exClass false 0 2 ≠ exClass true 0 2 := by
  simp [exClass]

/-- **The boundary is a spectrum.** For each reason `e`, total-except-reason-`e` is coherent: total everywhere
but `(0,2)`, where it keeps reason `e`. Partial totalization by reason is available. -/
theorem except_boundary_is_a_spectrum (e : Bool) :
    (∀ x y : Fin 4, ¬(x = 0 ∧ y = 2) → ∃ b, exClass e x y = Sum.inl b)
    ∧ exClass e 0 2 = Sum.inr e := by
  refine ⟨fun x y h => ⟨true, ?_⟩, ?_⟩
  · simp only [exClass, if_neg h]
  · simp [exClass]

/-- **Only full totality collides.** A classification total everywhere and keeping any reason is impossible:
the impossibility bites only at full totality, not at any per-reason partial totalization. -/
theorem except_full_totality_collides :
    ¬ ∃ c : Fin 4 → Fin 4 → Bool ⊕ Bool,
      (∀ x y, ∃ b, c x y = Sum.inl b) ∧ (∃ x y e, c x y = Sum.inr e) := by
  rintro ⟨c, htot, x, y, e, he⟩
  obtain ⟨b, hb⟩ := htot x y
  rw [hb] at he
  simp at he

/-! ## Writer: the classification carries a log

Totalization can be silent (fabricate, leave the log) or recording (fabricate and log it). -/

def totalizeSilent : Option Bool × List Bool → Option Bool × List Bool
  | (none, l) => (some true, l)
  | (some b, l) => (some b, l)

def totalizeRecording (e : Bool) : Option Bool × List Bool → Option Bool × List Bool
  | (none, l) => (some true, e :: l)
  | (some b, l) => (some b, l)

/-- **Silent totalization loses the fabrication.** A fabricated verdict and a genuine one collide: the move
is irreversible, as at the base. -/
theorem silent_loses_fabrication :
    totalizeSilent (none, []) = totalizeSilent (some true, ([] : List Bool)) := rfl

/-- **Recording totalization marks the fabrication.** The log records that a verdict was fabricated, so it is
distinguishable from a genuine one: structure the base's single unmarked absence cannot express. -/
theorem recording_marks_fabrication (e : Bool) :
    totalizeRecording e (none, []) ≠ totalizeRecording e (some true, ([] : List Bool)) :=
  fun h => List.cons_ne_nil e [] (congrArg Prod.snd h)

/-! ## List: plural verdicts

The absence is the empty list, the one-verdict point is the singleton, plurality is a longer list. -/

/-- **The center is bidirectional.** Around the singleton (one verdict) there are two deviations: the empty
list (under-determined, absent) and a longer list (over-determined, plural). The base has only the absence
side. -/
theorem list_has_two_deviations :
    ([] : List (Option Bool)).length = 0
    ∧ ([some true] : List (Option Bool)).length = 1
    ∧ ([some true, some false] : List (Option Bool)).length = 2 := by decide

/-- **The boundary keeps the base's shape on the absence side.** Total (every verdict-list nonempty) and
faithful (some empty) collide, exactly as at the base; the plural direction is extra structure the base's
boundary does not address. -/
theorem list_boundary_collides :
    ¬ ∃ c : Fin 4 → Fin 4 → List (Option Bool),
      (∀ x y, c x y ≠ []) ∧ c 0 2 = [] := by
  rintro ⟨c, htot, hf⟩; exact htot 0 2 hf

/-! ## Reader: the classification varies with context -/

def totalizeUniform (f : Bool → Option Bool) : Bool → Option Bool :=
  fun s => match f s with | none => some true | some b => some b

def totalizeVarying (f : Bool → Option Bool) : Bool → Option Bool :=
  fun s => match f s with | none => some s | some b => some b

/-- **The moves have a context-uniform and a context-varying variant.** Uniform fabricates the same verdict
at every context (the natural one, matching the base); varying fabricates per context, buying
context-dependent fabrication. They differ. -/
theorem reader_totalization_has_variants :
    totalizeUniform (fun _ => none) ≠ totalizeVarying (fun _ => none) :=
  fun h => absurd (congrFun h false) (by decide)

/-- **The center is context-dependent.** The absence is now a function of context: a classification absent at
one context and present at another. The none is carried and varies, where the base's is single. -/
theorem reader_center_is_context_dependent :
    ∃ f : Bool → Option Bool, f true = none ∧ f false = some true :=
  ⟨fun s => if s then none else some true, rfl, rfl⟩

/-! ## State: the classification consults its state -/

def totalizeStateBlind (f : Bool → Option Bool × Bool) : Bool → Option Bool × Bool :=
  fun s => match f s with | (none, s') => (some true, s') | (some b, s') => (some b, s')

def totalizeStateReading (f : Bool → Option Bool × Bool) : Bool → Option Bool × Bool :=
  fun s => match f s with | (none, s') => (some s', s') | (some b, s') => (some b, s')

/-- **Totalization can read the state.** The fabrication may depend on what the classification has done: a
state-reading totalization differs from a state-blind one. The base, stateless, has only the blind move. -/
theorem state_totalization_reads_state :
    totalizeStateBlind (fun s => (none, s)) ≠ totalizeStateReading (fun s => (none, s)) :=
  fun h => absurd (congrFun h false) (by decide)

/-! ## The prohibition under structured absence

`except_boundary_is_a_spectrum` showed the boundary is graded above the base. What does that do to the one
prohibition (6.a.3) and to 6.a.4 (nothing reachable ranked)? A totalization move at Except is given by which
reasons it closes, `close : Bool → Bool`; it is full when it closes every reason. -/

abbrev isFull (close : Bool → Bool) : Prop := close false = true ∧ close true = true
abbrev keepsSome (close : Bool → Bool) : Prop := close false = false ∨ close true = false

/-- **Permitted iff not full.** A move keeps some reason (does not collide) exactly when it is not the full
closure. -/
theorem permitted_iff_not_full (close : Bool → Bool) : keepsSome close ↔ ¬ isFull close := by
  cases h0 : close false <;> cases h1 : close true <;> simp [isFull, keepsSome, h0, h1]

/-- **Exactly one prohibited move.** Only the full closure collides: the prohibited totalization is unique,
not a family. -/
theorem exactly_one_prohibited (close : Bool → Bool) : isFull close ↔ close = fun _ => true := by
  constructor
  · rintro ⟨h0, h1⟩; funext r; cases r <;> assumption
  · rintro rfl; exact ⟨rfl, rfl⟩

/-- **One prohibition, permitted set grew.** Of the four totalization moves, exactly one, the full closure, is
prohibited and three are permitted. Structured absence narrows the prohibition, it does not fragment it:
fewer moves forbidden than the binary base, more permitted. -/
theorem one_prohibition_permitted_grew :
    (Finset.univ.filter (fun close : Bool → Bool => isFull close)).card = 1
    ∧ (Finset.univ.filter (fun close : Bool → Bool => ¬ isFull close)).card = 3 := by decide

/-! ### Ranking: does 6.a.4 hold? -/

abbrev closeLE (close close' : Bool → Bool) : Prop := ∀ r, close r = true → close' r = true

/-- **The full closure is the top.** Every move is below the full closure: the prohibition sits at the top of
the inclusion order. -/
theorem full_closure_is_the_top (close : Bool → Bool) : closeLE close (fun _ => true) :=
  fun _ _ => rfl

/-- **The moves are ranked by inclusion.** A strict chain of closures exists: closing more reasons is higher.
Reachable partial totalizations are ordered by how much they close, so 6.a.4's "nothing reachable ranked" is
qualified above the base. -/
theorem partial_totalizations_are_ranked :
    closeLE (fun _ => false) (fun r => decide (r = false))
    ∧ closeLE (fun r => decide (r = false)) (fun _ => true)
    ∧ ¬ closeLE (fun _ => true) (fun r => decide (r = false)) := by decide

/-- **The ranking is partial, not total.** Closing only `false` and closing only `true` are incomparable: the
order is a lattice of closures, not a total ranking of the reachable. -/
theorem ranking_is_partial_not_total :
    ¬ closeLE (fun r => decide (r = false)) (fun r => decide (r = true))
    ∧ ¬ closeLE (fun r => decide (r = true)) (fun r => decide (r = false)) := by decide

/-! ### Writer: collision without concealment -/

/-- **Recorded totalization still collides.** The boundary collision holds at the memoryful codomain: total
(verdict always present) and faithful (an absence) are incompatible regardless of the log. So recorded
totalization is prohibited by collision. -/
theorem recorded_totalization_collides :
    ¬ ∃ c : Fin 4 → Fin 4 → Option Bool × List Bool,
      (∀ x y, (c x y).1 ≠ none) ∧ (c 0 2).1 = none := by
  rintro ⟨c, htot, hf⟩; exact htot 0 2 hf

/-- **Collision without concealment.** The collision holds (structural), while the recording variant marks the
fabrication (`recording_marks_fabrication`), so it does not conceal. The base bundles collision and
concealment; Writer separates them: collision survives, concealment is contingent on unmarked absence. -/
theorem collision_without_concealment :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool × List Bool, (∀ x y, (c x y).1 ≠ none) ∧ (c 0 2).1 = none)
    ∧ (∀ e : Bool, totalizeRecording e (none, []) ≠ totalizeRecording e (some true, ([] : List Bool))) :=
  ⟨recorded_totalization_collides, recording_marks_fabrication⟩

/-! ## The verdict

Except: the richest. The center fragments into a family of crossings, one per reason
(`except_center_is_a_family`, `except_reasons_give_distinct_classes`); the boundary is a spectrum, total-except-
reason-`e` coherent for each `e`, only full totality colliding (`except_boundary_is_a_spectrum`,
`except_full_totality_collides`). Partial totalization by reason is a move the base lacks.

Writer: totalization splits into silent (irreversible, as the base) and recording, which marks the
fabrication in the log (`silent_loses_fabrication`, `recording_marks_fabrication`): recoverable fabrication,
structure the base's unmarked absence cannot express.

List: the center is bidirectional, a singleton flanked by the empty list and plurality
(`list_has_two_deviations`); the boundary keeps the base's shape on the absence side (`list_boundary_collides`),
with over-determination as extra structure.

Reader: the moves gain a context-varying variant (`reader_totalization_has_variants`), and the center is
context-dependent (`reader_center_is_context_dependent`): the none is carried and varies with context.

State: totalization can read the state (`state_totalization_reads_state`): the fabrication may consult history,
a move the stateless base lacks.

The prohibition, under structured absence: it does not fragment, it narrows. Exactly one move is prohibited,
the full closure (`exactly_one_prohibited`, `one_prohibition_permitted_grew`); the permitted set grows from one
(the binary base) to three, since partial totalizations become available. So the one prohibition stays one and
its content narrows: structured absence makes the framework more permissive, not more prohibitive. But 6.a.4
is qualified: the reachable partial totalizations are ranked by inclusion (`partial_totalizations_are_ranked`),
with the prohibition at the top (`full_closure_is_the_top`); the ranking is a partial order, a lattice, not a
total one (`ranking_is_partial_not_total`). And at Writer the two halves of the base's rationale separate: the
collision survives (`recorded_totalization_collides`) while concealment drops away, since recording marks the
fabrication (`collision_without_concealment`).

The verdict: the model structure differs by level. Except fragments the center and spreads the boundary into a
spectrum, yet the prohibition narrows rather than fragments (one forbidden move, more permitted), while an
inclusion order appears among the permitted, qualifying 6.a.4. Writer makes fabrication recordable, separating
collision from concealment; List makes the center bidirectional; Reader and State make the moves context- and
state-dependent. The base's singular none is one instance; each level's absence-structure gives its own moves,
center, boundary, and ethics. Nothing here is resolved beyond describing that structure. -/

end Chiralogy.TowerStructure
