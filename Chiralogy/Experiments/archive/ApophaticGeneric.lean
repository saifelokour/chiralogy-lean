import Chiralogy

/-! # Experiment: dry run of the apophatic generalization

Restructure the apophatic model as skeleton plus instances, mirroring the cataphatic side. Generic over an
absence-structure, with Maybe as the distinguished base (free pointed) and the five levels as instances. Dry
run only: the canonical tree is untouched, nothing moved; this validates what generalizes before graduating.

Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.ApophaticGeneric

/-! ## Part 1: the generic skeleton

An absence-structure is a value space with a distinguished "absent" predicate. A classification is
`c : X → X → A.V`. Nothing below uses more than the predicate. -/

structure AbsenceStructure where
  V : Type
  absent : V → Prop

/-- **The boundary collision is generic.** No classification is both everywhere-defined and somewhere-absent.
This goes through from the existence of the predicate alone, using nothing about the value space's structure. -/
theorem boundary_collision (A : AbsenceStructure) {X : Type} :
    ¬ ∃ c : X → X → A.V, (∀ x y, ¬ A.absent (c x y)) ∧ (∃ x y, A.absent (c x y)) := by
  rintro ⟨c, htot, x, y, hf⟩; exact htot x y hf

/-- **Totalization, generic.** Given a non-absent value, a classification can be made everywhere-defined. -/
theorem totalization_exists (A : AbsenceStructure) (d : A.V) (hd : ¬ A.absent d) {X : Type} :
    ∃ c : X → X → A.V, ∀ x y, ¬ A.absent (c x y) :=
  ⟨fun _ _ => d, fun _ _ => hd⟩

/-- **Partialization, generic.** Given an absent value, a classification can keep an absence. The moves cross
at the absence-locus `{v | A.absent v}`; how many points that has is an instance fact, not stated here. -/
theorem partialization_exists (A : AbsenceStructure) (a : A.V) (ha : A.absent a) {X : Type} (x₀ : X) :
    ∃ c : X → X → A.V, ∃ x y, A.absent (c x y) :=
  ⟨fun _ _ => a, x₀, x₀, ha⟩

/-! ## Part 2: Maybe as the distinguished base -/

/-- Maybe as an absence-structure: the absent value is `none`. -/
def maybeAbsence : AbsenceStructure := ⟨Option Bool, fun v => v = none⟩

/-- **The base collision is the generic one.** The base's total-versus-absent collision is
`boundary_collision` at `maybeAbsence`; the canonical `complete_and_faithful_is_impossible` (with `imprecise`,
`Fin 4`, its decides and ancestry) stays a concrete fact about this instance, unchanged. -/
theorem base_collision_is_generic {X : Type} :
    ¬ ∃ c : X → X → Option Bool, (∀ x y, c x y ≠ none) ∧ (∃ x y, c x y = none) :=
  boundary_collision maybeAbsence

/-- **Singular absence: the base's distinguishing property.** Maybe has one absence: all absent values are
equal. This is what the tower's shape-claims depend on, and what Except lacks. -/
theorem singular_absence : ∀ v v' : Option Bool, maybeAbsence.absent v → maybeAbsence.absent v' → v = v' :=
  fun _ _ h h' => h.trans h'.symm

/-- **The base embeds out (freeness).** The base injects into a tower level (here Writer), a map out of the
free pointed object `maybe_free_pointed`. Maybe is distinguished by freeness, not convention. -/
theorem base_embeds_out {E : Type} :
    Function.Injective (fun v : Option Bool => (v, ([] : List E))) :=
  fun _ _ h => congrArg Prod.fst h

/-! ## Part 3: the five levels as instances -/

def writerAbsence : AbsenceStructure := ⟨Option Bool × List Bool, fun p => p.1 = none⟩
def readerAbsence : AbsenceStructure := ⟨Bool → Option Bool, fun f => ∃ e, f e = none⟩
def stateAbsence : AbsenceStructure := ⟨Bool → Option Bool × Bool, fun f => ∃ s, (f s).1 = none⟩
def exceptAbsence : AbsenceStructure := ⟨Bool ⊕ Bool, fun x => ∃ e, x = Sum.inr e⟩
def listAbsence : AbsenceStructure := ⟨List (Option Bool), fun l => l = []⟩

/-- **The collision specializes to each level** (generic, so free). -/
theorem collision_at_each_level {X : Type} :
    (¬ ∃ c : X → X → writerAbsence.V, (∀ x y, ¬ writerAbsence.absent (c x y)) ∧ ∃ x y, writerAbsence.absent (c x y))
    ∧ (¬ ∃ c : X → X → exceptAbsence.V, (∀ x y, ¬ exceptAbsence.absent (c x y)) ∧ ∃ x y, exceptAbsence.absent (c x y))
    ∧ (¬ ∃ c : X → X → listAbsence.V, (∀ x y, ¬ listAbsence.absent (c x y)) ∧ ∃ x y, listAbsence.absent (c x y)) :=
  ⟨boundary_collision writerAbsence, boundary_collision exceptAbsence, boundary_collision listAbsence⟩

/-- **The center's cardinality is instance-dependent: Except is plural.** Two distinct absent values (reasons),
so the absence-locus is a family, not a point. -/
theorem except_center_is_plural :
    exceptAbsence.absent (Sum.inr false) ∧ exceptAbsence.absent (Sum.inr true)
    ∧ (Sum.inr false : Bool ⊕ Bool) ≠ Sum.inr true :=
  ⟨⟨false, rfl⟩, ⟨true, rfl⟩, by decide⟩

/-- **List is singular** for the empty-absence reading: the only absent value is `[]`, like the base (its
plural direction is over-determination, not an absence). -/
theorem list_center_is_singular : ∀ l, listAbsence.absent l → l = [] := fun _ h => h

/-! ## Part 4: what happens to the boundary -/

/-- **Untouched: the channel is absence-agnostic.** `guard_is_universal` applies at any absence-structure's
value space, mentioning nothing about the absence. Confirmed on the term, not assumed. -/
theorem channel_untouched (A : AbsenceStructure) {X : Type} {g : A.V → A.V}
    (hg : ∀ v, g v ≠ v) (c : X → X → A.V) : ¬ Function.Surjective c :=
  guard_is_universal c hg

/-- **Untouched: the channel-uniformity content is generic.** The universality of the guard is the hole
(`no_reflexive_object`) at any absence-structure, so `apophatic_uniformity_is_channel_uniformity`, stated over
`Option Bool`, is one instance of an absence-agnostic fact. -/
theorem channel_uniformity_is_generic (A : AbsenceStructure) {X : Type} {g : A.V → A.V}
    (hg : ∀ v, g v ≠ v) (c : X → X → A.V) :
    guard_is_universal c hg = no_reflexive_object hg c := rfl

/-- **Untouched: the arms are absence-agnostic.** `two_adjacent_arms` (connected-not-fused) holds at any
absence-structure, mentioning nothing about the absence. -/
theorem arms_untouched (A : AbsenceStructure) {X : Type} (c : X → X → A.V) :
    (∀ g : A.V → A.V, (∀ v, g v ≠ v) → ¬ Function.Surjective c)
    ∧ (∃ build : X → (X → A.V), ∀ x, build x = c x) :=
  two_adjacent_arms c

/-! ## The verdict

Part 1: the skeleton generalizes cleanly. The collision (`boundary_collision`) and both moves
(`totalization_exists`, `partialization_exists`) go through over a bare absence-structure, from the predicate
alone. What refuses: the cost asymmetry (`model_arms_invert`, the money-pump) and the concrete
`imprecise`/`Fin 4` proofs need Option-specific structure and belong in the instances, not the generic
statement.

Part 2: the base survives intact. `base_collision_is_generic` shows the base collision is the generic one at
`maybeAbsence`, while the canonical concrete proofs, decides, and ancestry stay unchanged instance facts.
Maybe is distinguished by freeness (`base_embeds_out`, `maybe_free_pointed`), not convention, and its
distinguishing structural property is `singular_absence`.

Part 3: the five levels sit as instances with their absence-structures explicit (`writerAbsence`,
`readerAbsence`, `stateAbsence`, `exceptAbsence`, `listAbsence`). The collision specializes to each
(`collision_at_each_level`), and the center's cardinality is instance-dependent: Except plural
(`except_center_is_plural`), List and the base singular (`list_center_is_singular`, `singular_absence`).

Part 4: the boundary splits three ways, confirmed on the term. Generic: the collision. Untouched: the channel
and arms (`channel_untouched`, `channel_uniformity_is_generic`, `arms_untouched`) mention no absence-structure
and are unaffected. Changed: the prohibition's rationale splits (collision generic, concealment
instance-specific) and the permitted moves carry a partial order with the prohibited move at the top, with the
base as the one-element degenerate case, as `TowerStructure` established (`one_prohibition_permitted_grew`,
`partial_totalizations_are_ranked`, `collision_without_concealment`).

Part 5: the corrected asymmetry. 5.c.1 read the model layer as apophatic-unique versus cataphatic-open. Under
this structure both sides are skeleton-plus-instances, both open, differently indexed: cataphatic instances by
forgetful functor, apophatic instances by absence-structure. The real asymmetry is not open-versus-closed but
that the apophatic side has a distinguished base, `Maybe`, initial and free (`base_embeds_out`), while the
cataphatic side has none, its free constructions all on equal footing.

The verdict: the apophatic model restructures cleanly as skeleton plus instances. The collision, the moves, and
the channel and arms generalize; the base survives intact as the free-pointed instance; the five levels sit as
absence-structure instances with instance-dependent centers. What does not generalize is identified, not
forced: the cost asymmetry and the concrete proofs stay in the instances, and the prohibition's changed shape
is a real difference, not a failure. Nothing here is resolved; this is a validated blueprint. -/

end Chiralogy.ApophaticGeneric
