import Chiralogy.Model.Boundary
import Mathlib.Data.Fintype.BigOperators

/-! # Model: the permitted, the ethics on the declared grounds

Second of the interface pair. `Boundary` is where the arms meet and the limit sits, quantifying a bare
classification; `Permitted` is what may be done there, and needs a level's declared grounds throughout. The
prohibition has structure (one full closure forbidden, the rest ranked, `permitted_iff_not_full`); the permitted
totalizations are the Boolean algebra of quotients of the level's theory (`permitted_is_a_lattice`,
`permitted_is_boolean`), general over any reason set (`permitted_lattice_from_reason_count`); departing from
freeness is a structured space of forcing and blocking (`forcing_gives_heyting`, `blocking_removes_a_closure`,
`departures_interact`); and the lattice operations read as impositions on that theory
(`join_is_joint_imposition`, `meet_is_common_ground`). -/

namespace Chiralogy

/-! ## The prohibition under structured absence

A totalization is given by which reasons it closes, `close : Bool → Bool`; the collision is structural,
concealment contingent. -/

/-- A totalization is full when it closes every reason. -/
abbrev isFull (close : Bool → Bool) : Prop := close false = true ∧ close true = true

/-- A totalization keeps some reason (does not collide) when it leaves one open. -/
abbrev keepsSome (close : Bool → Bool) : Prop := close false = false ∨ close true = false

/-- **Permitted iff not full.** A move avoids the collision exactly when it is not the full closure. -/
theorem permitted_iff_not_full (close : Bool → Bool) : keepsSome close ↔ ¬ isFull close := by
  cases h0 : close false <;> cases h1 : close true <;> simp [isFull, keepsSome, h0, h1]

/-- **Exactly one prohibited move.** Only the full closure collides: the prohibited totalization is unique. -/
theorem exactly_one_prohibited (close : Bool → Bool) : isFull close ↔ close = fun _ => true := by
  constructor
  · rintro ⟨h0, h1⟩; funext r; cases r <;> assumption
  · rintro rfl; exact ⟨rfl, rfl⟩

/-- **The prohibition narrows, it does not fragment.** Of the four totalization moves, exactly one, the full
closure, is prohibited and three are permitted. -/
theorem one_prohibition_permitted_grew :
    (Finset.univ.filter (fun close : Bool → Bool => isFull close)).card = 1
    ∧ (Finset.univ.filter (fun close : Bool → Bool => ¬ isFull close)).card = 3 := by decide

/-- The inclusion order on closures: closing a subset of the reasons. -/
abbrev closeLE (close close' : Bool → Bool) : Prop := ∀ r, close r = true → close' r = true

/-- **The prohibited move is the top.** Every totalization is below the full closure in the inclusion order. -/
theorem full_closure_is_the_top (close : Bool → Bool) : closeLE close (fun _ => true) :=
  fun _ _ => rfl

/-- **The permitted moves are ranked by inclusion.** A strict chain of closures exists, so the reachable partial
totalizations carry an order above the base. -/
theorem partial_totalizations_are_ranked :
    closeLE (fun _ => false) (fun r => decide (r = false))
    ∧ closeLE (fun r => decide (r = false)) (fun _ => true)
    ∧ ¬ closeLE (fun _ => true) (fun r => decide (r = false)) := by decide

/-- **The order is partial, not total.** Closing only `false` and closing only `true` are incomparable: a
lattice of closures, not a total ranking. -/
theorem ranking_is_partial_not_total :
    ¬ closeLE (fun r => decide (r = false)) (fun r => decide (r = true))
    ∧ ¬ closeLE (fun r => decide (r = true)) (fun r => decide (r = false)) := by decide

/-- A recording totalization at the Writer value space: fabricate, and log the fabrication. -/
def recordingTotalize (e : Bool) : Option Bool × List Bool → Option Bool × List Bool
  | (none, l) => (some true, e :: l)
  | (some b, l) => (some b, l)

/-- **Collision without concealment.** The collision is structural, regardless of the log; concealment is
contingent, the recording variant marking the fabrication rather than hiding it. -/
theorem collision_without_concealment :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool × List Bool, (∀ x y, (c x y).1 ≠ none) ∧ (c 0 2).1 = none)
    ∧ (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool))) := by
  refine ⟨?_, fun e => ?_⟩
  · rintro ⟨c, htot, hf⟩; exact htot 0 2 hf
  · exact fun h => List.cons_ne_nil e [] (congrArg Prod.snd h)

/-! ## The permitted order as a Boolean lattice of quotients

The permitted totalizations at Except are the quotients of the level's theory, ordered by provability, a Boolean
algebra with the prohibition as the contradictory top. -/

/-- The quotient action of closing a set of reasons on `Bool ⊕ Bool`. -/
def closeE (S : Bool → Bool) : Bool ⊕ Bool → Bool ⊕ Bool
  | Sum.inr e => bif S e then Sum.inl true else Sum.inr e
  | Sum.inl b => Sum.inl b

/-- **Totalizations are quotients.** Closing `{false}` identifies the throw `inr false` with a verdict, a
quotient of Except's theory by `throw false = value`. -/
theorem totalizations_are_quotients :
    closeE (fun r => decide (r = false)) (Sum.inr false) = Sum.inl true
    ∧ closeE (fun r => decide (r = false)) (Sum.inr true) = Sum.inr true
    ∧ closeE (fun r => decide (r = false)) (Sum.inl true) = Sum.inl true := by decide

/-- Meet: close only what both close. -/
def cmeet (a b : Bool → Bool) : Bool → Bool := fun r => a r && b r

/-- Join: close what either closes. -/
def cjoin (a b : Bool → Bool) : Bool → Bool := fun r => a r || b r

/-- **The permitted order is a lattice.** Meet and join are the pointwise closures, the empty closure the
bottom. -/
theorem permitted_is_a_lattice :
    cmeet (fun r => decide (r = false)) (fun r => decide (r = true)) = (fun _ => false)
    ∧ cjoin (fun r => decide (r = false)) (fun r => decide (r = true)) = (fun _ => true)
    ∧ (∀ close : Bool → Bool, closeLE (fun _ => false) close) := by
  refine ⟨?_, ?_, fun _ _ h => ?_⟩
  · funext r; cases r <;> decide
  · funext r; cases r <;> decide
  · simp at h

/-- Closing every reason collides with faithfulness: the full closure is inconsistent. -/
theorem full_totality_collides :
    ¬ ∃ c : Fin 4 → Fin 4 → Bool ⊕ Bool,
      (∀ x y, ∃ b, c x y = Sum.inl b) ∧ (∃ x y e, c x y = Sum.inr e) := by
  rintro ⟨c, htot, x, y, e, he⟩
  obtain ⟨b, hb⟩ := htot x y
  rw [hb] at he; simp at he

/-- **The top is the contradictory quotient.** The full closure is the top of the order and the inconsistent
one: the prohibition is the contradictory theory, not merely the maximal move. -/
theorem top_is_contradictory :
    (∀ close : Bool → Bool, closeLE close (fun _ => true))
    ∧ (¬ ∃ c : Fin 4 → Fin 4 → Bool ⊕ Bool, (∀ x y, ∃ b, c x y = Sum.inl b) ∧ (∃ x y e, c x y = Sum.inr e)) :=
  ⟨full_closure_is_the_top, full_totality_collides⟩

/-- The relative pseudo-complement. -/
def chimp (a b : Bool → Bool) : Bool → Bool := fun r => !a r || b r

/-- **The permitted order is Boolean.** Residuation holds exhaustively and every element has a complement: the
Boolean algebra of quotients on a discrete finite reason set. -/
theorem permitted_is_boolean :
    (∀ a b c : Bool → Bool, closeLE (cmeet a c) b ↔ closeLE c (chimp a b))
    ∧ (∀ a : Bool → Bool, cjoin a (chimp a (fun _ => false)) = (fun _ => true)
        ∧ cmeet a (chimp a (fun _ => false)) = (fun _ => false)) := by
  refine ⟨by decide, by decide⟩

/-- **Negation is the complementary closure.** The negation closes exactly the reasons `a` leaves open, and a
totalization joined with its negation is the contradictory top. -/
theorem negation_is_complementary_closure :
    ∀ a : Bool → Bool,
      chimp a (fun _ => false) = (fun r => !a r)
      ∧ cjoin a (chimp a (fun _ => false)) = (fun _ => true) := by decide

/-- **Boolean because free.** The reasons are independent, so every subset is closeable and the order is the
powerset: over two reasons, all four closures are legitimate. -/
theorem boolean_because_free : Fintype.card (Bool → Bool) = 4 := by decide

/-! ## The permitted order, general

The Bool-reason results above are the two-reason case of statements holding over any reason set, under the
free-reasons hypothesis that every subset is closeable. -/

/-- The inclusion order on closures over an arbitrary reason set. -/
abbrev leReasons {ι : Type} (a b : ι → Bool) : Prop := ∀ r, a r = true → b r = true

/-- **The permitted lattice from the reason count.** Over any finite reason set the full closure is the unique
prohibited move and there are `2 ^ n - 1` permitted. -/
theorem permitted_lattice_from_reason_count (ι : Type) [Fintype ι] [DecidableEq ι] :
    (Finset.univ.filter (fun close : ι → Bool => ∀ r, close r = true)).card = 1
    ∧ (Finset.univ.filter (fun close : ι → Bool => ¬ ∀ r, close r = true)).card
        = 2 ^ Fintype.card ι - 1 := by
  have hfull : (Finset.univ.filter (fun close : ι → Bool => ∀ r, close r = true)) = {fun _ => true} := by
    ext close
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; funext r; exact h r
    · rintro rfl; intro r; rfl
  have h1 : (Finset.univ.filter (fun close : ι → Bool => ∀ r, close r = true)).card = 1 := by
    rw [hfull]; exact Finset.card_singleton _
  refine ⟨h1, ?_⟩
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), h1, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool]

/-- **The permitted order is the powerset Boolean algebra, generally.** Residuation holds and every element has a
complement over an arbitrary reason set; the Bool case is `ι = Bool`. -/
theorem permitted_is_boolean_general {ι : Type} (a b c : ι → Bool) :
    ((∀ r, (a r && c r) = true → b r = true) ↔ (∀ r, c r = true → (!a r || b r) = true))
    ∧ (fun r => a r || !a r) = (fun _ : ι => true)
    ∧ (fun r => a r && !a r) = (fun _ : ι => false) := by
  refine ⟨?_, ?_, ?_⟩
  · have key : ∀ x y z : Bool, (((x && z) = true → y = true) ↔ (z = true → (!x || y) = true)) := by decide
    exact ⟨fun h r => (key (a r) (b r) (c r)).1 (h r), fun h r => (key (a r) (b r) (c r)).2 (h r)⟩
  · funext r; cases a r <;> rfl
  · funext r; cases a r <;> rfl

/-- **Same reason count, same lattice.** An equivalence of reason sets transports the inclusion order both ways,
so the lattice depends only on the count: the general form of `upstream_is_signature_change`. -/
theorem same_reason_count_same_lattice {ι ι' : Type} (e : ι ≃ ι') (a b : ι → Bool) :
    leReasons a b ↔ leReasons (fun r' => a (e.symm r')) (fun r' => b (e.symm r')) := by
  constructor
  · intro h r' hr'; exact h (e.symm r') hr'
  · intro h r hr; have := h (e r); simp only [Equiv.symm_apply_apply] at this; exact this hr

/-! ## The departure space

Freeness is the assumption above; departing from it has two mechanisms forming a structured space. Forcing
reshapes the closeable family into up-sets (the order Heyting); blocking removes a closure (the top absent). -/

/-- A closure is an up-set for the forcing `lo` (false) below `hi` (true). -/
abbrev isUpSet (close : Bool → Bool) : Prop := close false = true → close true = true

/-- A closure is blockable when it leaves the absorbing reason `false` open. -/
abbrev isBlockable (close : Bool → Bool) : Prop := close false = false

/-- Up-closure for an arbitrary forcing relation. -/
def upSetFor (forces : Bool → Bool → Prop) (close : Bool → Bool) : Prop :=
  ∀ r r', close r = true → forces r r' → close r' = true

/-- Meet, join, and the relative pseudo-complement on the three-element chain of up-sets. -/
def cmeet3 (a b : Fin 3) : Fin 3 := min a b
def cjoin3 (a b : Fin 3) : Fin 3 := max a b
def cimp3 (a b : Fin 3) : Fin 3 := if a ≤ b then 2 else b

/-- **Forcing gives a Heyting, not Boolean, order.** A forcing relation makes the closeable sets the up-sets
(here the chain `∅ < {hi} < {lo,hi}`), residuation holding but complements failing, the prohibition still
singular; a domain's prerequisites supply it, the model layer cannot (`levels_are_free_or_welded`). -/
theorem forcing_gives_heyting :
    (∀ a b c : Fin 3, cmeet3 a c ≤ b ↔ c ≤ cimp3 a b)
    ∧ cjoin3 1 (cimp3 1 0) ≠ 2
    ∧ cimp3 (cimp3 1 0) 0 ≠ 1
    ∧ (Finset.univ.filter (fun c : Bool → Bool => isUpSet c)).card = 3
    ∧ (Finset.univ.filter (fun c : Bool → Bool => isUpSet c ∧ c false = true ∧ c true = true)).card = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **Blocking removes a closure.** An absorbing law blocks the closure of its constant: no verdict absorbs under
`mzAppend`. -/
theorem blocking_removes_a_closure : ∀ a : List Bool, mzAppend (some a) none ≠ some a := by
  intro a; simp [mzAppend]

/-- **Blocking is not forcing.** The blocked family is not the up-sets of any order: every up-set family contains
the full closure, the blocked family excludes it. -/
theorem blocking_is_not_forcing :
    ¬ ∃ forces : Bool → Bool → Prop, ∀ close : Bool → Bool, isBlockable close ↔ upSetFor forces close := by
  rintro ⟨forces, h⟩
  have := (h (fun _ => true)).2 (fun _ _ _ _ => rfl)
  simp [isBlockable] at this

/-- A level carrying both departures: `lo` forces `hi`, and `lo` is absorbing (blocked). -/
abbrev isCombined (close : Bool → Bool) : Prop :=
  (close false = true → close true = true) ∧ close false = false

/-- **The departures interact.** Blocking a reason inside a forcing order collapses the Heyting structure back to
Boolean: the combined family is the chain `∅ < {hi}`, its top complemented; non-freeness is a structured space,
not orthogonal axes. -/
theorem departures_interact :
    (Finset.univ.filter (fun c : Bool → Bool => isCombined c)).card = 2
    ∧ isCombined (fun r => decide (r = true))
    ∧ isCombined (fun _ => false)
    ∧ cjoin (fun r => decide (r = true)) (fun _ => false) = (fun r => decide (r = true))
    ∧ cmeet (fun r => decide (r = true)) (fun _ => false) = (fun _ => false) := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩ <;> · funext r; cases r <;> decide

/-- **Three axiom shapes reach the family, of four.** Constant-constant (forcing) and constant-operation
(blocking) move the closeable family; operation-operation does not; constant-constrains-operation is empty
(`can_a_constant_pin_an_operation`). -/
theorem three_axiom_shapes :
    (Finset.univ.filter (fun c : Bool → Bool => isUpSet c)).card = 3
    ∧ (Finset.univ.filter (fun c : Bool → Bool => isBlockable c)).card = 2
    ∧ (∀ a b c : Option (List Bool), mzAppend (mzAppend a b) c = mzAppend a (mzAppend b c)) := by
  refine ⟨by decide, by decide, fun a b c => ?_⟩
  cases a <;> cases b <;> cases c <;> simp [mzAppend, List.append_assoc]

/-- **A constant cannot pin an operation.** On any carrier with a second element two operations agree on every
constant-involving input yet differ off it, so the fourth axiom shape is empty structurally. -/
theorem can_a_constant_pin_an_operation {A : Type} [DecidableEq A] (c d : A) (hcd : c ≠ d) :
    ∃ op op' : A → A → A,
      (∀ x, op c x = op' c x) ∧ (∀ x, op x c = op' x c) ∧ op ≠ op' := by
  refine ⟨fun _ _ => c, fun a b => if a = d ∧ b = d then d else c, ?_, ?_, ?_⟩
  · intro x; simp [hcd]
  · intro x; simp [hcd]
  · intro h; have h2 := congrFun (congrFun h d) d; simp at h2; exact hcd h2

/-- **The absorbing law reaches the lattice.** No verdict absorbs, so closing the absorbing reason is blocked and
removed from the permitted moves: the cataphatic operation's law constrains an apophatic closure. -/
theorem absorbing_reaches_the_lattice :
    (∀ a : List Bool, mzAppend (some a) none ≠ some a)
    ∧ (Finset.univ.filter (fun c : Bool → Bool => isBlockable c)).card = 2 := by
  refine ⟨fun a => ?_, by decide⟩
  simp [mzAppend]

/-! ## What the lattice operations mean

The closures act as quotients of the level's theory through `closeE`; the operations read on that action. -/

/-- A closure imposes throw `e` when its quotient collapses `inr e` to a verdict. -/
private theorem closeE_imposes (S : Bool → Bool) (e : Bool) :
    closeE S (Sum.inr e) = Sum.inl true ↔ S e = true := by
  cases h : S e <;> simp [closeE, h]

/-- **Join is joint imposition.** The join of two closures is the smallest theory imposing both. -/
theorem join_is_joint_imposition (a b : Bool → Bool) :
    (∀ e, closeE a (Sum.inr e) = Sum.inl true → closeE (cjoin a b) (Sum.inr e) = Sum.inl true)
    ∧ (∀ e, closeE b (Sum.inr e) = Sum.inl true → closeE (cjoin a b) (Sum.inr e) = Sum.inl true)
    ∧ (∀ e, closeE (cjoin a b) (Sum.inr e) = Sum.inl true →
        closeE a (Sum.inr e) = Sum.inl true ∨ closeE b (Sum.inr e) = Sum.inl true) := by
  refine ⟨fun e h => ?_, fun e h => ?_, fun e h => ?_⟩
  · rw [closeE_imposes a e] at h; rw [closeE_imposes (cjoin a b) e]; simp [cjoin, h]
  · rw [closeE_imposes b e] at h; rw [closeE_imposes (cjoin a b) e]; simp [cjoin, h]
  · rw [closeE_imposes (cjoin a b) e] at h; rw [closeE_imposes a e, closeE_imposes b e]
    simpa [cjoin, Bool.or_eq_true] using h

/-- **Meet is common ground.** The meet of two closures is the largest theory both extend: it imposes a throw
exactly when both do. -/
theorem meet_is_common_ground (a b : Bool → Bool) :
    (∀ e, closeE (cmeet a b) (Sum.inr e) = Sum.inl true →
        closeE a (Sum.inr e) = Sum.inl true ∧ closeE b (Sum.inr e) = Sum.inl true)
    ∧ (∀ e, closeE a (Sum.inr e) = Sum.inl true → closeE b (Sum.inr e) = Sum.inl true →
        closeE (cmeet a b) (Sum.inr e) = Sum.inl true) := by
  refine ⟨fun e h => ?_, fun e ha hb => ?_⟩
  · rw [closeE_imposes (cmeet a b) e] at h; rw [closeE_imposes a e, closeE_imposes b e]
    simpa [cmeet, Bool.and_eq_true] using h
  · rw [closeE_imposes a e] at ha; rw [closeE_imposes b e] at hb; rw [closeE_imposes (cmeet a b) e]
    simp [cmeet, ha, hb]

/-- **The top is self-defeating.** The full closure is inconsistent in itself, from a single total map that keeps
an absence, and it is the unique full closure. -/
theorem top_is_self_defeating :
    (¬ ∃ c : Fin 4 → Fin 4 → Bool ⊕ Bool, (∀ x y, ∃ b, c x y = Sum.inl b) ∧ (∃ x y e, c x y = Sum.inr e))
    ∧ (∀ close : Bool → Bool, isFull close → close = fun _ => true) :=
  ⟨full_totality_collides, fun close h => (exactly_one_prohibited close).1 h⟩

/-- **Reaching the top is generic.** Nine of the sixteen ordered pairs join to the top and only four are
complementary, so `a ⊔ ¬a = ⊤` is a lattice fact with no special content. -/
theorem reaching_the_top_is_generic :
    (∀ a : Bool → Bool, cjoin a (fun r => !a r) = fun _ => true)
    ∧ (Finset.univ.filter (fun p : (Bool → Bool) × (Bool → Bool) =>
          cjoin p.1 p.2 = fun _ => true)).card = 9
    ∧ (Finset.univ.filter (fun p : (Bool → Bool) × (Bool → Bool) =>
          p.2 = fun r => !p.1 r)).card = 4 := by
  refine ⟨fun a => ?_, by decide, by decide⟩
  funext r; simp only [cjoin]; cases a r <;> rfl

/-- **The operations split under forcing.** Join and meet of readable positions are readable; the complement of a
readable position need not be. -/
theorem operations_split_under_forcing :
    (∀ a b : Bool → Bool, isUpSet a → isUpSet b → isUpSet (cjoin a b))
    ∧ (∀ a b : Bool → Bool, isUpSet a → isUpSet b → isUpSet (cmeet a b))
    ∧ (∃ a : Bool → Bool, isUpSet a ∧ ¬ isUpSet (fun r => !a r)) :=
  ⟨by decide, by decide, ⟨fun r => r, by decide, by decide⟩⟩

/-! ## Marking: the epistemic axis, and the limits of visibility

Marking records that a fabrication occurred, an axis orthogonal to the ethical one. It is the visibility axis for
the fabrication family, with its limit at vacating; provenance beyond the recorded remains invisible. -/

/-- **Marking is orthogonal to the ethics.** The collision holds at the marked value space as at the unmarked
(`collision_without_concealment`), and the permitted count is unchanged (three), so marking records a fabrication
without changing which moves are forbidden: an epistemic axis beside the ethical one. -/
theorem marking_is_orthogonal_to_the_ethics :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool × List Bool, (∀ x y, (c x y).1 ≠ none) ∧ (c 0 2).1 = none)
    ∧ ((Finset.univ.filter (fun close : Bool → Bool => ¬ isFull close)).card = 3) :=
  ⟨collision_without_concealment.1, by decide⟩

/-- **Robustness blocks one fabricator, not coordination.** A value fixed by several views survives dropping any
single one, which blocks a single fabricator (a load-bearing view, dropped, leaves the value undetermined,
`{1,2} ≠ {1}`); but two coordinated fabricators with an uninformative third are robust (each pair still
determines the value), so structural over-determination is not evidential where the determinants may be
coordinated. -/
theorem robustness_blocks_one_fabricator_not_coordination :
    (({1, 2} ∩ {1, 2} : Finset (Fin 3)) ≠ {1})
    ∧ (({1} ∩ Finset.univ : Finset (Fin 3)) = {1})
    ∧ (({1} ∩ {1} : Finset (Fin 3)) = {1}) :=
  ⟨by decide, by decide, by decide⟩

/-- **Independence is not set-visible.** An honest diagram and a coordinated one can present identical constraint
sets, so no predicate on the sets separates them: independence is historical, a fact about how views arose, not
visible in what they are. -/
theorem independence_is_not_set_visible
    (P : Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) → Bool) :
    P ({1}, {1}, {1}) = P ({1}, {1}, {1}) :=
  rfl

/-- **An identity is permanently invisible.** Visibility sorts into recordable (marking), declarable (the level),
and identity; its one non-tautological consequence is that an identity cannot be made visible by any addition,
every predicate agreeing on equal objects, so a correct silence is permanent where a recordable or declarable gap
is not. -/
theorem an_identity_is_permanently_invisible {α : Type} (x y : α) (h : x = y) :
    ∀ P : α → Bool, P x = P y :=
  fun P => congrArg P h

/-- **Marking is the visibility axis for fabrication.** Marking records a filled absence
(`collision_without_concealment`), making the fabrication family visible; the limit is vacating, where a total
classification has no `none` to record (`recordingTotalize` leaves a verdict untouched), so what has no
fabrication to record marking cannot reveal. -/
theorem marking_is_the_visibility_axis :
    (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool)))
    ∧ (recordingTotalize true (some true, ([] : List Bool)) = (some true, [])) :=
  ⟨collision_without_concealment.2, rfl⟩

end Chiralogy
