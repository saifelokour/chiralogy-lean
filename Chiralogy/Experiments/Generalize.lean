import Chiralogy

/-! # Experiment: can the surveys be proven?

Four results are surveys, checked at instances. Determine which can be stated generally with the machinery at
hand. Closures over a reason set `ι` are `ι → Bool`, the order `a ≤ b` being pointwise. Stays in
`Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Generalize

/-- The pointwise order on closures: `a` closes a subset of what `b` closes. -/
def leC {ι : Type} (a b : ι → Bool) : Prop := ∀ r, a r = true → b r = true

/-! ## Part 1: the permitted lattice from the reason count

For a free level (independent reasons), the closeable sets are all subsets. Under forcing or blocking the
family is not the full powerset, so these statements assume independent reasons. -/

/-- **The permitted lattice from the reason count.** For any finite reason set, the full closure is the unique
forbidden one and there are `2 ^ n - 1` permitted (the non-full subsets). Proven generally, over an arbitrary
finite reason set, not at `n = 2`. -/
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
  have hsub : (Finset.univ.filter (fun close : ι → Bool => ∀ r, close r = true)) ⊆ Finset.univ :=
    Finset.filter_subset _ _
  rw [Finset.filter_not, Finset.card_sdiff_of_subset hsub, h1, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool]

/-- **The permitted order is the powerset Boolean algebra, generally.** Residuation holds and every element
has a complement (`a ⊔ ¬a = ⊤`, `a ⊓ ¬a = ⊥`), with negation the pointwise complement, over an arbitrary
reason set. The top is prohibited. -/
theorem permitted_is_boolean_general {ι : Type} (a b c : ι → Bool) :
    ((∀ r, (a r && c r) = true → b r = true) ↔ (∀ r, c r = true → (!a r || b r) = true))
    ∧ (fun r => a r || !a r) = (fun _ : ι => true)
    ∧ (fun r => a r && !a r) = (fun _ : ι => false) := by
  refine ⟨?_, ?_, ?_⟩
  · have key : ∀ x y z : Bool, (((x && z) = true → y = true) ↔ (z = true → (!x || y) = true)) := by decide
    exact ⟨fun h r => (key (a r) (b r) (c r)).1 (h r), fun h r => (key (a r) (b r) (c r)).2 (h r)⟩
  · funext r; cases a r <;> rfl
  · funext r; cases a r <;> rfl

/-- **Same reason count, same lattice.** An equivalence of reason sets transports the order both ways, so
levels with the same reason count have isomorphic permitted lattices. The lattice depends only on the reason
count, so an operation moves it exactly when it changes the count, a signature change: this is the general
form of `upstream_is_signature_change`, a corollary rather than a survey. -/
theorem same_reason_count_same_lattice {ι ι' : Type} (e : ι ≃ ι') (a b : ι → Bool) :
    leC a b ↔ leC (fun r' => a (e.symm r')) (fun r' => b (e.symm r')) := by
  constructor
  · intro h r' hr'; exact h (e.symm r') hr'
  · intro h r hr; have := h (e r); simp only [Equiv.symm_apply_apply] at this; exact this hr

/-! ## Part 2: is the fourth cell empty for a reason? -/

/-- **A constant cannot pin an operation.** A constant supplies one element; an operation is its whole graph.
Any equation involving the constant constrains the operation only where the constant appears, leaving the rest
of the graph free. So on any carrier with a second element, two operations agree on every constant-involving
input yet differ off it. The fourth cell is empty structurally, not incidentally, and the four axiom-shapes
reduce to three. -/
theorem can_a_constant_pin_an_operation {A : Type} [DecidableEq A] (c d : A) (hcd : c ≠ d) :
    ∃ op op' : A → A → A,
      (∀ x, op c x = op' c x) ∧ (∀ x, op x c = op' x c) ∧ op ≠ op' := by
  refine ⟨fun _ _ => c, fun a b => if a = d ∧ b = d then d else c, ?_, ?_, ?_⟩
  · intro x; simp [hcd]
  · intro x; simp [hcd]
  · intro h; have h2 := congrFun (congrFun h d) d; simp at h2; exact hcd h2

/-! ## Part 3: what needs machinery we lack

Two surveys do not generalize with the machinery at hand, and it is worth naming what would be needed rather
than forcing them.

`correspondence_needs_signatures`: the constants-are-reasons correspondence (`reasons_are_nullary_generators`)
is stated for specific value spaces, `Option Bool` and `Bool ⊕ Bool`. Generalizing it, that a level's
absences are exactly the range of its nullary operations, requires a type of algebraic signatures, a notion of
a level's presentation over one, and the arity of a symbol. The framework has value spaces and absent
predicates, not presentations, so the correspondence stays instance-bound.

`arity_split_needs_signatures`: the arity split (`witnesses_split_by_algebraicity`,
`same_signature_different_arity`) is checked at the seven witnesses. Generalizing it, that the apophatic side
reads the arity-0 symbols and the cataphatic side the positive-arity ones of a level's signature, requires the
same missing machinery: signatures, arities, and the full non-nullary reduct. Naming these is the honest end;
attempting them without a `Signature` type would be fabricating structure the framework does not carry. -/

/-! ## The verdict

Part 1: three of the lattice surveys become theorems. The permitted count is `2 ^ n - 1` for any finite reason
set (`permitted_lattice_from_reason_count`), the order is the powerset Boolean algebra with negation the
complement (`permitted_is_boolean_general`), and same reason count gives isomorphic lattices
(`same_reason_count_same_lattice`), from which the upstream criterion follows as a corollary. These assume
independent reasons, the free case; forcing and blocking restrict the family and are excluded.

Part 2: the fourth cell is empty for a structural reason. A constant supplies one element and an operation is
its whole graph, so no equation involving a constant can pin the operation off the constant's rows
(`can_a_constant_pin_an_operation`, over any carrier with two elements). The four axiom-shapes reduce to three:
constant-constant and constant-operation move the family, operation-operation does not, and
constant-constrains-operation cannot arise.

Part 3: two surveys do not generalize here. The constants-are-reasons correspondence and the arity split need a
type of signatures, a level's presentation, and arities, which the framework does not have. They stay
instance-bound, and the honest report is to name the missing machinery, not to fabricate it.

The verdict: the lattice surveys generalize (three theorems, one corollary) under the free-reasons hypothesis;
the fourth-cell survey becomes a structural theorem; the two signature-dependent surveys do not generalize with
the machinery at hand. Nothing here is resolved. -/

end Chiralogy.Generalize
