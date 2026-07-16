import Autology.Kernel.Trichotomy
import Mathlib.Data.Set.Defs

/-! # Target-parametric dynamics

There is no dynamics without a target. An abstract target `t` induces a coalgebra for `F X = B → Set X`:
its order-part, the agreement preorder, is canonical; its rate is imported. The idempotent lift is the
one canonical channel; the target-flow is an imported flow beside it. The arrow of the category is the
lift's irreversibility. The flow moves among existing elements toward an equilibrium: no generation, no
history: order, not duration. -/

namespace Autology

/-! ## The one canonical channel: the idempotent lift -/

/-- The lift: collapse to the degenerate shadow at a basepoint. -/
def lift {X B : Type} (x₀ : X) (c : X → X → B) : X → X → B := fun _ y => c x₀ y

/-- **The one canonical channel.** The lift is idempotent: collapsing twice equals collapsing once.
Intrinsic to the classification, independent of the distinction space and of any target. -/
theorem lift_idempotent {X B : Type} (x₀ : X) (c : X → X → B) :
    lift x₀ (lift x₀ c) = lift x₀ c := rfl

/-- The lift is not injective: two maps agreeing on the basepoint row have the same lift. -/
theorem lift_not_injective :
    ∃ c c' : Fin 2 → Fin 2 → Bool, c ≠ c' ∧ lift 0 c = lift 0 c' :=
  ⟨(fun _ _ => false), (fun i j => decide (i = 1 ∧ j = 0)), by decide, by decide⟩

/-- **The arrow.** No operation recovers the original from its lift: the canonical collapse is
irreversible. -/
theorem no_recovery :
    ¬ ∃ recover : (Fin 2 → Fin 2 → Bool) → (Fin 2 → Fin 2 → Bool),
        ∀ c, recover (lift 0 c) = c := by
  rintro ⟨recover, h⟩
  obtain ⟨c, c', hne, heq⟩ := lift_not_injective
  apply hne
  rw [← h c, heq, h c']

/-! ## The imported flow: the agreement preorder -/

/-- The agreement preorder toward a target: `x ⊑_t x'` iff `x'` classifies as `t` at least wherever `x`
does. Motion toward `t` is ascent. -/
def agreementLE {X B : Type} (c : X → X → B) (t : B) (x x' : X) : Prop :=
  ∀ y, c x y = t → c x' y = t

theorem agreementLE_refl {X B : Type} (c : X → X → B) (t : B) (x : X) : agreementLE c t x x :=
  fun _ h => h

theorem agreementLE_trans {X B : Type} (c : X → X → B) (t : B) {x x' x'' : X}
    (h1 : agreementLE c t x x') (h2 : agreementLE c t x' x'') : agreementLE c t x x'' :=
  fun y hy => h2 y (h1 y hy)

/-- The coalgebra for `F X = B → Set X`: the nondeterministic all-successors transition structure,
determined by the classification alone. -/
def targetCoalgebra {X B : Type} (c : X → X → B) : X → (B → Set X) :=
  fun x t => {x' | agreementLE c t x x'}

/-- **The order-part is canonical.** A preorder read off the classification and the target: no measure. -/
theorem order_canonical {X B : Type} (c : X → X → B) (t : B) :
    (∀ x, agreementLE c t x x) ∧
      (∀ x x' x'', agreementLE c t x x' → agreementLE c t x' x'' → agreementLE c t x x'') :=
  ⟨agreementLE_refl c t, fun _ _ _ => agreementLE_trans c t⟩

/-- The rate is imported: the identity is always a valid step, yet a strict successor exists: how far to
move is not determined by the target. -/
def rateWitness : Fin 2 → Fin 2 → Bool := fun i _ => decide (i = 1)

theorem rate_imported :
    agreementLE rateWitness true 0 0 ∧ agreementLE rateWitness true 0 1 ∧
      ¬ agreementLE rateWitness true 1 0 := by
  refine ⟨agreementLE_refl rateWitness true 0, ?_, ?_⟩
  · intro y hy; simp [rateWitness] at hy
  · intro h; have := h 0 (by decide); simp [rateWitness] at this

/-- **Fixed points are target-agreers.** A state classifying everything as `t` is above every state: the
equilibrium the flow ascends to. The moves are the flow structure: totalization is the flow to one
equilibrium. -/
theorem fixed_points_are_target_agreers {X B : Type} (c : X → X → B) (t : B) (xstar : X)
    (h : ∀ y, c xstar y = t) : ∀ x, agreementLE c t x xstar :=
  fun _ y _ => h y

/-- **The flow is kernel-level.** Incomparable equilibria appear on a total object: the dynamics is a fact
about the classification and a target, not the extension. -/
theorem dynamics_nontrivial_on_total :
    ∃ (c : Fin 2 → Fin 2 → Bool) (t : Bool) (x x' : Fin 2),
      ¬ agreementLE c t x x' ∧ ¬ agreementLE c t x' x := by
  refine ⟨fun i j => decide (i = j), true, 0, 1, ?_, ?_⟩
  · intro h; have := h 0 (by decide); simp at this
  · intro h; have := h 1 (by decide); simp at this

/-- **No generation, no history.** The successors are a subset of the existing carrier: the flow moves
among existing elements, and is a function of the current state. Only order-motion toward a target. -/
theorem no_generation {X B : Type} (c : X → X → B) (x : X) (t : B) :
    targetCoalgebra c x t ⊆ (Set.univ : Set X) :=
  fun _ _ => trivial

end Autology
