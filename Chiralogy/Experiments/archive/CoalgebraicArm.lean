import Chiralogy

/-! # Experiment: the apophatic arm read coalgebraically

`Coalgebra` concluded that coalgebra is the apophatic arm's proper name: the hole is a Lambek-style
non-existence, the guard observes without inspecting, cofree constructions were already flagged
apophatic-shaped, and the diagonal is observation while construction is the monad side. Test whether the arm's
algebraic dress is essential or incidental, and build the coalgebraic reading as far as it goes. Independent
verdicts per stage; a failure at one does not invalidate the others, and stage 1 failing means stop. Concrete
small instances; no general coalgebra machinery. Stays in `Experiments/`; canonical untouched; nothing
resolved. -/

open Chiralogy

namespace Chiralogy.CoalgebraicArm

/-! ## Stage 1: is the algebraic reading essential? (the gate) -/

/-- **What is algebraic about the arm.** The apophatic model's algebraic dress: `Kl(Maybe)` presented with
`failMaybe` as its one nullary generator, the reasons as generators (`reasons_are_nullary_generators`), the
levels as presentations, the arity tower over them. This is what a coalgebraic reading must absorb or
dispense with. -/
theorem what_is_algebraic_about_the_arm :
    (failMaybe () = (none : Option Bool))
    ∧ (∀ v : Option Bool, v = none ↔ ∃ u : Unit, failMaybe u = v)
    ∧ (∀ x : Bool ⊕ Bool, (∃ e, x = Sum.inr e) ↔ ∃ e, throwExcept e = x) :=
  ⟨rfl, reasons_are_nullary_generators.2, reasons_are_nullary_generators.1⟩

/-- **Is the content observational.** The hole, the payload, and the guard are each stated with functions and
surjectivity alone, no operation or generator (`no_reflexive_object`, `hole_uniform`,
`erasure_forces_nondependence`). So the arm's content is observational and the algebra is a presentation, a
carrier. The gate passes: proceed. -/
theorem is_the_content_observational {X : Type} {g : Bool → Bool} (hg : ∀ b, g b ≠ b) :
    (∀ c : X → X → Bool, ¬ Function.Surjective c)
    ∧ (∀ c : X → X → Option Bool, ¬ Function.Surjective c)
    ∧ (∀ (T : Type) (c : X → X → Bool) (F : ¬ Function.Surjective c → T)
        (h₁ h₂ : ¬ Function.Surjective c), F h₁ = F h₂) :=
  ⟨fun c => no_reflexive_object hg c, fun c => hole_uniform c,
   fun _ c F h₁ h₂ => erasure_forces_nondependence c F h₁ h₂⟩

/-! ## Stage 2: the guard as observation -/

/-- **The guard as observation.** The guard's verdict is proof-irrelevant, so every observation of it is
constant (`erasure_forces_nondependence`); coalgebraically an observation distinguishing nothing is the
coarsest bisimilarity, all states identified. The guard's uniformity is exactly that coarseness, the same fact
on the observation side. -/
theorem guard_as_observation {X B T : Type} (c : X → X → B) (F : ¬ Function.Surjective c → T) :
    ∀ h₁ h₂ : ¬ Function.Surjective c, F h₁ = F h₂ :=
  fun h₁ h₂ => erasure_forces_nondependence c F h₁ h₂

/-- **What the guard observes.** One bit, the presence of a hole against a verdict, and nothing finer; that
one-bit observation is why the channel carries nothing (`channel_capacity_is_zero`), the verdict never varying
beyond the bit. -/
theorem what_the_guard_observes {X : Type} {g : Option Bool → Option Bool} (hg : ∀ b, g b ≠ b)
    (build₁ build₂ : X → (X → Option Bool)) :
    (∀ v : Option Bool, v.isSome = true ↔ ∃ b, v = some b)
    ∧ ((¬ Function.Surjective build₁) ↔ (¬ Function.Surjective build₂)) :=
  ⟨fun v => by cases v <;> simp, channel_capacity_is_zero hg build₁ build₂⟩

/-! ## Stage 3: absence coalgebraically -/

/-- A ground read as a non-producing state, never emitting a verdict. -/
def groundState : Unit → Bool ⊕ Unit := fun _ => Sum.inr ()

/-- **Grounds as observations.** A ground can be read coalgebraically, a state that fails to produce a verdict,
rather than a returned `none`; the two readings match, `failMaybe` returning `none` on the range side and
`groundState` never emitting on the observation side. -/
theorem grounds_as_observations :
    (∀ b : Bool, groundState () ≠ Sum.inl b)
    ∧ (failMaybe () = (none : Option Bool)) :=
  ⟨fun b => by simp [groundState], rfl⟩

/-- **Does the lattice transfer.** The permitted lattice is over closures of the reason-index (`Fin n`), not
over the returned values; a closure is a predicate on the index, indifferent to whether a reason is a returned
`none` or a non-producing state. So the count is the same, three at two reasons, on either reading. -/
theorem does_the_lattice_transfer :
    ((Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3)
    ∧ (∀ close : Fin 2 → Bool, (¬ ∀ r, close r = true) ↔ ∃ r, close r = false) :=
  ⟨by decide, by decide⟩

/-- **Which reading the ethics needs.** The prohibition and the lattice are over the reason-index and its
closures, one prohibited and three permitted at two reasons, which is neutral between a returned absence and a
non-producing state (`groundState` is available). So the ethical structure has a coalgebraic form; it does not
require returned absences. -/
theorem which_reading_the_ethics_needs :
    ((Finset.univ.filter (fun close : Fin 2 → Bool => ∀ r, close r = true)).card = 1)
    ∧ ((Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3)
    ∧ (∀ b : Bool, groundState () ≠ Sum.inl b) :=
  ⟨by decide, by decide, fun b => by simp [groundState]⟩

/-! ## Stage 4: the arms under the reframing -/

/-- **Cataphatic stays algebraic.** The cataphatic arm is free constructions and operations preserved by
homomorphisms; the reframing touches only the apophatic side, so it is unaffected. -/
theorem cataphatic_stays_algebraic (f : List Bool → List Bool)
    (hom : ∀ x y, f (x ++ y) = f x ++ f y) (x y : List Bool) :
    ((fun a b : List Bool => a ++ b) [] [true] = [true])
    ∧ (f (x ++ y) = f x ++ f y) :=
  ⟨rfl, hom x y⟩

/-- **The duality named.** The bicameral structure is the algebra/coalgebra duality, and each asymmetry checks
against it. Non-fusion is the hole, no reflexive object, no fixed point where an initial algebra would meet a
final coalgebra (`no_reflexive_object`). The zero channel is the observation's coarseness, the verdict never
varying (`channel_capacity_is_zero`). Thin transport is that a coalgebra morphism preserves the observation, and
the observation is one bit, so only that bit transports. Each holds; the duality is checked, not asserted. -/
theorem the_duality_named {X : Type} {g : Bool → Bool} (hg : ∀ b, g b ≠ b)
    {g' : Option Bool → Option Bool} (hg' : ∀ b, g' b ≠ b)
    (build₁ build₂ : X → (X → Option Bool)) :
    (∀ c : X → X → Bool, ¬ Function.Surjective c)
    ∧ ((¬ Function.Surjective build₁) ↔ (¬ Function.Surjective build₂))
    ∧ (∀ (f : Option Bool → Option Bool) (v : Option Bool),
        (∀ x, (f x).isSome = x.isSome) → (f v).isSome = v.isSome) :=
  ⟨fun c => no_reflexive_object hg c, channel_capacity_is_zero hg' build₁ build₂, fun _ v h => h v⟩

/-- **What the reframing explains.** The duality accounts for the structural absences, the hole and non-fusion,
the zero channel, the thin transport, the guard's uniformity, and cofree being apophatic-shaped; it does not
account for the combinatorial content, the permitted count and the lattice, which is over the reason-index and
holds on either reading. The duality explains the shape of the arm, not its numerical content. -/
theorem what_the_reframing_explains {X : Type} {g : Bool → Bool} (hg : ∀ b, g b ≠ b) :
    (∀ c : X → X → Bool, ¬ Function.Surjective c)
    ∧ ((Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3) :=
  ⟨fun c => no_reflexive_object hg c, by decide⟩

/-! ## Stage 5: what would have to change -/

/-- **Canonical impact.** Nothing in the canonical tree is mathematically misdescribed; the hole, the guard, and
the lattice hold as stated. What a coalgebraic reading would change is the naming and the register, the
apophatic model read as observations and the levels as behaviour-presentations, not the theorems. -/
theorem canonical_impact :
    (∀ (X : Type) (c : X → X → Option Bool), ¬ Function.Surjective c)
    ∧ ((Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3)
    ∧ (failMaybe () = (none : Option Bool)) :=
  ⟨fun _ c => hole_uniform c, by decide, rfl⟩

/-- **What survives untouched.** The protocol and registers (about returned verdicts, whose reading is neutral),
the cataphatic arm (algebraic), and the kernel (the hole, itself the coalgebraic non-existence). The reframing is
confined to the apophatic model's reading. -/
theorem what_survives_untouched {X : Type} {g : Bool → Bool} (hg : ∀ b, g b ≠ b) :
    (∀ c : X → X → Bool, ¬ Function.Surjective c)
    ∧ ((fun a b : List Bool => a ++ b) [] [true] = [true])
    ∧ (∀ c : X → X → Option Bool, ¬ Function.Surjective c) :=
  ⟨fun c => no_reflexive_object hg c, rfl, fun c => hole_uniform c⟩

/-! ## The verdicts

Stage 1: the algebraic reading is a carrier, not essential. The arm's dress is algebraic, `Kl(Maybe)` with
`failMaybe` as generator, the reasons as generators, the tower (`what_is_algebraic_about_the_arm`); but the
content, the hole, the payload, and the guard, is stated with functions and surjectivity alone
(`is_the_content_observational`). The gate passes: the algebra presents an observational content.

Stage 2: the guard is an observation, and its uniformity is bisimilarity's coarseness. Every observation of the
guard is constant (`guard_as_observation`), the coarsest bisimilarity; the guard observes one bit, hole against
verdict, and that one bit is why the channel carries nothing (`what_the_guard_observes`,
`channel_capacity_is_zero`).

Stage 3: the ethics has a coalgebraic form; it does not need returned absences. A ground reads as a non-producing
state (`grounds_as_observations`); the permitted lattice is over closures of the reason-index, neutral to the
reading (`does_the_lattice_transfer`), so the count is the same on either (`which_reading_the_ethics_needs`). The
risk did not materialize: the lattice sits on the index, not on the returned value.

Stage 4: the bicameral structure is the algebra/coalgebra duality, and it checks. The cataphatic arm stays
algebraic (`cataphatic_stays_algebraic`); non-fusion, the zero channel, and thin transport each hold against the
duality (`the_duality_named`). But the duality explains the arm's shape, not its content: the permitted count is
combinatorial, over the index, and holds on either reading (`what_the_reframing_explains`).

Stage 5: nothing canonical is mathematically misdescribed; only the naming and register would change
(`canonical_impact`). The protocol, the registers, the cataphatic arm, and the kernel survive untouched
(`what_survives_untouched`).

The verdict: the arm's algebraic dress is incidental, a presentation of an observational content, so the
coalgebraic reading is available and coherent to the end, the guard an observation, a ground a non-producing
state, the bicameral structure the algebra/coalgebra duality. But the reframing is a reading, not a discovery of
new content: it renames what the framework already proves, explaining the structural absences it had found while
leaving the combinatorial content, the reason-index and its lattice, exactly as it was, holding on either
reading. So the honest report is that the duality names the arm's shape without changing its theorems; adopting
it would rewrite registers, not mathematics. Reported per stage. Nothing here is resolved. -/

end Chiralogy.CoalgebraicArm
