import Chiralogy

/-! # Experiment: is the register floor generic?

`RegisterFloors` found five domain floors sharing the form `neverPos`, the success verdict never firing, and showed
it is not determined by the ground-order. It did not test whether the form is generic on the codomain. Test that.
The concern: `neverPos` says a particular verdict never appears, stateable for any classification into `Option Bool`
with no domain content, the same shape as a generic two-valued disagreement. If so, the framework supplies the
floor-shape and the domains supply only which verdict counts as success. The discriminating question: is there an
asymmetry between the two present verdicts the codomain does not have, which a domain must supply, or are `some
true` and `some false` symmetric until a domain names one success? Stays in `Experiments/`; canonical untouched;
nothing resolved. -/

open Chiralogy

namespace Chiralogy.FloorGeneric

/-- Relabelling the codomain: swap the two present verdicts, fix the absence. -/
def swap : Option Bool → Option Bool := fun o => o.map not

/-- A floor-state witness on `Fin 2`: never fires `some true`, yet distinguishes its first row. -/
def wit2 : Fin 2 → Fin 2 → Option Bool := fun x _ => if x = 0 then some false else none

/-! ## Part 1: is the form stateable without domain content? -/

/-- **Never-fires is generic.** For any verdict `v`, with no domain input, "verdict `v` never appears" is
non-trivial: there are classifications avoiding `v` and classifications firing it. The form is stateable on the
bare codomain. -/
theorem never_fires_is_generic (v : Option Bool) :
    (∃ c : Fin 2 → Fin 2 → Option Bool, ∀ x y, c x y ≠ v)
    ∧ (∃ c : Fin 2 → Fin 2 → Option Bool, ¬ ∀ x y, c x y ≠ v) := by
  refine ⟨⟨fun _ _ => if v = some true then some false else some true, ?_⟩,
          ⟨fun _ _ => v, fun h => h 0 0 rfl⟩⟩
  intro x y
  by_cases h : v = some true
  · simp only [h]; decide
  · simp only [if_neg h]; exact fun heq => h heq.symm

/-- **Both verdicts are symmetric.** Relabelling the codomain by swapping the two present verdicts is an
involution fixing the absence: the framework's asymmetry is absence versus presence, `none` versus `some`, not
`true` versus `false`. Nothing distinguishes the two present verdicts. -/
theorem both_verdicts_are_symmetric :
    (swap (some true) = some false ∧ swap (some false) = some true ∧ swap none = none)
    ∧ (∀ o, swap (swap o) = o)
    ∧ (∀ o, swap o = none ↔ o = none) := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, by decide⟩

/-- **What the domain adds is the polarity.** The floor at `some true` and the floor at `some false` are one shape
under relabelling: a classification never firing `some true` is, relabelled, one never firing `some false`. So the
domain contributes only which verdict is success, a label carried by the relabelling, doing no structural work. -/
theorem what_the_domain_adds (c : Fin 2 → Fin 2 → Option Bool) :
    (∀ x y, c x y ≠ some true) ↔ (∀ x y, swap (c x y) ≠ some false) := by
  have key : ∀ o : Option Bool, (o ≠ some true) ↔ (swap o ≠ some false) := by decide
  exact ⟨fun h x y => (key (c x y)).mp (h x y), fun h x y => (key (c x y)).mpr (h x y)⟩

/-! ## Part 2: does the floor depend on the choice? -/

/-- **The floor survives relabelling.** The witness never firing `some true` becomes, under the swap, one never
firing `some false`: the same set of classifications moved by the relabelling, not attached to a particular
verdict. -/
theorem floor_under_relabelling :
    (∀ x y, wit2 x y ≠ some true)
    ∧ (∀ x y, swap (wit2 x y) ≠ some false) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **There is no privileged verdict.** Totalization fills an absence with `decide (s y ≤ s x)`, a scale-dependent
value; two scales give opposite fills, `some true` and `some false`, at the same absence. The fill is chosen by the
scale, so the move privileges neither verdict. -/
theorem is_there_a_privileged_verdict :
    ∃ (s s' : Fin 2 → Nat) (c : Fin 2 → Fin 2 → Option Bool) (x y : Fin 2),
      totalization s c x y = some true ∧ totalization s' c x y = some false :=
  ⟨fun _ => 0, fun i => (i : Nat), fun _ _ => none, 0, 1, by decide, by decide⟩

/-! ## Part 3: the verdict -/

/-- **The floor is generic with imported polarity.** The shape, a present verdict never firing, is stateable for
any verdict with no domain input and non-trivial; the two present verdicts are symmetric, exchanged by an
involution fixing the absence; and the floor at one verdict is the floor at the other under relabelling. The
framework supplies the floor-shape, the domain supplies only which verdict is success. -/
theorem floor_is_generic_with_imported_polarity :
    (∀ v : Option Bool, ∃ c : Fin 2 → Fin 2 → Option Bool, ∀ x y, c x y ≠ v)
    ∧ (swap (some true) = some false ∧ swap (some false) = some true ∧ swap none = none
        ∧ ∀ o, swap (swap o) = o)
    ∧ (∀ c : Fin 2 → Fin 2 → Option Bool,
        (∀ x y, c x y ≠ some true) ↔ (∀ x y, swap (c x y) ≠ some false)) :=
  ⟨fun v => (never_fires_is_generic v).1,
   ⟨by decide, by decide, by decide, by decide⟩,
   what_the_domain_adds⟩

/-! ## The verdicts

Part 1: the form is stateable without domain content, and the verdicts are symmetric. For any verdict, avoiding it
and firing it are both non-trivial on the bare codomain (`never_fires_is_generic`); the two present verdicts are
exchanged by an involution fixing the absence, the framework's asymmetry being `none` versus `some`
(`both_verdicts_are_symmetric`); and the domain adds only the polarity, the floor at one verdict being the floor at
the other relabelled (`what_the_domain_adds`).

Part 2: the floor survives relabelling and no verdict is privileged. The witness moves from the `some true` floor
to the `some false` floor under the swap (`floor_under_relabelling`); and totalization's fill is scale-dependent,
two scales giving opposite verdicts at one absence (`is_there_a_privileged_verdict`).

Part 3: the floor is generic with imported polarity (`floor_is_generic_with_imported_polarity`): the framework
supplies the shape, the domain names the verdict.

The verdict: the register floor is generic, and RegisterFloors's conclusion needs correcting. The form, a present
verdict never firing, is stateable for an arbitrary verdict with no domain content, and it is non-trivial, so it is
a property of the bare codomain, not of any domain. The two present verdicts are symmetric: swapping them is an
involution that fixes the absence, and nothing in the framework distinguishes them, the kernel's obstruction and
the protocol's non-degeneracy naming neither, and totalization filling an absence with a scale-dependent value that
is either verdict, so the move privileges none. The floor at `some true` and the floor at `some false` are one
shape under relabelling, the same set of classifications carried by the swap, so the choice of which verdict is
success is a label, doing no structural work. The framework's genuine asymmetry is `none` versus `some`, absence
versus presence, which is the hole; the polarity within the present verdicts is not the framework's. So the
framework supplies the floor-shape, generic on the codomain, and the domains supply only which verdict counts as
success. RegisterFloors was wrong to say registers supply floors: they name which of a generic pair of floors
applies, and the five different words, detecting, binding, accepting, predicting, trusting, are five names for one
generic condition, evidence of genericity rather than of domain contribution. Per the counter-bias, the five names
are read as genericity not contribution; no polarity was assumed, the framework checked and found none; and the
earlier conclusion is corrected rather than preferred: the floor-shape is the framework's, the polarity imported.
Reported per part. Nothing here is resolved. -/

end Chiralogy.FloorGeneric
