import Autology.Kernel.Trichotomy
import Autology.Kernel.Hole

/-! # Partiality: the canonical extension `Kl(Maybe)`

The model adjoins a constitutive absence to the distinction space, passing to the Kleisli category of the
`Maybe` monad: `c : X → X → Option B`. The payload survives the extension, and the partial mode opens.

`Maybe` is the free way to adjoin one absence; it is the canonical codomain member, characterized by its
universal property (see `Closure`). Constitutive partiality is rare: a single canonical occupant. An
engineered absence (a filling value, a downstream layer, or a threshold) is not constitutive and does
not open the partial mode. -/

namespace Autology

/-- The extension is the Kleisli category of `Maybe` on the distinction space. -/
example : Monad Option := inferInstance

/-- **The payload survives the extension.** A partial classification is still not surjective. -/
theorem payload_survives {X : Type} (c : X → X → Option Bool) : ¬ Function.Surjective c :=
  hole_uniform c

/-- A constitutively partial object: incomparable options, ranked by their own incommensurable lights. -/
def imprecise : Fin 4 → Fin 4 → Option Bool := fun i j =>
  if i = 0 ∧ j = 1 then some true
  else if i = 1 ∧ j = 0 then some false
  else if i = 2 ∧ j = 3 then some true
  else if i = 3 ∧ j = 2 then some false
  else none

/-- The partial mode: a non-degenerate classification with a constitutive absence. -/
theorem imprecise_is_partial_mode :
    NonDegenerate imprecise ∧ ∃ x y, imprecise x y = none := by
  refine ⟨⟨0, 2, fun h => ?_⟩, 0, 2, by decide⟩
  exact absurd (congrFun h 1) (by decide)

/-- A total classification embeds via `some` and never abstains: the total instances sit at the
no-absence pole; a `some ∘ f` value is present, not an absence. -/
theorem total_never_abstains {X : Type} (f : X → X → Bool) (x y : X) :
    (fun a b => some (f a b)) x y ≠ none := by simp

/-- **Maybe is the free pointed object.** For a point `pt : C` and a map `f : B → C`, there is a unique
pointed extension `Option B → C` sending `none` to `pt` and `some b` to `f b`. This universal property
characterizes `B + 1` as the free object with a distinguished point, the canonical codomain extension. -/
theorem maybe_free_pointed {B C : Type} (pt : C) (f : B → C) :
    ∃! g : Option B → C, g none = pt ∧ ∀ b, g (some b) = f b := by
  refine ⟨fun o => o.elim pt f, ⟨rfl, fun _ => rfl⟩, ?_⟩
  rintro g ⟨hnone, hsome⟩
  funext o
  cases o with
  | none => exact hnone
  | some b => exact hsome b

end Autology
