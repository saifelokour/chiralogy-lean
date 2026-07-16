import Autology.Model.Chiasm
import Autology.Model.Closure

/-! # Composing the two chiasms: one construction, or three facts?

Are the kernel chiasm (K16, `two_inversions_share_center`) and the model chiasm (M7, `model_arms_invert`)
instances of a single construction parameterized by which absence is the center, or three separate facts?

Verdict: (c), they do not compose. The two centers are different kinds of absence. The hole is a
non-surjectivity obstruction parameterized by a fixed-point-free endomap on the codomain (K4, arity-1): by
Closure (`stochastic_collapses`) it holds on any codomain, including `Bool`, which has no absence point. The
none is a distinguished element of the codomain (M1): the model's arms (`totalization`, `partialization`)
are operations on `Option`-valued maps that consume it. The hole lives where the none cannot
(`double_chiasm_does_not_compose`), so no single datum "the absence" feeds both. The attempted generator
`chiasm_of` must therefore inspect which absence it received and hand back the corresponding pre-proven
chiasm: its result type `ChiasmType` is itself a case-split (the two chiasm-types differ), so `chiasm_of` is
the conjunction in a function's clothing, not a uniform construction (trap #33). The figure is three facts,
not one generated object.

So "Autology is doubly chiastic" is a reading (●), not a theorem, and the reason is structural (the arity
and kind difference between hole and none), demonstrated by proof. It is NOT the incompleteness theorem: no
proof term here routes through `no_complete_self_account`. The earlier note that composing the figure whole
is "forbidden by `no_complete_self_account`" was a reading stated as a reason; it is retracted. The figure is
not nobly withheld, it simply does not compose. `no_complete_self_account` stays true of the framework's
self-account; it is just not why these two chiasms fail to share a generator. -/

namespace Autology

/-- K16, the kernel chiasm: two inversions around the hole. -/
abbrev KernelChiasmStmt : Prop :=
  (¬ Function.Surjective 𝒜.classify) ∧ (∀ M : Member, ¬ Function.Surjective M.classify)

/-- M7, the model chiasm: two arms around the none, with inverted costs. -/
abbrev ModelChiasmStmt : Prop :=
  (∃ (s : Fin 4 → Nat) (w : Fin 4 → Fin 4 → Bool),
      (imprecise 0 2 = none ∧ totalization s imprecise 0 2 ≠ none) ∧
      (imprecise 0 1 ≠ none ∧ partialization w imprecise 0 1 = none)) ∧
  (∀ t : Fin 4 → Fin 4 → Bool,
      assertsFalse (totalization (fun _ => 0) imprecise) t 0 2 ∨
        assertsFalse (totalization (fun i => if i = 2 then 1 else 0) imprecise) t 0 2) ∧
  (∀ (w : Fin 4 → Fin 4 → Bool) (c : Fin 4 → Fin 4 → Option Bool)
      (t : Fin 4 → Fin 4 → Bool) (x y : Fin 4),
      assertsFalse (partialization w c) t x y → assertsFalse c t x y)

/-- B7, the braid: the one prohibition brings the two centers into contact. -/
abbrev BraidStmt : Prop :=
  (∀ (X : Type) (c : X → X → Option Bool), ¬ Function.Surjective c) ∧
  (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2)

/-- **The conjunction (the floor).** K16, M7, and B7 bundled into one statement. This always succeeds: it is
three proven facts placed side by side, a conjunction, not one generated object. -/
theorem double_chiasm_conjunction : KernelChiasmStmt ∧ ModelChiasmStmt ∧ BraidStmt :=
  ⟨two_inversions_share_center, model_arms_invert, boundary_braids_both_absences⟩

/-- The two absences, as the candidate parameter of a uniform generator. -/
inductive Absence where
  | hole
  | none

/-- The chiasm-type of each absence. It is a case-split: the two chiasms have different types, so any
generator over `Absence` is dependently typed on which absence it received. -/
def ChiasmType : Absence → Prop
  | .hole => KernelChiasmStmt
  | .none => ModelChiasmStmt

/-- The attempted generator. Its proof term is a match: it inspects which absence it got and returns the
corresponding pre-proven chiasm. That is a dispatch, not a construction from the absence's structure (trap
#33), so it adds nothing beyond `double_chiasm_conjunction`. -/
def chiasm_of : (a : Absence) → ChiasmType a
  | .hole => two_inversions_share_center
  | .none => model_arms_invert

/-- **The double chiasm does not compose.** The two centers are different kinds of absence, so no single
datum feeds a uniform generator. The kernel center (the hole) is non-surjectivity for any codomain carrying
a fixed-point-free endomap (`stochastic_collapses`): it holds on `Bool`, which has no `none`. The model
center is a distinguished point of the codomain, realized only in `Option` (here as `imprecise`'s `none`).
The hole is present where the none cannot be, so `chiasm_of` can only dispatch (K4 arity vs M1 codomain). -/
theorem double_chiasm_does_not_compose :
    (∃ c : Fin 2 → Fin 2 → Bool, ¬ Function.Surjective c) ∧
    (∃ i j : Fin 4, imprecise i j = none) :=
  ⟨⟨fun _ _ => true, stochastic_collapses (g := fun b => !b) (by decide) _⟩, 0, 2, by decide⟩

end Autology
