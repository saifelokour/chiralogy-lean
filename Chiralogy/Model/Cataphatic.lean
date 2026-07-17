import Mathlib.Logic.Function.Basic

/-! # Model: the cataphatic model, the free skeleton

`CataphaticConformant` is the cataphatic submission form (carrier, ambient, build); it is loose (everything
conforms), so it is a model-construction shape, not a discriminating protocol like `Member`.

The free move is parameterized: `embed` sends a bit into any pointed ambient `F`, and the free/forget moves
and the surplus-chiasm are theorems about *any* ambient with a surplus (a point outside the image of `embed`,
`a ≠ 0 ∧ a ≠ 1`) and `0 ≠ 1`. `ZMod 3` does not appear here: the move is free, the ambient is a parameter.
The borrowed fillings (the four registers, the target-dependence demonstrations that show the specific
ambient matters, the tower and telescoping) are in `Model/Cataphatic/Instances.lean`. -/

namespace Chiralogy

/-- **The cataphatic submission form.** Carrier, ambient, and a build-outward map. There is no owned
discriminating field (no can-differ analogue): building-outward is free, so the form is loose by design. -/
structure CataphaticConformant where
  X : Type
  T : Type
  build : X → T

/-- **The cataphatic form is loose.** Every carrier passes: it builds into itself. -/
theorem cataphatic_is_loose (X : Type) : ∃ cc : CataphaticConformant, cc.X = X :=
  ⟨⟨X, X, id⟩, rfl⟩

/-- The free move: a bit into any pointed ambient (`false` to 0, `true` to 1). -/
def embed (F : Type) [Zero F] [One F] : Bool → F := fun b => if b then 1 else 0

/-- The forget move: pull an ambient element back to a bit (test whether it is 1). -/
def restrict {F : Type} [One F] [DecidableEq F] (a : F) : Bool := decide (a = 1)

/-- **Forget after free is the identity**, given the two build points are distinct (`0 ≠ 1`). -/
theorem restrict_embed_id {F : Type} [Zero F] [One F] [DecidableEq F] (h01 : (0 : F) ≠ 1) :
    ∀ b : Bool, restrict (embed F b) = b := by
  intro b
  cases b with
  | false => show restrict (0 : F) = false; simp only [restrict, decide_eq_false_iff_not]; exact h01
  | true  => show restrict (1 : F) = true; simp only [restrict, decide_eq_true_eq]

/-- **Free after forget is not the identity**, given a surplus point (one outside the image `{0, 1}`): the
build gains that point, the forget drops it. -/
theorem embed_restrict_not_id {F : Type} [Zero F] [One F] [DecidableEq F]
    (surplus : ∃ a : F, a ≠ 0 ∧ a ≠ 1) : ∃ a : F, embed F (restrict a) ≠ a := by
  obtain ⟨a, ha0, ha1⟩ := surplus
  refine ⟨a, ?_⟩
  have hr : restrict a = false := by simp only [restrict, decide_eq_false_iff_not]; exact ha1
  rw [hr]
  exact fun h => ha0 h.symm

/-- **Not iso**, given a surplus point: the embedding misses it, so it is not surjective. -/
theorem embedding_not_iso {F : Type} [Zero F] [One F] (surplus : ∃ a : F, a ≠ 0 ∧ a ≠ 1) :
    ¬ Function.Surjective (embed F) := by
  obtain ⟨a, ha0, ha1⟩ := surplus
  intro hsurj
  obtain ⟨b, hb⟩ := hsurj a
  cases b with
  | false => exact ha0 hb.symm
  | true  => exact ha1 hb.symm

/-- **The free/forget moves, not inverse**, over any ambient with distinct build points and a surplus:
forget-after-free is the identity, free-after-forget is not (a section with retraction, the cataphatic dual
of the apophatic non-invertible move-pair). -/
theorem free_forget_moves {F : Type} [Zero F] [One F] [DecidableEq F] (h01 : (0 : F) ≠ 1)
    (surplus : ∃ a : F, a ≠ 0 ∧ a ≠ 1) :
    (∀ b : Bool, restrict (embed F b) = b) ∧ (∃ a : F, embed F (restrict a) ≠ a) :=
  ⟨restrict_embed_id h01, embed_restrict_not_id surplus⟩

/-- **The cataphatic model chiasm, at the surplus**, over any ambient with distinct build points and a
surplus. The free (`embed`) and forget (`restrict`) moves cross, the crossing a genuine inversion
(`embed_restrict_not_id`), the center the surplus: the point `embed` never reaches. Dual to the apophatic
none: excess where the model has absence. -/
theorem cataphatic_model_chiasm {F : Type} [Zero F] [One F] [DecidableEq F] (h01 : (0 : F) ≠ 1)
    (surplus : ∃ a : F, a ≠ 0 ∧ a ≠ 1) :
    (∀ b : Bool, restrict (embed F b) = b) ∧ (∃ a : F, embed F (restrict a) ≠ a) ∧
      ¬ Function.Surjective (embed F) :=
  ⟨restrict_embed_id h01, embed_restrict_not_id surplus, embedding_not_iso surplus⟩

end Chiralogy
