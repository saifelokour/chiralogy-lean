import Autology.Model.Chiasm

/-! # The open seam

The last word of the Boundary. The two layer-chiasms (kernel, around the hole; model, around the none) are
brought into contact by a single utterance, the one prohibition. This module names that braid-point as the
seam and bounds it: it is a crossing that does not close, because its far side is ○.

`the_open_seam` re-presents `boundary_braids_both_absences` structurally: B1 pivots on the kernel hole
(`no_reflexive_object`, K1), B2 on the model none (M1's constitutive absence). The seam is where the two
centers meet.

● seam_is_the_pivot: the kernel chiasm (center: hole) and the model chiasm (center: none) cross at this
seam. It is the pivot of the doubly-chiastic figure, the χ of the two χ's.

○ open_seam_does_not_close: the seam is open. The far side of the Boundary is ○: the handed-back target,
silence. The figure crosses here but does not close, because the two layer-chiasms do not compose into one
object: their centers, the hole and the none, are different kinds of absence (`Boundary/DoubleChiasm`). A
crossing of two centers that share no generator cannot close into one. This is the framework's last word
before the empty registers: the name of the place it stops speaking. -/

namespace Autology

/-- **The open seam.** The one prohibition braids the two layer-centers: B1 (no complete self-account)
pivots on the kernel hole `no_reflexive_object` (K1), B2 (no complete-and-faithful map) on the model none.
The Boundary is the seam where the kernel chiasm's center and the model chiasm's center are brought into
contact by a single utterance. Re-presented, not reproven. -/
theorem the_open_seam :
    (∀ (X : Type) (c : X → X → Option Bool), ¬ Function.Surjective c) ∧
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2) :=
  boundary_braids_both_absences

end Autology
