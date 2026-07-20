import Chiralogy

/-! # Experiment: does ground-structure transport across level morphisms?

A `LevelHom` carries declared grounds to grounds. Whether the reason count, the closeable family, the permitted
lattice, and the prohibition survive it was unaskable before, because `Hom` need not respect declarations. Test
it with morphisms that merely satisfy `LevelHom`, not ones built to preserve the structure. Stays in
`Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.LevelTransport

/-- An object carrying a classification and its declared grounds. -/
structure LevelObj where
  X : Type
  B : Type
  classify : X → X → B
  absent : B → Prop

/-- A morphism carrying declared grounds to grounds, with `preserves` holding. -/
structure LevelHom (S T : LevelObj) where
  onCarrier : S.X → T.X
  onValues : S.B → T.B
  preserves : ∀ x y, onValues (S.classify x y) = T.classify (onCarrier x) (onCarrier y)
  respects : ∀ v, S.absent v → T.absent (onValues v)

/-- A collapse of two grounds to one, verdict fixed. -/
def collapse : Fin 3 → Fin 3 := fun v => if v = 2 then 2 else 0

/-- A swap of two grounds, verdict fixed. -/
def swap01 : Fin 3 → Fin 3 := fun v => if v = 0 then 1 else if v = 1 then 0 else 2

/-- A carrier classification (its content is irrelevant to ground-transport). -/
def dummyClass : Fin 2 → Fin 2 → Fin 3 := fun x y => if x = y then 2 else 0

/-- Source: two grounds `{0, 1}`. Collapse target: one ground `{0}`. -/
def srcObj : LevelObj := ⟨Fin 2, Fin 3, dummyClass, fun v => v = 0 ∨ v = 1⟩
def tgtObj : LevelObj := ⟨Fin 2, Fin 3, fun x y => collapse (dummyClass x y), fun v => v = 0⟩

/-- The collapsing morphism, a valid `LevelHom`. -/
def collapseHom : LevelHom srcObj tgtObj :=
  ⟨id, collapse, fun _ _ => rfl, fun v h => by rcases h with rfl | rfl <;> rfl⟩

/-- Swap source and target: two grounds each. -/
def swapSrc : LevelObj := ⟨Fin 2, Fin 3, dummyClass, fun v => v = 0 ∨ v = 1⟩
def swapTgt : LevelObj := ⟨Fin 2, Fin 3, fun x y => swap01 (dummyClass x y), fun v => v = 0 ∨ v = 1⟩

/-- The swapping morphism, a valid `LevelHom`. -/
def swapHom : LevelHom swapSrc swapTgt :=
  ⟨id, swap01, fun _ _ => rfl, fun v h => by rcases h with rfl | rfl; exacts [Or.inr rfl, Or.inl rfl]⟩

/-! ## Part 1: the reason count -/

/-- **The reason count can shrink.** A `LevelHom` carries grounds to grounds but need not do so injectively:
`collapseHom` sends the two source grounds to one, so the image ground count is one where the source has two. It
never grows, the image being a subset of the target's grounds; a `LevelHom` permits shrinking. -/
theorem reason_count_under_levelhom :
    (Finset.univ.filter (fun v : Fin 3 => v = 0 ∨ v = 1)).card = 2
    ∧ (Finset.image collapse (Finset.univ.filter (fun v : Fin 3 => v = 0 ∨ v = 1))).card = 1
    ∧ (∀ v, srcObj.absent v → tgtObj.absent (collapseHom.onValues v)) :=
  ⟨by decide, by decide, collapseHom.respects⟩

/-- **When the count is preserved.** Exactly when `onValues` is injective on the grounds: injectivity restricted
to the ground set, weaker than global injectivity, preserves the count. `collapse` fails it and shrinks. -/
theorem when_is_the_count_preserved (f : Fin 3 → Fin 3) (G : Finset (Fin 3)) (h : Set.InjOn f ↑G) :
    (Finset.image f G).card = G.card :=
  Finset.card_image_of_injOn h

/-! ## Part 2: the closeable family and the lattice -/

/-- The prerequisite order `0 ≺ 1` on grounds. -/
def prereq : Fin 3 → Fin 3 → Bool := fun a b => decide (a = 0 ∧ b = 1)

/-- **Prerequisites need not transport.** `swapHom` respects grounds, yet it sends the ordered pair `(0, 1)` to
`(1, 0)`, which is not ordered in the target: ground-respecting does not imply order-respecting. The order would
transport only under a monotone `onValues`, which `LevelHom` does not require. -/
theorem prerequisites_under_levelhom :
    (∀ v, swapSrc.absent v → swapTgt.absent (swapHom.onValues v))
    ∧ prereq 0 1 = true
    ∧ prereq (swap01 0) (swap01 1) = false :=
  ⟨swapHom.respects, by decide, by decide⟩

/-- A set is closeable when up-closed under `0 ≺ 1`: closing `1` closes its prerequisite `0`. -/
abbrev coh (S : Finset (Fin 3)) : Prop := (1 : Fin 3) ∈ S → (0 : Fin 3) ∈ S

/-- **The closeable family need not transport.** The source closeable set `{0}` maps under `swap01` to `{1}`,
which is not closeable (up-closed) in the target order. So the closeable family, and with it the permitted
lattice, does not transport under a merely ground-respecting morphism. Checked, not assumed either way. -/
theorem closeable_family_transports_or_not :
    coh {(0 : Fin 3)} ∧ ¬ coh (Finset.image swap01 {(0 : Fin 3)}) :=
  ⟨by decide, by decide⟩

/-! ## Part 3: the prohibition -/

/-- **A permitted move can become the prohibition.** Under `collapse` the permitted source move `{0}` and the
source full closure `{0, 1}` both map to `{0}`, the target's full closure (its single ground). So a permitted
move becomes the target prohibition: the ethics does not transport under a ground-respecting morphism, a finding
of the laundering kind, now in the level category. -/
theorem prohibition_under_levelhom :
    (Finset.image collapse {(0 : Fin 3)} = Finset.image collapse ({0, 1} : Finset (Fin 3)))
    ∧ (Finset.image collapse {(0 : Fin 3)} = {(0 : Fin 3)})
    ∧ (({0} : Finset (Fin 3)) ≠ ({0, 1} : Finset (Fin 3))) :=
  ⟨by decide, by decide, by decide⟩

/-! ## Part 4: what wants stating over LevelHom -/

/-- **Results wanting the level category.** A kernel fact quantifies a classification and needs no declaration
(the payload, here); a ground fact requires the declared grounds (the closeable count, here). The full sort is
in the verdict: what never mentions declarations belongs with `Obj`, what cannot be stated without them belongs
with the level category. -/
theorem results_wanting_the_level_category :
    (∀ {X : Type} (c : X → X → Option Bool), ¬ Function.Surjective c)
    ∧ ((Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3) :=
  ⟨fun c => hole_uniform c, by decide⟩

/-! ## The verdicts

Part 1: the reason count can shrink. A `LevelHom` carries grounds to grounds but need not be injective on them,
so `collapseHom` sends two grounds to one (`reason_count_under_levelhom`); it never grows. The count is preserved
exactly when `onValues` is injective on the grounds (`when_is_the_count_preserved`), weaker than global
injectivity.

Part 2: prerequisites and the closeable family need not transport. Ground-respecting is not order-respecting:
`swapHom` reverses `0 ≺ 1` (`prerequisites_under_levelhom`), and the closeable set `{0}` maps to `{1}`, not
closeable (`closeable_family_transports_or_not`). The order and lattice would transport only under a monotone
`onValues`, which `LevelHom` does not require.

Part 3: the prohibition does not survive. Under `collapse` a permitted move maps onto the target's full closure
(`prohibition_under_levelhom`): a permitted source move becomes the prohibition. The ethics does not transport
across a ground-respecting morphism, the laundering finding recast in the level category.

Part 4: the sort (`results_wanting_the_level_category` exhibits one of each side). Obj side, statable without
declarations: the collision (`complete_and_faithful_is_impossible`), the payload, the hole, the center, the
channel (proposer and guard, maps of value types), and the arms as one map's two ends. Level side, needing the
declared grounds: the reason count, the closeable family, the permitted lattice, the departure space, and the
enumeration. The moves (totalization, partialization) act on a classification, so they are Obj-expressible, but
which moves are permitted needs declarations, so their ethics is level side; likewise the arms cohabit at Obj,
but the absorbing law that blocks a closure is level side. A result that cannot be stated without declarations
belongs with the level category, one that never mentions them with `Obj`. This records the sort; it moves
nothing. Nothing here is resolved. -/

end Chiralogy.LevelTransport
