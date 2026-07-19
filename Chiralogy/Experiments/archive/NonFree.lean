import Chiralogy

/-! # Experiment: are the non-free phenomena one?

Two departures from freeness: forcing among constants (closeable sets become the up-sets of an order, the
lattice Heyting) and absorbing between a constant and an operation (a closure is blocked, an element removed).
Both need axioms beyond the free ones, but that is a shared precondition, not a shared mechanism. The sharp
test: does absorbing induce forcing, or forcing induce blocking?

Reasons are `Bool`; closures are `Bool → Bool`. Stays in `Experiments/`; canonical untouched; nothing
resolved. -/

open Chiralogy

namespace Chiralogy.NonFree

/-- Forcing `lo` (false) below `hi` (true): a closure is an up-set of this order. -/
abbrev IsUpSet (close : Bool → Bool) : Prop := close false = true → close true = true

/-- Blocking: the absorbing reason `false` is unclosable, so a closure must leave it open. -/
abbrev IsBlockable (close : Bool → Bool) : Prop := close false = false

/-- An up-set for an arbitrary forcing relation. -/
def UpSetFor (forces : Bool → Bool → Prop) (close : Bool → Bool) : Prop :=
  ∀ r r', close r = true → forces r r' → close r' = true

/-! ## Part 1: does absorbing induce forcing? -/

/-- **Absorbing blocks one closure.** No verdict absorbs under `mzAppend`, so the absorbing reason cannot be
closed to a verdict. -/
theorem absorbing_blocks_one_closure :
    ∀ a : List Bool, mzAppend (some a) none ≠ some a := by
  intro a; simp [mzAppend]

/-- The full closure is an up-set for any order: it is up-closed trivially, so every up-set family contains
it. -/
theorem full_closure_is_up_set_for_any_order (forces : Bool → Bool → Prop) :
    UpSetFor forces (fun _ => true) :=
  fun _ _ _ _ => rfl

/-- **Blocking is not forcing.** The blocked family is not the up-sets of any order: every up-set family
contains the full closure, but the blocked family excludes it (the absorbing reason cannot be closed, so no
closeable set contains it, including the top). The blocked family is a different restriction of the powerset,
not up-closed for any order. -/
theorem blocking_is_not_forcing :
    ¬ ∃ forces : Bool → Bool → Prop, ∀ close : Bool → Bool, IsBlockable close ↔ UpSetFor forces close := by
  rintro ⟨forces, h⟩
  have := (h (fun _ => true)).2 (full_closure_is_up_set_for_any_order forces)
  simp [IsBlockable] at this

/-- **The closeable families differ.** Free (all four subsets), forcing (three up-sets, excluding `{lo}`), and
blocking (two, excluding every set with the blocked reason) are three different families over two reasons. -/
theorem closeable_families_differ :
    (Finset.univ.filter (fun _ : Bool → Bool => True)).card = 4
    ∧ (Finset.univ.filter (fun c : Bool → Bool => IsUpSet c)).card = 3
    ∧ (Finset.univ.filter (fun c : Bool → Bool => IsBlockable c)).card = 2 := by decide

/-! ## Part 2: does forcing induce blocking? -/

/-- **Under forcing, `lo` is closeable, but only at the top.** `{lo, hi}` is an up-set (so `lo` is closed
there), while `{lo}` alone is not: `lo` appears in a closeable set, unlike the blocked reason, which appears
in none. -/
theorem forcing_closes_lo_only_at_top :
    IsUpSet (fun _ => true)
    ∧ ((fun _ => true) false = true)
    ∧ ¬ IsUpSet (fun r => decide (r = false)) := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Forcing blocks `lo` only among the permitted moves.** In every permitted up-set (non-full), `lo` is
left open: its only closure is the full one, which is prohibited. So forcing makes `lo` unclosable among
permitted moves, the shared symptom, yet `lo` remains closeable at the prohibited top, unlike blocking. -/
theorem forcing_blocks_lo_only_among_permitted :
    ∀ close : Bool → Bool, IsUpSet close → ¬ (∀ r, close r = true) → close false = false := by
  decide

/-! ## Part 3: the verdict on non-freeness -/

/-- **Non-freeness has two distinct effects.** Forcing reshapes the closeable family to up-sets, keeping the
top (`full_closure_is_up_set_for_any_order`) and making the order Heyting; blocking removes a closure, the
blocked family excluding the top (`blocking_is_not_forcing`). The families are different
(`closeable_families_differ`). The shared symptom, a reason unclosable among permitted moves, is superficial:
under forcing the reason is closeable at the prohibited top, under blocking it is not closeable at all. Two
mechanisms, not one. -/
theorem nonfree_effects :
    (¬ ∃ forces : Bool → Bool → Prop, ∀ close : Bool → Bool, IsBlockable close ↔ UpSetFor forces close)
    ∧ ((Finset.univ.filter (fun c : Bool → Bool => IsUpSet c)).card = 3
        ∧ (Finset.univ.filter (fun c : Bool → Bool => IsBlockable c)).card = 2) :=
  ⟨blocking_is_not_forcing, ⟨by decide, by decide⟩⟩

/-! ## The verdict

Part 1: absorbing does not induce forcing. The blocked family is not the up-sets of any order
(`blocking_is_not_forcing`): every up-set family contains the full closure, but blocking excludes it, since
the absorbing reason is in no closeable set. The families are distinct at a small instance
(`closeable_families_differ`, sizes four, three, two).

Part 2: forcing does not induce blocking at the level of the closeable family. Under forcing `lo` is closeable,
in the full up-set (`forcing_closes_lo_only_at_top`), and only there; among the permitted moves `lo` is always
left open (`forcing_blocks_lo_only_among_permitted`). So forcing makes `lo` unclosable among permitted moves,
which looks like blocking, but `lo` is still closeable at the prohibited top, where the blocked reason is not
closeable at all. The coincidence is only in the symptom.

Part 3: two mechanisms. Departing from freeness produces distinct effects, forcing reshaping the closeable
family into up-sets (Heyting) and blocking removing a closure (the top absent). They coincide only in the
degenerate symptom at the top, not in the closeable family. So the tower's position depends on which axioms a
level carries, forcing or absorbing, not merely on whether it has any. Non-freeness acts several ways, not
one. Nothing here is resolved. -/

end Chiralogy.NonFree
