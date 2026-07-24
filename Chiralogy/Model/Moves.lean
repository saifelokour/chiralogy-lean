import Chiralogy.Kernel.Apophatic

/-! # The two moves

The two operations on classifications `X → X → Option Bool`: `totalization` fills each absence with a scale
verdict (none to some), `partialization` withdraws marked verdicts (some to none). Extracted from `Model/Apophatic`
in the per-module-purity refactor: the moves cluster with the downstream dynamics community (the information order,
the n-ary assemblage, the assemblage dynamics and relations) that consumes them, a consumer base that did not exist
before those modules were graduated. This module holds the moves and the lemmas depending only on them; the
move-lemmas that also use the absence-carried shelf (`presentCarried`) or the model material (`imprecise`, `assertsFalse`)
stay in `Model/Apophatic`, which imports this module. -/

namespace Chiralogy

/-- Totalization: fill each absence with a scale verdict, keeping the present ones. -/
def totalization {X : Type} (s : X → Nat) (c : X → X → Option Bool) : X → X → Option Bool :=
  fun x y => some ((c x y).getD (decide (s y ≤ s x)))

theorem totalization_totalizes {X : Type} (s : X → Nat) (c : X → X → Option Bool) :
    ∀ x y, totalization s c x y ≠ none := by
  intro x y; simp [totalization]

/-- Totalization does not reach completeness: the totalized map still carries the hole. -/
theorem totalization_hole {X : Type} (s : X → Nat) (c : X → X → Option Bool) :
    ¬ Function.Surjective (totalization s c) :=
  hole_uniform (totalization s c)

/-- **Totalization is not faithful.** Two different partial maps totalize to the same map. -/
theorem totalization_not_faithful :
    ∃ c c' : Fin 2 → Fin 2 → Option Bool,
      c ≠ c' ∧ totalization (fun _ => 0) c = totalization (fun _ => 0) c' :=
  ⟨(fun _ _ => none), (fun x y => if x = 0 ∧ y = 1 then some true else none), by decide, by decide⟩

/-- **Totalization is irreversible.** No operation recovers the original from the totalized map. -/
theorem totalization_irreversible :
    ¬ ∃ recover : (Fin 2 → Fin 2 → Option Bool) → (Fin 2 → Fin 2 → Option Bool),
        ∀ c, recover (totalization (fun _ => 0) c) = c := by
  rintro ⟨recover, h⟩
  obtain ⟨c, c', hne, heq⟩ := totalization_not_faithful
  exact hne (by rw [← h c, heq, h c'])

/-- Partialization: withdraw the marked verdicts. -/
def partialization {X : Type} (w : X → X → Bool) (c : X → X → Option Bool) : X → X → Option Bool :=
  fun x y => if w x y then none else c x y

/-- **Totalization separates equal rows exactly through a split fill.** Two rows equal before totalization become
distinct after when they share an absence at a pair where the scale sends the fill different ways,
`decide (s y ≤ s x) ≠ decide (s y ≤ s x')`: at that pair the totalization gives different filled values. -/
theorem totalization_separates_equal_rows {X : Type} (c : X → X → Option Bool) (s : X → Nat) (x x' : X) :
    c x = c x' → (∃ y, c x y = none ∧ decide (s y ≤ s x) ≠ decide (s y ≤ s x')) →
    totalization s c x ≠ totalization s c x' := by
  intro heqc hy htot
  obtain ⟨y, hnone, hf⟩ := hy
  have hnone' : c x' y = none := (congrFun heqc y) ▸ hnone
  have he := congrFun htot y
  have e1 : totalization s c x y = some (decide (s y ≤ s x)) := by simp [totalization, hnone]
  have e2 : totalization s c x' y = some (decide (s y ≤ s x')) := by simp [totalization, hnone']
  rw [e1, e2] at he
  exact hf (Option.some_inj.mp he)

/-- **Opening is monotone on distinction.** Opening by a column-uniform mask never separates equal rows: the fill is
the parameterless absence, so on a column it maps both rows the same way. Partialization increases distinction only
through a row-discriminating mask, never through its fill. -/
theorem opening_is_monotone_on_distinction {X : Type} (wc : X → Bool)
    (c : X → X → Option Bool) (x x' : X) :
    c x = c x' → partialization (fun _ y => wc y) c x = partialization (fun _ y => wc y) c x' := by
  intro h; funext y; simp only [partialization, congrFun h y]

end Chiralogy
