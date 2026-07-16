import Autology.Kernel.TargetDynamics
import Autology.Model.Partiality

/-! # The moves

Totalization fills the absences; partialization withdraws verdicts. These are the flow structure of the
target dynamics. Totalization is not faithful and is irreversible; its cost is target-free (it falsifies
against every target), while partialization's cost is target-dependent. (Totalization is elsewhere called
the attempt.) -/

namespace Autology

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

/-- Totalization fabricates: it fills a constitutive absence with a scale-dependent verdict: two scales
give opposite verdicts. -/
theorem totalization_fabricates :
    ∃ s s' : Fin 4 → Nat, totalization s imprecise 0 2 ≠ totalization s' imprecise 0 2 :=
  ⟨(fun _ => 0), (fun i => if i = 2 then 1 else 0), by decide⟩

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

/-- A false assertion against a target: a present verdict that contradicts it. -/
def assertsFalse {X : Type} (c : X → X → Option Bool) (t : X → X → Bool) (x y : X) : Prop :=
  ∃ b, c x y = some b ∧ b ≠ t x y

/-- **Partialization asserts no falsehood, against any target.** It only removes verdicts; an absence
makes no claim. -/
theorem partialization_asserts_no_falsehood {X : Type} (w : X → X → Bool)
    (c : X → X → Option Bool) (t : X → X → Bool) (x y : X) :
    assertsFalse (partialization w c) t x y → assertsFalse c t x y := by
  rintro ⟨b, hb, hne⟩
  simp only [partialization] at hb
  by_cases hw : w x y
  · rw [if_pos hw] at hb; simp at hb
  · rw [if_neg hw] at hb; exact ⟨b, hb, hne⟩

/-- **Totalization falsifies against every target.** At the constitutive absence of `imprecise`, whatever
the target says, one of the two scale-verdicts contradicts it: a target-free cost. -/
theorem totalization_falsifies_against_every_target (t : Fin 4 → Fin 4 → Bool) :
    assertsFalse (totalization (fun _ => 0) imprecise) t 0 2 ∨
      assertsFalse (totalization (fun i => if i = 2 then 1 else 0) imprecise) t 0 2 := by
  cases h : t 0 2
  · exact Or.inl ⟨true, by decide, by rw [h]; decide⟩
  · exact Or.inr ⟨false, by decide, by rw [h]; decide⟩

end Autology
