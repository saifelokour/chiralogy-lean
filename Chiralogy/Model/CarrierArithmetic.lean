import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Prime.Basic

/-! # Carrier arithmetic

The size bound on splitting a carrier. A LEAF: it imports no other part of the framework, because it needs
none. The fact is about finite cardinalities and nothing else, and that independence is why it lives here
rather than beside the assemblage laws it bounds, which would have carried this file's imports into a module
much of the framework depends on.

What it bounds: any attempt to see a carrier as a product of strictly smaller ones. Where the carrier's size
is prime there is no such attempt to make, whatever the number of factors and whatever the classification
carried. So a descent through repeated splitting terminates on arithmetic grounds alone, before any question
about what a classification says. -/

set_option autoImplicit false

namespace Chiralogy

/-- **A CARRIER OF PRIME SIZE ADMITS NO SPLIT INTO STRICTLY SMALLER FACTORS.** No family of strictly smaller
fibres has the right size, whatever the number of fibres. Needs no lower bound on that number: even a single
strictly smaller fibre is refused. -/
theorem prime_carriers_admit_no_split {Z : Type} [Fintype Z]
    (hp : Nat.Prime (Fintype.card Z)) {m : ℕ} {W : Fin m → Type} [∀ i, Fintype (W i)]
    (e : Z ≃ (∀ i, W i)) (hsmall : ∀ i, Fintype.card (W i) < Fintype.card Z) : False := by
  have hcard : Fintype.card Z = ∏ i, Fintype.card (W i) := by
    rw [Fintype.card_congr e, Fintype.card_pi]
  have hone : ∀ i, Fintype.card (W i) = 1 := by
    intro i
    have hdvd : Fintype.card (W i) ∣ Fintype.card Z := by
      rw [hcard]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact h
    · exact absurd h (Nat.ne_of_lt (hsmall i))
  have hprod : (∏ i, Fintype.card (W i)) = 1 := Finset.prod_eq_one fun i _ => hone i
  rw [hcard, hprod] at hp
  exact Nat.not_prime_one hp

end Chiralogy
