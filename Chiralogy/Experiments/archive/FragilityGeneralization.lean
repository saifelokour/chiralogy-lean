import Chiralogy

/-! # Experiment (ARCHIVED, GRADUATED): the general fragility shelf

GRADUATED to canonical in `Model/Apophatic` (all hooking `presentCarried`, so the graph placed the whole shelf
there beside `survives_totalization`; no split). Mapping of this scratch record to canonical:
  presentCarriedG  -> presentCarried (already canonical)
  absCarried       -> absenceCarried
  fragG            -> fragility            ; distinctPairs -> distinctRows
  absCarried_symm / absCarried_offdiag     -> absenceCarried_symm / absenceCarried_offdiagonal (axiom-free)
  fragG_eq_two_mul / fragG_even            -> fragility_eq_two_mul / fragility_even
  robust_iff                               -> fragility_eq_zero_iff
  maximally_fragile_iff                    -> fragility_eq_distinctRows_iff
Held back (NOT graduated): the interior full-fill (every even value in [0, n^2 - n] achieved) stays a CONJECTURE
(enumerated n = 2, 3); the u/C(n,2) uniform grid is scoped to all-distinct-rows only. This record is namespaced
`Chiralogy.FragilityGeneralizationRecord` so its names do not collide with canonical; it typechecks standalone. -/

namespace Chiralogy.FragilityGeneralizationRecord
open Chiralogy Finset
open scoped Classical

variable {X : Type} [Fintype X] [DecidableEq X]

def presentCarriedG (c : X → X → Option Bool) (x x' : X) : Prop :=
  ∃ y b b', c x y = some b ∧ c x' y = some b' ∧ b ≠ b'
def absCarried (c : X → X → Option Bool) (p : X × X) : Prop :=
  c p.1 ≠ c p.2 ∧ ¬ presentCarriedG c p.1 p.2
noncomputable def fragG (c : X → X → Option Bool) : Nat :=
  (univ.filter (fun p : X × X => absCarried c p)).card
noncomputable def distinctPairs (c : X → X → Option Bool) : Nat :=
  (univ.filter (fun p : X × X => c p.1 ≠ c p.2)).card

theorem absCarried_symm (c : X → X → Option Bool) {a b : X} :
    absCarried c (a, b) → absCarried c (b, a) := by
  rintro ⟨hne, hnp⟩
  exact ⟨fun h => hne h.symm, fun ⟨y,b1,b2,h1,h2,hb⟩ => hnp ⟨y,b2,b1,h2,h1,fun h => hb h.symm⟩⟩
theorem absCarried_offdiag (c : X → X → Option Bool) (a : X) : ¬ absCarried c (a, a) := by
  rintro ⟨hne, _⟩; exact hne rfl

theorem fragG_eq_two_mul [LinearOrder X] (c : X → X → Option Bool) :
    fragG c = 2 * (univ.filter (fun p : X × X => p.1 < p.2 ∧ absCarried c p)).card := by
  rw [fragG]
  set S := univ.filter (fun p : X × X => absCarried c p) with hS
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := S) (p := fun p : X × X => p.1 < p.2)
  set A := S.filter (fun p : X × X => p.1 < p.2) with hA
  have hbij : (S.filter (fun p : X × X => ¬ p.1 < p.2)).card = A.card := by
    apply card_bij' (fun p _ => Prod.swap p) (fun p _ => Prod.swap p)
    · intro p hp
      simp only [hS, mem_filter, mem_univ, true_and] at hp
      obtain ⟨hac, hnlt⟩ := hp
      have hne : p.1 ≠ p.2 := fun h => hac.1 (congrArg c h)
      simp only [hA, hS, mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]
      exact ⟨absCarried_symm c hac, lt_of_le_of_ne (not_lt.mp hnlt) (fun h => hne h.symm)⟩
    · intro p hp
      simp only [hA, hS, mem_filter, mem_univ, true_and] at hp
      simp only [hS, mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]
      exact ⟨absCarried_symm c hp.1, not_lt.mpr (le_of_lt hp.2)⟩
    · intro p _; exact Prod.swap_swap p
    · intro p _; exact Prod.swap_swap p
  have hAu : A.card = (univ.filter (fun p : X × X => p.1 < p.2 ∧ absCarried c p)).card := by
    congr 1; ext p; simp only [hA, hS, mem_filter, mem_univ, true_and]; tauto
  omega

theorem fragG_even [LinearOrder X] (c : X → X → Option Bool) : 2 ∣ fragG c :=
  ⟨_, fragG_eq_two_mul c⟩

theorem robust_iff (c : X → X → Option Bool) :
    fragG c = 0 ↔ ∀ a b, c a ≠ c b → presentCarriedG c a b := by
  rw [fragG, card_eq_zero, filter_eq_empty_iff]
  constructor
  · intro h a b hab; by_contra hp; exact (h (mem_univ (a,b))) ⟨hab, hp⟩
  · intro h p _ ⟨hne, hnp⟩; exact hnp (h p.1 p.2 hne)

theorem maximally_fragile_iff (c : X → X → Option Bool) :
    fragG c = distinctPairs c ↔ ∀ a b, c a ≠ c b → ¬ presentCarriedG c a b := by
  rw [fragG, distinctPairs]
  have hsub : (univ.filter (fun p : X × X => absCarried c p)) ⊆
             (univ.filter (fun p : X × X => c p.1 ≠ c p.2)) := by
    intro p hp; simp only [mem_filter, mem_univ, true_and, absCarried] at *; exact hp.1
  constructor
  · intro h a b hab
    have heq := eq_of_subset_of_card_le hsub (le_of_eq h.symm)
    by_contra hp
    have hmem : (a,b) ∈ univ.filter (fun p : X × X => c p.1 ≠ c p.2) := by simp [hab]
    rw [← heq] at hmem
    simp only [mem_filter, mem_univ, true_and, absCarried] at hmem
    exact hmem.2 hp
  · intro h
    congr 1; apply filter_congr
    intro p _; simp only [absCarried]
    exact ⟨fun hp => hp.1, fun hne => ⟨hne, h p.1 p.2 hne⟩⟩

end Chiralogy.FragilityGeneralizationRecord
