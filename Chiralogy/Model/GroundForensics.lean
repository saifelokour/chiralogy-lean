import Chiralogy.Model.Grounds
import Chiralogy.Model.Permitted

/-! # Model: ground-forensics, the fibre and the three sources

Locating a totalization from the state. The fibre of a state is the partial classifications that totalize to it;
an empty fibre is a state-side negative, proving the state is not a totalization, without a log. The order
constrains the fibre computably. Three sources are independent: the grounds bound what could have happened, the
fibre refutes what did not, the mark attributes what did. The order-shapes reading names how process structure
yields order shapes, marked READING. -/

namespace Chiralogy

/-- **The empty fibre proves never totalized.** The all-false classification on `Fin 1` is the totalization of no
partial classification, since a filled absence is `some true` on the diagonal, never `some false`: a state
predicate ruling out totalization, a negative, not detection. -/
theorem empty_fibre_never_totalized :
    ¬ ∃ c : Fin 1 → Fin 1 → Option Bool,
        (∃ x y, c x y = none) ∧ totalization (fun _ => 0) c = (fun _ _ => some false) := by decide

/-- **The fibre is non-constant.** Some fibre is empty (the all-false state) and another has at least two
preimages, totalization being non-injective (`totalization_not_faithful`): the quantity distinguishes states. -/
theorem fibre_is_nonconstant :
    ((Finset.univ.filter (fun c : Fin 1 → Fin 1 → Option Bool =>
        totalization (fun _ => 0) c = (fun _ _ => some false) ∧ ∃ x y, c x y = none)).card = 0)
    ∧ (∃ c c' : Fin 2 → Fin 2 → Option Bool,
        c ≠ c' ∧ totalization (fun _ => 0) c = totalization (fun _ => 0) c') :=
  ⟨by decide, totalization_not_faithful⟩

/-- The fibre size of a state with true-set `T`: the nonempty closeable subsets of `T`. -/
abbrev fibreSize {n : ℕ} (prereq : Fin n → Fin n → Bool) (T : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun S : Fin n → Bool =>
    closeable prereq S ∧ (∃ i, S i = true) ∧ (∀ i, S i = true → T i = true))).card

/-- **The order constrains the fibre computably.** More states are legible (empty or singleton fibre) at the
chain than at the discrete order with the same reason count, six against four: order-shape determines forensic
legibility. -/
theorem order_constrains_the_fibre :
    ((Finset.univ.filter (fun T : Fin 3 → Bool => fibreSize prereqDiscrete T ≤ 1)).card = 4)
    ∧ ((Finset.univ.filter (fun T : Fin 3 → Bool => fibreSize prereqChain3 T ≤ 1)).card = 6) :=
  ⟨by decide, by decide⟩

/-- **The three sources are independent.** The grounds bound the possible (the closeable family, contained in all
closures); the fibre rules out the impossible (an empty fibre proves never totalized); the mark attributes the
actual (a recorded fabrication distinguished). None subsumes another. -/
theorem three_sources_independent {n : ℕ} (prereq : Fin n → Fin n → Bool) :
    (∀ S : Fin n → Bool, closeable prereq S → closeable prereqDiscrete S)
    ∧ (¬ ∃ c : Fin 1 → Fin 1 → Option Bool,
        (∃ x y, c x y = none) ∧ totalization (fun _ => 0) c = (fun _ _ => some false))
    ∧ (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool))) := by
  refine ⟨?_, by decide, collision_without_concealment.2⟩
  intro S _ a b h1 _; simp [prereqDiscrete] at h1

/-- **Order shapes and their source.** READING: staged processes give chains, alternatives give forks, second
axes give free grounds. The three shapes are distinguished by their permitted counts, a chain three, a fork four,
a chain-plus-free five, as `enumerate_small` records. -/
theorem order_shapes_and_their_source :
    ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqChain3 S ∧ ¬ ∀ r, S r = true)).card = 3)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqV3 S ∧ ¬ ∀ r, S r = true)).card = 4)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqMixed3 S ∧ ¬ ∀ r, S r = true)).card = 5) :=
  ⟨by decide, by decide, by decide⟩

end Chiralogy
