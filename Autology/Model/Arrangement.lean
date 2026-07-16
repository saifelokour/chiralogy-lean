import Autology.Model.Partiality

/-! # Arrangement

The comparability graph of a partial object carries free structure: it can federate into components, or
have a cut-vertex. On a total object it is complete: the terminal product, no free structure. Degree
concentration (cored versus diffuse) is not free: it is a measure, and stays imported (○). -/

namespace Autology

/-- Comparability: an edge iff the pair is classified (not absent). The free arrangement lives here. -/
def Comparable {X : Type} (c : X → X → Option Bool) (x y : X) : Prop := c x y ≠ none

/-- **Federation.** The comparability graph of `imprecise` splits into two components: blocks `{0,1}` and
`{2,3}` are internally comparable, with no comparability between them. -/
theorem comparability_federates :
    Comparable imprecise 0 1 ∧ Comparable imprecise 2 3 ∧
      (∀ i j : Fin 4, (i = 0 ∨ i = 1) → (j = 2 ∨ j = 3) →
        imprecise i j = none ∧ imprecise j i = none) := by
  refine ⟨?_, ?_, ?_⟩
  · show imprecise 0 1 ≠ none; decide
  · show imprecise 2 3 ≠ none; decide
  · decide

/-- A partial object whose comparability graph has a cut-vertex. -/
def vshape : Fin 3 → Fin 3 → Option Bool := fun i j =>
  if i = 0 ∧ j = 1 then some true
  else if i = 1 ∧ j = 0 then some false
  else if i = 0 ∧ j = 2 then some true
  else if i = 2 ∧ j = 0 then some false
  else none

/-- **Cut-vertex.** In `vshape`, `1` and `2` are each comparable to `0` but incomparable to each other:
removing `0` disconnects them. A free structural hub. -/
theorem comparability_has_cut_vertex :
    vshape 0 1 ≠ none ∧ vshape 0 2 ≠ none ∧ vshape 1 2 = none ∧ vshape 2 1 = none :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **Trivial on total objects.** A total classification is comparable everywhere: the comparability graph
is complete (the terminal product), carrying no free arrangement. -/
theorem total_comparability_complete {X : Type} (f : X → X → Bool) (x y : X) :
    Comparable (fun a b => some (f a b)) x y := by
  simp [Comparable]

end Autology
