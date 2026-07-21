import Chiralogy

/-! # Experiment: what does territorialization map to?

The free-part reading failed on physics. The proposed repositioning (mine, untested): territorialization is a
parameter on assemblage-shaped registers, and physics is stratum-shaped, out of range. Test what the parameter
maps to without assuming the repositioning. Imported (DeLanda): territorialization measures homogenization of
components and impermeability of boundaries together, distinct from coding (identity fixed by rules). Known:
coding identifies with order-density (closures ruled out); the free-part fails on physics, whose single isolated
ground reads as maximally permeable though the register is the sharpest. Candidates are computed across all six
before judging. Domain content IMPORTED, mappings READINGS. Stays in `Experiments/`; canonical untouched; nothing
resolved. -/

open Chiralogy

namespace Chiralogy.Territorialization

/-! ## Part 1: candidates, computed across all six

The six orders (canonical): physics `prereqDiscrete` on `Fin 1`; type and cognition `prereqChain3`; immunology
`prereqMixed3`; chemistry `prereqChemistry`; trust `prereqTrust`. -/

/-- **Free-part size, the failing candidate.** The isolated grounds: physics one, the chain none, immunology one,
chemistry one, trust one. Physics groups with the permeable registers, all at one, though it is the sharpest. -/
theorem free_part_size :
    ((Finset.univ.filter (fun i : Fin 1 => isFree prereqDiscrete i)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => isFree prereqChain3 i)).card = 0)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => isFree prereqMixed3 i)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 4 => isFree prereqChemistry i)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 4 => isFree prereqTrust i)).card = 1) :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **Homogeneity of the bound part, the maximal-count.** The number of maximal elements, the order's endpoints or
culminations: physics one, the chain one, immunology two, chemistry two, trust three. A chain has one endpoint
(homogeneous), a fork two (alternatives); physics groups with the chains. -/
theorem homogeneity_of_the_bound_part :
    ((Finset.univ.filter (fun i : Fin 1 => ∀ j, prereqDiscrete i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqChain3 i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqMixed3 i j = false)).card = 2)
    ∧ ((Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqChemistry i j = false)).card = 2)
    ∧ ((Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqTrust i j = false)).card = 3) :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **Boundary measure, the bound-part size.** The non-free grounds: physics zero, the chain three, trust three.
Physics reads as fully permeable (zero bound), the same failure as the free-part from the other side. -/
theorem boundary_measure :
    ((Finset.univ.filter (fun i : Fin 1 => ¬ isFree prereqDiscrete i)).card = 0)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => ¬ isFree prereqChain3 i)).card = 3)
    ∧ ((Finset.univ.filter (fun i : Fin 4 => ¬ isFree prereqTrust i)).card = 3) :=
  ⟨by decide, by decide, by decide⟩

/-- **Combined candidates.** Combining the free-based candidates does not fix physics: its single ground is free
(one) and unbound (zero), permeable by both; only the maximal-count places physics with the chains (one). No
combination of the free-based measures helps; the endpoint-count succeeds alone. -/
theorem combined_candidates :
    ((Finset.univ.filter (fun i : Fin 1 => isFree prereqDiscrete i)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 1 => ¬ isFree prereqDiscrete i)).card = 0)
    ∧ ((Finset.univ.filter (fun i : Fin 1 => ∀ j, prereqDiscrete i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqChain3 i j = false)).card = 1) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ## Part 2: does anything order the six sensibly? -/

/-- **Ordering check.** By the maximal-count: physics and the chains at one, immunology and chemistry at two,
trust at three. Inverse reading, most to least territorialized: chemistry more than trust, a chain-plus-free more
homogeneous than a fork-plus-free, one linear process and a limit against two alternatives and a limit; physics
with the chains at the territorialized end. -/
theorem ordering_check :
    ((Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqChemistry i j = false)).card <
     (Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqTrust i j = false)).card)
    ∧ ((Finset.univ.filter (fun i : Fin 1 => ∀ j, prereqDiscrete i j = false)).card =
       (Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqChain3 i j = false)).card) :=
  ⟨by decide, by decide⟩

/-- **Physics is in range.** The maximal-count places physics at one, the chains' also one, at the territorialized
end, defensibly, a single ground being one homogeneous culmination; so a candidate places physics sensibly and the
repositioning is unnecessary, dropped. The free-part misplaced it, physics reading as more permeable than a chain
(free one against zero); the maximal-count corrects it. -/
theorem is_physics_in_range :
    ((Finset.univ.filter (fun i : Fin 1 => ∀ j, prereqDiscrete i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqChain3 i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 1 => isFree prereqDiscrete i)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => isFree prereqChain3 i)).card = 0) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ## Part 3: the verdict -/

/-- **What territorialization maps to.** The maximal-count, the number of the order's endpoints, whose inverse is
the homogeneity: a chain has one (homogeneous, one culmination), a fork two (alternatives). A computed quantity,
not nothing and not a mere combination; the free-based candidates failed, the endpoint-count succeeds. -/
theorem what_territorialization_maps_to :
    ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqChain3 i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqV3 i j = false)).card = 2) :=
  ⟨by decide, by decide⟩

/-- **It is independent of coding.** The fork `V` and the join `Λ` code alike, five closeable sets each, coding
three; but they territorialize differently, maximal-count two against one, the fork's two endpoints against the
join's one. So territorialization varies at fixed coding: two independent knobs. And physics realizes the other
independence, territorialized (maximal-count one) yet uncoded (no closures ruled out), a bounded but rule-free
corner. -/
theorem is_it_independent_of_coding :
    ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqV3 S)).card =
     (Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqLambda3 S)).card)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqV3 i j = false)).card = 2)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqLambda3 i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun S : Fin 1 → Bool => ¬ closeable prereqDiscrete S)).card = 0) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ## The verdicts

Part 1: the candidates split on physics. The free-part size groups physics with the permeable registers, all at
one (`free_part_size`), and the boundary measure at zero bound reads it fully permeable (`boundary_measure`); the
maximal-count places physics with the chains at one (`homogeneity_of_the_bound_part`). Combining the free-based
candidates does not fix physics (`combined_candidates`); only the endpoint-count does.

Part 2: the maximal-count orders the six sensibly, physics included. Chemistry is more territorialized than trust,
a chain-plus-free more homogeneous than a fork-plus-free, and physics sits with the chains at the territorialized
end (`ordering_check`); so physics is in range and the repositioning is unnecessary (`is_physics_in_range`). The
free-based candidates alone misplaced it.

Part 3: territorialization maps to the maximal-count, a computed quantity (`what_territorialization_maps_to`), and
it is independent of coding: the fork and the join code alike but territorialize differently, and physics is
territorialized yet uncoded (`is_it_independent_of_coding`). Two knobs, not one.

The verdict: territorialization maps to the maximal-count of the ground-order, the number of its endpoints, whose
inverse is the homogeneity a chain has and a fork lacks. This is a computed quantity in the ground-structure, not
nothing and not a combination, and it places all six sensibly, physics with the chains at the territorialized end,
a single ground being one homogeneous culmination. So the repositioning is unnecessary and is dropped: a candidate
places physics correctly, physics is in range, and the earlier failure was the free-part's, not the parameter's.
And the two knobs are independent: the fork and the join code alike yet territorialize differently, and physics is
territorialized yet uncoded, the bounded but rule-free corner, so coding and territorialization are genuinely two,
not one. The reading is imported and the mapping a reading; that chemistry is more territorialized than trust is
defensible, a linear process being more homogeneous than a branching one. Reported per part. Nothing here is
resolved. -/

end Chiralogy.Territorialization
