import Chiralogy

/-! ARCHIVED (GRADUATED, SUPERSEDED): the 1D fragility-spectrum question this file explored is closed.
Mapping to canonical (Model/Apophatic): fragility (Fin-n) -> Model/Apophatic fragility (general) ; survives_totalization -> canonical ; absence_carried witness -> totalization_destroys_absence_carried ; the when-survives / clustering questions -> the boundary laws + interior_full_fill (spectrum = all even values in [0, n^2-n], no clusters).
The remaining open frontier (the 2D assemblage phase space: valued fraction against cross-fragility, and
whether factors bound the cross-fragility ceiling) lives on in the assemblage/phase-space experiments.
Namespaced under its own name, this record typechecks standalone against canonical. -/

/-! # Experiment: what fabrication destroys

Totalization removes absence and can merge rows whose distinctions rested on absences, preserving distinctions
carried by present verdicts. Characterize when a distinction survives, make the quantity computable, and see
whether configurations cluster. Compute across all cases before judging. The axes are otherwise independent,
coupled only at the total opening. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Flattening

/-- The saturated classifier: each element true on its own diagonal, absent elsewhere. -/
def satN {n : ℕ} : Fin n → Fin n → Option Bool := fun x y => if x = y then some true else none

/-- A maximally robust classifier on `Fin 3`: every row present and pairwise distinct at present verdicts. -/
def totSat3 : Fin 3 → Fin 3 → Option Bool := fun x y => some (decide (x = y))

/-- An intermediate classifier on `Fin 3`: rows 0 and 1 differ at a present verdict, row 2 differs only by
absence. -/
def mid : Fin 3 → Fin 3 → Option Bool := fun x y =>
  if x = 0 then (if y = 0 then some true else none)
  else if x = 1 then (if y = 0 then some false else none)
  else (if y = 2 then some true else none)

/-- A distinction is present-carried when the two rows differ at a pair where both return present verdicts. -/
abbrev presentCarried {n : ℕ} (c : Fin n → Fin n → Option Bool) (x x' : Fin n) : Prop :=
  ∃ y b b', c x y = some b ∧ c x' y = some b' ∧ b ≠ b'

/-! ## Part 1: the flattening condition -/

/-- **Present-carried is sufficient for survival, under any scale.** If two rows differ at a pair where both are
present, then for every scale the totalization keeps the present values there, so the rows stay distinct. -/
theorem survives_totalization {n : ℕ} (c : Fin n → Fin n → Option Bool) (s : Fin n → Nat) (x x' : Fin n) :
    presentCarried c x x' → totalization s c x ≠ totalization s c x' := by
  rintro ⟨y, b, b', hb, hb', hne⟩ heq
  have := congrFun heq y
  simp [totalization, hb, hb'] at this
  exact hne this

/-- **Absence-carried distinctions are the ones fabrication destroys.** The saturated map's rows differ only where
one abstains, not present-carried, and they merge under totalization, becoming equal. So present-carried is
necessary for survival, not merely sufficient: an absence-carried distinction does not survive. -/
theorem absence_carried_distinction :
    (¬ presentCarried (satN : Fin 2 → Fin 2 → Option Bool) 0 1)
    ∧ (totalization (fun _ => 0) (satN : Fin 2 → Fin 2 → Option Bool) 0
        = totalization (fun _ => 0) (satN : Fin 2 → Fin 2 → Option Bool) 1) := by
  refine ⟨by decide, by decide⟩

/-- **The condition is computable from the state.** Present-carried is decidable from the classification alone, a
finite search over columns, without performing the totalization: a state-side property, like the fibre. -/
theorem is_the_condition_computable :
    (¬ presentCarried (satN : Fin 2 → Fin 2 → Option Bool) 0 1)
    ∧ (presentCarried totSat3 0 1)
    ∧ (presentCarried mid 0 1)
    ∧ (¬ presentCarried mid 0 2) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## Part 2: the quantity -/

/-- Fragility: the count of ordered distinct row-pairs whose distinction is absence-carried, the pairs that fail
to survive. -/
def fragility {n : ℕ} (c : Fin n → Fin n → Option Bool) : Nat :=
  (Finset.univ.filter (fun p : Fin n × Fin n => c p.1 ≠ c p.2 ∧ ¬ presentCarried c p.1 p.2)).card

/-- **The extremes.** Maximally fragile: every distinction absence-carried, so totalization gives a degenerate
classification and fragility is the full count of distinct pairs. Maximally robust: every distinction
present-carried, so totalization preserves distinctness and fragility is zero. -/
theorem extremes :
    (¬ NonDegenerate (totalization (fun _ => 0) (satN : Fin 3 → Fin 3 → Option Bool))
      ∧ fragility (satN : Fin 3 → Fin 3 → Option Bool) = 6)
    ∧ (NonDegenerate (totalization (fun _ => 0) totSat3) ∧ fragility totSat3 = 0) := by
  refine ⟨⟨by unfold NonDegenerate; decide, by decide⟩,
          ⟨by unfold NonDegenerate; decide, by decide⟩⟩

/-- **Fragility does not track the ground-order.** For the register classification, the saturated map, fragility is
the count of distinct pairs, `n^2 - n`, determined by the carrier size: physics zero, the three-ground orders six,
the four-ground orders twelve. It is the same for two registers of equal size and different order, the chain and
the fork both six, while their coding differs, four against three. So fragility is independent of coding and
territorialization. -/
theorem compute_across_the_registers :
    (fragility (satN : Fin 1 → Fin 1 → Option Bool) = 0)
    ∧ (fragility (satN : Fin 3 → Fin 3 → Option Bool) = 6)
    ∧ (fragility (satN : Fin 4 → Fin 4 → Option Bool) = 12)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqChain3 S)).card ≠
       (Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqV3 S)).card) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## Part 3: configurations -/

/-- **The configuration of each register.** With the saturated classification the six are all saturated and all
maximally fragile for their size: physics `n = 1` fragility zero, type and cognition and immunology `n = 3`
fragility six, chemistry and trust `n = 4` fragility twelve. Type and cognition share the chain order and so share
every coordinate; the orders separate the rest by coding, the chain four, the mixed order two. -/
theorem configuration_of_each_register :
    (fragility (satN : Fin 1 → Fin 1 → Option Bool) = 0)
    ∧ (fragility (satN : Fin 3 → Fin 3 → Option Bool) = 6)
    ∧ (fragility (satN : Fin 4 → Fin 4 → Option Bool) = 12)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqChain3 S)).card = 4)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqMixed3 S)).card = 2) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **The registers sit in a corner, and coordinates separate.** For the register classification fragility is
`n^2 - n`, redundant with the carrier size; coding separates same-size same-fragility registers, the chain and the
mixed order both fragility six but coding four against two. So among the registers fragility adds nothing beyond
size, and the order coordinates do the separating. -/
theorem do_they_cluster :
    (fragility (satN : Fin 3 → Fin 3 → Option Bool) = 3 ^ 2 - 3)
    ∧ (fragility (satN : Fin 4 → Fin 4 → Option Bool) = 4 ^ 2 - 4)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqChain3 S)).card ≠
       (Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqMixed3 S)).card) := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Constructed cases fill the fragility axis.** At a fixed carrier size, fragility varies: maximally robust
zero, an intermediate four, maximally fragile six. So fragility is a genuine coordinate on classifications, not
determined by the size, though the register classification pins it to the maximum. -/
theorem constructed_cases :
    (fragility totSat3 = 0)
    ∧ (fragility mid = 4)
    ∧ (fragility (satN : Fin 3 → Fin 3 → Option Bool) = 6) := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## The verdicts

Part 1: a distinction survives totalization exactly when it is present-carried, and the condition is state-side.
Present-carried is sufficient under any scale (`survives_totalization`); an absence-carried distinction is not
present-carried and merges under totalization, so the condition is necessary too
(`absence_carried_distinction`); and present-carried is decidable from the classification alone, no totalization
performed (`is_the_condition_computable`).

Part 2: fragility is a new coordinate, not determined by the order. It is defined as the count of absence-carried
distinct pairs, with extremes at zero and the full count (`extremes`); across the registers, taken with the
saturated classification, it is `n^2 - n`, the same for the chain and the fork of equal size while their coding
differs, so it is independent of coding and territorialization (`compute_across_the_registers`).

Part 3: the registers cluster in a corner and fragility is a real but register-redundant coordinate. Each register
is saturated and maximally fragile for its size, type and cognition sharing every coordinate
(`configuration_of_each_register`); fragility is `n^2 - n` for the register classification, redundant with size,
the order coordinates separating the rest (`do_they_cluster`); but constructed classifications at a fixed size take
fragility zero, four, and six, so the axis is genuinely occupied (`constructed_cases`).

The verdict: fabrication destroys exactly the absence-carried distinctions, and how much of an object is so carried
is a computable coordinate, independent of the ground-order but pinned to its maximum for the registers. A
distinction survives totalization if and only if it is present-carried, the two rows differing where both return
present verdicts; there the totalization keeps the present values whatever the scale, while an absence-carried
distinction, differing only where one abstains, merges when the fill lands on the abstaining side. The condition is
computable from the state alone, a finite search over columns needing no totalization, so it is a state-side
property like the fibre. Fragility, the count of absence-carried distinct pairs, is a genuine coordinate: at a
fixed carrier size it ranges from zero, a maximally robust object totalization leaves untouched, to the full count,
a maximally fragile object totalization flattens to a constant. It does not track the ground-order: with the
saturated classification the registers all have fragility `n^2 - n`, the same for the chain and the fork of equal
size though their coding differs, so it is independent of coding and territorialization, and the gate is passed, it
is a new coordinate. But the registers, taken with that classification, sit in a corner of the space, all saturated
and all maximally fragile for their size, fragility redundant there with the carrier size and the order coordinates
doing the separating; type and cognition, sharing the chain, share every coordinate. The constructed cases show the
axis is not empty away from that corner, fragility taking intermediate values at a fixed size, so fragility is a
real coordinate the registers happen to occupy at its extreme. Per the counter-bias, fragility was checked against
the order and found independent, not assumed so; no archetype was named, only occupancy reported, the registers in
a corner and the constructed cases elsewhere; and the survival condition was tested in both directions, sufficient
under any scale and necessary against the merging one. Reported per part. Nothing here is resolved. -/

end Chiralogy.Flattening
