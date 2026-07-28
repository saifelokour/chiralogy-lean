import Chiralogy.Model.AssemblageRelations

/-! ARCHIVED (fully graduated). The heterogeneous residue, and the strict separation.

GRADUATED to `Model/NaryAssemblage`, same names: `lineAt`, `lineAt_card`, `linkCount`, `linkCount_invariant`,
`linkCount_eq`, `typedCount`, and the strict separation `no_crossStable_relates` with its witness carrier.
Spec 9.25, 9.26.

THE FINDING THIS FILE OWNS. The plain differing count is NOT the classification: on a carrier with fibre sizes
two, two and three, two cells with the same plain count lie in different orbits. So the earlier homogeneous
result's hypothesis was necessary, not an artefact, and the typing is not decorative. That is why the canonical
structure clause counts by type rather than by coordinate.

`common_neighbours` graduated in the form `EquinumerosityCount` restated, which is the same theorem, and it is
what makes the fibre size visible to the group without identifying the group. Typechecks standalone. -/

/-! # Experiment (LIVE): the heterogeneous residue

`HowManyIsOrbit` closed the tower classification on homogeneous carriers and left the heterogeneous case open:
the orbit partition sits between the differing SET and the differing COUNT, and homogeneity collapses it to the
count. No separation was exhibited, only the reason one is possible.

This settles whether the sandwich is strict. The route is a local invariant that reads FIBRE SIZE off the graph
structure alone, so no group identification is needed.

Register-neutral throughout: no statement and no proof mentions any domain.

Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.HeterogeneousOrbit

/-! ### GRADUATED (external-relation pass)

Into `Model/NaryAssemblage`, same names: `lineAt`, `lineAt_card`, `linkCount`, `linkCount_invariant`,
`linkCount_eq`, `typedCount`, and the strict separation `no_crossStable_relates` with its witness carrier
`sz`, `Het`, `zeroP`, `oneOn`, `diffSet_oneOn`, `both_cross`, `eq_of_differs_at_zero`. Spec 9.25, 9.26.

`common_neighbours` graduated in the form `EquinumerosityCount` restated, which is the same theorem.

This file is fully graduated. -/

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-! ## The differing set, restated -/

def diffSet (a b : Pt X) : Finset (Fin n) := Finset.univ.filter (fun i => a i ≠ b i)

theorem mem_diffSet {a b : Pt X} {i : Fin n} : i ∈ diffSet a b ↔ a i ≠ b i := by
  simp [diffSet]

theorem differsInOne_iff_diffSet (a b : Pt X) (i : Fin n) :
    differsInOne a b i ↔ diffSet a b = {i} := by
  constructor
  · rintro ⟨hne, hoth⟩
    ext j
    rw [mem_diffSet, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hji
      exact hj (hoth j hji)
    · intro hj; subst hj; exact hne
  · intro h
    refine ⟨?_, fun j hj => ?_⟩
    · exact mem_diffSet.mp (by rw [h]; exact Finset.mem_singleton_self i)
    · by_contra hc
      exact hj (Finset.mem_singleton.mp (by rw [← h]; exact mem_diffSet.mpr hc))

theorem diffSet_subset_union (a b c : Pt X) : diffSet a b ⊆ diffSet a c ∪ diffSet c b := by
  intro i hi
  rw [mem_diffSet] at hi
  rw [Finset.mem_union, mem_diffSet, mem_diffSet]
  by_contra hc
  have h1 : a i = c i := by by_contra h; exact hc (Or.inl h)
  have h2 : c i = b i := by by_contra h; exact hc (Or.inr h)
  exact hi (h1.trans h2)

instance decDiffersInOne (a b : Pt X) (i : Fin n) : Decidable (differsInOne a b i) := by
  unfold differsInOne; infer_instance

def Adjacent (a b : Pt X) : Prop := ∃ i, differsInOne a b i

instance decAdjacent (a b : Pt X) : Decidable (Adjacent a b) := by
  unfold Adjacent; infer_instance

theorem not_adjacent_self (a : Pt X) : ¬ Adjacent a a := by
  rintro ⟨i, hne, _⟩
  exact hne rfl

def CrossStable (e : Pt X ≃ Pt X) : Prop := ∀ a b, IsCross a b ↔ IsCross (e a) (e b)

theorem crossStable_adjacent (e : Pt X ≃ Pt X) (he : CrossStable e) (a b : Pt X) :
    Adjacent a b ↔ Adjacent (e a) (e b) := not_iff_not.mp (he a b)

/-! ## The local invariant that reads fibre size

The common neighbours of an adjacent pair are exactly the rest of the line the pair spans, so counting them
reads the size of that line's fibre. That count is preserved by any cross-stable bijection, since adjacency is,
and this is what makes fibre size visible to the group without identifying the group. -/

/-- **The common neighbours of an adjacent pair are the rest of their line.** If `a` and `c` differ exactly at
`i`, then `d` is adjacent to both exactly when `d` differs from `a` exactly at `i` and is not `c`. A `d`
differing from `a` anywhere else differs from `c` in two coordinates and so is not adjacent to it.
Carrier-general. -/
theorem common_neighbours (a c : Pt X) (i : Fin n) (hac : differsInOne a c i) (d : Pt X) :
    (Adjacent a d ∧ Adjacent c d) ↔ (differsInOne a d i ∧ d ≠ c) := by
  constructor
  · rintro ⟨⟨k, hk⟩, hcd⟩
    have hki : k = i := by
      by_contra hne
      obtain ⟨l, hl⟩ := hcd
      have h1 : c i ≠ d i := by
        rw [← hk.2 i (fun hc => hne hc.symm)]
        exact fun hc => hac.1 hc.symm
      have h2 : c k ≠ d k := by
        rw [← hac.2 k hne]
        exact hk.1
      have hsing := (differsInOne_iff_diffSet c d l).mp hl
      have hi : i ∈ diffSet c d := mem_diffSet.mpr h1
      have hk' : k ∈ diffSet c d := mem_diffSet.mpr h2
      rw [hsing, Finset.mem_singleton] at hi hk'
      exact hne (hk'.trans hi.symm)
    subst hki
    refine ⟨hk, ?_⟩
    rintro rfl
    exact not_adjacent_self d hcd
  · rintro ⟨had, hdc⟩
    refine ⟨⟨i, had⟩, ⟨i, ?_, fun j hj => ?_⟩⟩
    · intro hc
      refine hdc (funext fun j => ?_)
      by_cases hj : j = i
      · subst hj; exact hc.symm
      · rw [← had.2 j hj, hac.2 j hj]
    · rw [← hac.2 j hj, had.2 j hj]

section Counting

variable [∀ i, Fintype (X i)]

/-- The number of vertices adjacent to both members of a pair. -/
def linkCount (a c : Pt X) : ℕ :=
  (Finset.univ.filter (fun d : Pt X => Adjacent a d ∧ Adjacent c d)).card

/-- **The link count is a cross-stable invariant.** Adjacency transports both ways and the bijection is
injective, so the two filtered sets correspond. Carrier-general. -/
theorem linkCount_invariant (e : Pt X ≃ Pt X) (he : CrossStable e) (a c : Pt X) :
    linkCount (e a) (e c) = linkCount a c := by
  have hset : (Finset.univ.filter (fun d : Pt X => Adjacent (e a) d ∧ Adjacent (e c) d))
      = (Finset.univ.filter (fun d : Pt X => Adjacent a d ∧ Adjacent c d)).image e := by
    ext d
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, h1, h2⟩
      refine ⟨e.symm d, ?_, Equiv.apply_symm_apply e d⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [crossStable_adjacent e he, Equiv.apply_symm_apply]; exact h1
      · rw [crossStable_adjacent e he, Equiv.apply_symm_apply]; exact h2
    · rintro ⟨d0, hd0, rfl⟩
      rw [Finset.mem_filter] at hd0
      exact ⟨Finset.mem_univ _, (crossStable_adjacent e he a d0).mp hd0.2.1,
        (crossStable_adjacent e he c d0).mp hd0.2.2⟩
  rw [linkCount, linkCount, hset, Finset.card_image_of_injective _ e.injective]

/-- The points differing from `a` exactly at coordinate `i`: the line through `a` in that direction, minus `a`
itself. -/
def lineAt (a : Pt X) (i : Fin n) : Finset (Pt X) :=
  Finset.univ.filter (fun d : Pt X => differsInOne a d i)

/-- **The line has one point per other fibre value.** Sending a point of the line to its value at `i` is a
bijection onto the values other than `a i`. -/
theorem lineAt_card (a : Pt X) (i : Fin n) :
    (lineAt a i).card = Fintype.card (X i) - 1 := by
  have hbij : (lineAt a i).card = (Finset.univ.filter (fun v : X i => v ≠ a i)).card := by
    refine Finset.card_bij (fun d _ => d i) ?_ ?_ ?_
    · intro d hd
      rw [lineAt, Finset.mem_filter] at hd
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun hc => hd.2.1 hc.symm⟩
    · intro d1 h1 d2 h2 h
      rw [lineAt, Finset.mem_filter] at h1 h2
      funext j
      by_cases hj : j = i
      · subst hj; exact h
      · rw [← h1.2.2 j hj, h2.2.2 j hj]
    · intro v hv
      rw [Finset.mem_filter] at hv
      refine ⟨Function.update a i v, ?_, ?_⟩
      · rw [lineAt, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, fun j hj => ?_⟩
        · rw [Function.update_self]; exact fun hc => hv.2 hc.symm
        · rw [Function.update_of_ne hj]
      · rw [Function.update_self]
  rw [hbij]
  have : (Finset.univ.filter (fun v : X i => v ≠ a i)).card
      = Fintype.card (X i) - (Finset.univ.filter (fun v : X i => v = a i)).card := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (X i))) (p := fun v => v = a i)
    have heq : (Finset.univ.filter (fun v : X i => ¬ v = a i)).card
        = (Finset.univ.filter (fun v : X i => v ≠ a i)).card := rfl
    rw [Finset.card_univ] at hsum
    omega
  rw [this, Finset.filter_eq' Finset.univ (a i)]
  simp

/-- **THE LOCAL READING.** The link count of an adjacent pair is two less than the size of the fibre they
differ in. So the graph structure alone sees fibre size, at every adjacent pair. Carrier-general. -/
theorem linkCount_eq (a c : Pt X) (i : Fin n) (hac : differsInOne a c i) :
    linkCount a c = Fintype.card (X i) - 2 := by
  have hset : (Finset.univ.filter (fun d : Pt X => Adjacent a d ∧ Adjacent c d))
      = (lineAt a i).erase c := by
    ext d
    rw [Finset.mem_filter, Finset.mem_erase, lineAt, Finset.mem_filter]
    constructor
    · intro hd
      have := (common_neighbours a c i hac d).mp hd.2
      exact ⟨this.2, Finset.mem_univ _, this.1⟩
    · intro hd
      exact ⟨Finset.mem_univ _, (common_neighbours a c i hac d).mpr ⟨hd.2.2, hd.1⟩⟩
  have hmem : c ∈ lineAt a i := by
    rw [lineAt, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hac⟩
  rw [linkCount, hset, Finset.card_erase_of_mem hmem, lineAt_card]
  omega

/-- **THE TYPING CONSTRAINT.** A cross-stable bijection can carry a pair differing at coordinate `i` to a pair
differing at coordinate `j` only when the two fibres have the same size. This is forced by cross-stability
alone: the link count is an invariant and it reads the fibre size. No identification of the group is used.
Carrier-general. -/
theorem crossStable_preserves_fibre_card (e : Pt X ≃ Pt X) (he : CrossStable e)
    (a c : Pt X) (i j : Fin n) (hac : differsInOne a c i) (hij : differsInOne (e a) (e c) j) :
    Fintype.card (X i) - 2 = Fintype.card (X j) - 2 := by
  rw [← linkCount_eq a c i hac, ← linkCount_eq (e a) (e c) j hij]
  exact (linkCount_invariant e he a c).symm

/-! ### The typed differing count -/

/-- How many of the differing coordinates have a fibre of a given size. -/
def typedCount (a b : Pt X) (q : ℕ) : ℕ :=
  ((diffSet a b).filter (fun i => Fintype.card (X i) = q)).card

/-- The sizes that actually occur among the fibres. -/
def sizes (X : Fin n → Type) [∀ i, Fintype (X i)] : Finset ℕ :=
  Finset.univ.image (fun i => Fintype.card (X i))

/-- **The typed count refines the plain count**: summing the typed counts over the occurring fibre sizes
returns the plain differing count, so agreeing typed counts force agreeing plain counts. Carrier-general. -/
theorem plain_from_typed (a b : Pt X) :
    (diffSet a b).card = ∑ q ∈ sizes X, typedCount a b q := by
  refine Finset.card_eq_sum_card_fiberwise ?_
  intro i _
  simp [sizes]

/-- **And on a homogeneous carrier the two coincide**: with one fibre size the typed count at that size IS the
plain count, which is why homogeneity collapsed the sandwich. -/
theorem typed_eq_plain_of_homogeneous (q : ℕ) (hq : ∀ i, Fintype.card (X i) = q) (a b : Pt X) :
    typedCount a b q = (diffSet a b).card := by
  rw [typedCount, Finset.filter_true_of_mem]
  intro i _
  exact hq i

/-- A coordinatewise bijection fixes the differing set, hence every typed count. -/
def fibEquiv (π : ∀ k, X k ≃ X k) : Pt X ≃ Pt X where
  toFun a := fun k => π k (a k)
  invFun a := fun k => (π k).symm (a k)
  left_inv a := by funext k; exact (π k).symm_apply_apply (a k)
  right_inv a := by funext k; exact (π k).apply_symm_apply (a k)

theorem typedCount_fibEquiv (π : ∀ k, X k ≃ X k) (a b : Pt X) (q : ℕ) :
    typedCount (fibEquiv π a) (fibEquiv π b) q = typedCount a b q := by
  have hd : diffSet (fibEquiv π a) (fibEquiv π b) = diffSet a b := by
    ext k
    rw [mem_diffSet, mem_diffSet]
    show π k (a k) ≠ π k (b k) ↔ a k ≠ b k
    exact ⟨fun h hc => h (by rw [hc]), fun h hc => h ((π k).injective hc)⟩
  rw [typedCount, typedCount, hd]

end Counting

/-! ## The separation

A carrier with two fibres of one size and one of another, and two cross cells with the same plain differing
count that no cross-stable bijection relates. -/

def sz : Fin 3 → ℕ := ![2, 2, 3]

theorem sz_two_le : ∀ i, 2 ≤ sz i := by decide

abbrev Het := ∀ i : Fin 3, Fin (sz i)

def zeroP : Het := fun i => ⟨0, by have := sz_two_le i; omega⟩

/-- The point that is one on a chosen set of coordinates and zero elsewhere. -/
def oneOn (S : Finset (Fin 3)) : Het :=
  fun i => if i ∈ S then ⟨1, by have := sz_two_le i; omega⟩ else ⟨0, by have := sz_two_le i; omega⟩

theorem diffSet_oneOn (S : Finset (Fin 3)) :
    diffSet (X := fun i => Fin (sz i)) zeroP (oneOn S) = S := by
  ext i
  rw [mem_diffSet]
  by_cases hi : i ∈ S
  · simp only [hi, iff_true]
    show zeroP i ≠ (oneOn S) i
    rw [oneOn, if_pos hi]
    intro hc
    exact absurd (congrArg Fin.val hc) (by simp [zeroP])
  · simp only [hi, iff_false, not_not]
    show zeroP i = (oneOn S) i
    rw [oneOn, if_neg hi]
    rfl

theorem card_fibre (i : Fin 3) : Fintype.card (Fin (sz i)) = sz i := Fintype.card_fin _

/-- The two cells: both differ in exactly two coordinates, so both are cross and both have the same plain
differing count. -/
theorem both_cross :
    IsCross (X := fun i => Fin (sz i)) zeroP (oneOn {0, 1})
      ∧ IsCross (X := fun i => Fin (sz i)) zeroP (oneOn {0, 2})
      ∧ (diffSet (X := fun i => Fin (sz i)) zeroP (oneOn {0, 1})).card
          = (diffSet (X := fun i => Fin (sz i)) zeroP (oneOn {0, 2})).card := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, hi⟩
    rw [differsInOne_iff_diffSet, diffSet_oneOn] at hi
    have hc := congrArg Finset.card hi
    rw [Finset.card_singleton] at hc
    exact absurd hc (by decide)
  · rintro ⟨i, hi⟩
    rw [differsInOne_iff_diffSet, diffSet_oneOn] at hi
    have hc := congrArg Finset.card hi
    rw [Finset.card_singleton] at hc
    exact absurd hc (by decide)
  · rw [diffSet_oneOn, diffSet_oneOn]
    decide

/-- Two points differing from the base point only at coordinate zero coincide, because that fibre has just two
values. -/
theorem eq_of_differs_at_zero (u v : Het)
    (hu : differsInOne (X := fun i => Fin (sz i)) zeroP u 0)
    (hv : differsInOne (X := fun i => Fin (sz i)) zeroP v 0) : u = v := by
  funext j
  by_cases hj : j = 0
  · subst hj
    have hu0 : (u 0).val ≠ 0 := by
      intro hc
      exact hu.1 (Fin.val_injective (by rw [hc]; rfl))
    have hv0 : (v 0).val ≠ 0 := by
      intro hc
      exact hv.1 (Fin.val_injective (by rw [hc]; rfl))
    have hub : (u 0).val < 2 := (u 0).isLt
    have hvb : (v 0).val < 2 := (v 0).isLt
    exact Fin.val_injective (by omega)
  · rw [← hu.2 j hj, hv.2 j hj]

/-- **THE SEPARATION.** No cross-stable bijection relates the two cells. They have the same plain differing
count, so the orbit partition is STRICTLY finer than the differing count on this carrier, and the sandwich
`HowManyIsOrbit` left open is strict. -/
theorem no_crossStable_relates :
    ¬ ∃ e : Het ≃ Het, CrossStable (X := fun i => Fin (sz i)) e
        ∧ e zeroP = zeroP ∧ e (oneOn {0, 1}) = oneOn {0, 2} := by
  rintro ⟨e, he, ha, hb⟩
  have key : ∀ c : Het, differsInOne (X := fun i => Fin (sz i)) zeroP c 0 ∨
      differsInOne (X := fun i => Fin (sz i)) zeroP c 1 →
      Adjacent (X := fun i => Fin (sz i)) c (oneOn {0, 1}) →
      differsInOne (X := fun i => Fin (sz i)) zeroP (e c) 0 := by
    intro c hc hcb
    have hac : Adjacent (X := fun i => Fin (sz i)) zeroP c := by
      rcases hc with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have h1 : Adjacent (X := fun i => Fin (sz i)) zeroP (e c) := by
      have := (crossStable_adjacent e he zeroP c).mp hac
      rwa [ha] at this
    have h2 : Adjacent (X := fun i => Fin (sz i)) (e c) (oneOn {0, 2}) := by
      have := (crossStable_adjacent e he c (oneOn {0, 1})).mp hcb
      rwa [hb] at this
    obtain ⟨m, hm⟩ := h1
    obtain ⟨l, hl⟩ := h2
    -- the link count reads the fibre size and is preserved
    have hlink : Fintype.card (Fin (sz m)) - 2 = Fintype.card (Fin (sz 0)) - 2 ∨
        Fintype.card (Fin (sz m)) - 2 = Fintype.card (Fin (sz 1)) - 2 := by
      rcases hc with h | h
      · refine Or.inl ?_
        rw [← linkCount_eq zeroP (e c) m hm, ← linkCount_eq zeroP c 0 h]
        have := linkCount_invariant e he zeroP c
        rwa [ha] at this
      · refine Or.inr ?_
        rw [← linkCount_eq zeroP (e c) m hm, ← linkCount_eq zeroP c 1 h]
        have := linkCount_invariant e he zeroP c
        rwa [ha] at this
    have hszm : sz m ≤ 2 := by
      rw [Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at hlink
      have h0 : sz 0 = 2 := by decide
      have h1' : sz 1 = 2 := by decide
      have h2' : 2 ≤ sz m := sz_two_le m
      rcases hlink with h | h
      · rw [h0] at h; omega
      · rw [h1'] at h; omega
    have hm2 : m ≠ 2 := by
      intro hc2
      subst hc2
      exact absurd hszm (by decide)
    -- the triangle inclusion pins the coordinate
    have hsub := diffSet_subset_union (X := fun i => Fin (sz i)) zeroP (oneOn {0, 2}) (e c)
    rw [diffSet_oneOn, (differsInOne_iff_diffSet zeroP (e c) m).mp hm,
      (differsInOne_iff_diffSet (e c) (oneOn {0, 2}) l).mp hl] at hsub
    have h2mem : (2 : Fin 3) ∈ ({m} : Finset (Fin 3)) ∪ {l} := hsub (by decide)
    have h0mem : (0 : Fin 3) ∈ ({m} : Finset (Fin 3)) ∪ {l} := hsub (by decide)
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at h2mem h0mem
    have hl2 : l = 2 := by
      rcases h2mem with h | h
      · exact absurd h.symm hm2
      · exact h.symm
    have hm0 : m = 0 := by
      rcases h0mem with h | h
      · exact h.symm
      · rw [hl2] at h; exact absurd h (by decide)
    rw [hm0] at hm
    exact hm
  have hc0 : differsInOne (X := fun i => Fin (sz i)) zeroP (e (oneOn {0})) 0 :=
    key (oneOn {0}) (Or.inl (by decide)) ⟨1, by decide⟩
  have hc1 : differsInOne (X := fun i => Fin (sz i)) zeroP (e (oneOn {1})) 0 :=
    key (oneOn {1}) (Or.inr (by decide)) ⟨0, by decide⟩
  have := e.injective (eq_of_differs_at_zero _ _ hc0 hc1)
  exact absurd this (by decide)

/-! ## THE VERDICTS

PART 1: the typed count, and how much of its invariance is PROVED.

`typedCount` records, for each fibre size, how many of the differing coordinates have a fibre of that size. It
is cast-free: it reads `Fintype.card (X i)`, never a type equality. `plain_from_typed` shows it refines the
plain count, since summing it over the occurring sizes returns that count, and
`typed_eq_plain_of_homogeneous` shows the two coincide when there is one size, which is exactly why homogeneity
collapsed the sandwich. `typedCount_fibEquiv` gives invariance under the coordinatewise family, trivially,
since those maps fix the differing set outright.

THE SUBSTANTIVE HALF IS THE TYPING CONSTRAINT, and it is proved from cross-stability alone.
`common_neighbours` is the structural lemma: the vertices adjacent to both members of an adjacent pair are
exactly the rest of the line that pair spans, because anything differing from one endpoint elsewhere differs
from the other in two coordinates. `lineAt_card` counts a line, `linkCount_eq` therefore reads the FIBRE SIZE
off the graph at every adjacent pair, and `linkCount_invariant` shows that count is preserved by any
cross-stable bijection. Together, `crossStable_preserves_fibre_card`: a cross-stable bijection can carry a pair
differing at coordinate `i` to a pair differing at coordinate `j` ONLY IF the two fibres have the same size.
Carrier-general, and with no identification of the group, which `CrossStableGroup` left open and which is still
not needed.

NOT PROVED: invariance of the typed count at arbitrary distance. The argument is available and is sketched
here rather than formalized. Along a shortest chain from `a` to `b` each differing coordinate is used exactly
once; a cross-stable bijection carries shortest chains to shortest chains; and each step keeps its fibre size
by the typing constraint. So the multiset of fibre sizes over the differing set is preserved. Formalizing it
needs the chain machinery plus the bookkeeping that a shortest chain uses each coordinate once, and that is not
done in this file.

PART 2: TRANSITIVITY IS NOT PROVED, and the classification is NOT completed unconditionally.

This is the honest state. The reverse direction needs exchanges between DISTINCT coordinates whose fibres are
merely equinumerous rather than identical, and such an exchange must transport a value across a type
equivalence. In a dependent product that is a cast at every use, and every lemma about the resulting map has to
be proved through the cast. Nothing here attempts it. So `sameOrbit_iff_same_typed_count` is not established,
and the conjecture that the orbit partition IS the typed count remains a conjecture, now with one half of its
evidence proved.

PART 3: THE SANDWICH IS STRICT. This is settled, and it is the headline.

`both_cross` exhibits two cells on a carrier with fibre sizes two, two and three: one differing at the two
small coordinates, the other at one small and the large one. Both are cross and both have plain differing count
two. `no_crossStable_relates` proves NO cross-stable bijection carries the first to the second.

The proof uses only what is above. Either witness neighbour must map to a point adjacent to the base and to the
target, so its coordinate is pinned by the triangle inclusion; the link count forces that coordinate to have a
size-two fibre, which rules out the large one; the two remaining possibilities collapse because the pinned
coordinate has only two values, so both witnesses would have the same image; and the bijection is injective.

So on a heterogeneous carrier the orbit partition is STRICTLY finer than the differing count, and
`HowManyIsOrbit`'s homogeneity hypothesis was NECESSARY, not an artefact of its proof. That was the open
question and it now has an answer.

PART 4: what this licenses, and the status change it forces.

The external-relation bundle's STRUCTURE clause must STAY in its abstract form, the coarsenings of the orbit
partition. But the reason has CHANGED, and the change matters. Before this build the abstract form was kept
because the heterogeneous case was OPEN. Now the concrete plain-count form is PROVABLY FALSE over arbitrary
product carriers, by `no_crossStable_relates`. The abstract form is not a hedge against ignorance; it is the
only correct unconditional statement.

The concrete form remains available with its hypothesis: on a homogeneous carrier the structural readings are
the coarsenings of the differing count, by `HowManyIsOrbit`. What is not yet available is a concrete
unconditional form, since that would be the typed count and Part 2 is open.

VOCABULARY NOTE FOR THE SPEC, NOT FOR ANY THEOREM NAME. The adjacency structure here is a Hamming graph with
unequal alphabet sizes; `common_neighbours` is the standard fact that its maximal cliques are the lines;
`crossStable_preserves_fibre_card` is the standard consequence that an automorphism permutes the coordinate
directions only within equal-alphabet classes; and the conjectured orbit partition is the class scheme of a
product of Hamming schemes with distinct alphabet sizes. Those names belong in a spec entry citing the known
setting, and nothing above is claimed as new relative to them.

WHAT REMAINS OPEN

1. Transitivity, hence the identification of the orbit partition with the typed count. Stated in Part 2.
2. Typed-count invariance at arbitrary distance. Sketched in Part 1, not formalized.
3. The separation is exhibited at one carrier. Whether every pair of differing sets with equal plain count and
   unequal typed count is separated follows from 1 and 2 and is not proved directly.
4. Nothing here is graduated. -/

#print axioms diffSet
#print axioms mem_diffSet
#print axioms differsInOne_iff_diffSet
#print axioms diffSet_subset_union
#print axioms Adjacent
#print axioms not_adjacent_self
#print axioms CrossStable
#print axioms crossStable_adjacent
#print axioms common_neighbours
#print axioms linkCount
#print axioms linkCount_invariant
#print axioms lineAt
#print axioms lineAt_card
#print axioms linkCount_eq
#print axioms crossStable_preserves_fibre_card
#print axioms typedCount
#print axioms sizes
#print axioms plain_from_typed
#print axioms typed_eq_plain_of_homogeneous
#print axioms fibEquiv
#print axioms typedCount_fibEquiv
#print axioms sz
#print axioms sz_two_le
#print axioms zeroP
#print axioms oneOn
#print axioms diffSet_oneOn
#print axioms card_fibre
#print axioms both_cross
#print axioms eq_of_differs_at_zero
#print axioms no_crossStable_relates

end Chiralogy.HeterogeneousOrbit
