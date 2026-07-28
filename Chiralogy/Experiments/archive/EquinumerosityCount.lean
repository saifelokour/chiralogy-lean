import Chiralogy.Model.AssemblageRelations

/-! ARCHIVED (fully graduated). The lift off finiteness, and the resolved structure clause.

GRADUATED to `Model/NaryAssemblage`, same names: `Equinumerous` with its equivalence lemmas, `eqTypedCount`,
`eqTypedCount_eq_typedCount_of_finite`, the finiteness-free mechanism `lineSet`, `lineSet_eq`, `lineEquiv`,
`mem_lineSet_map`, `eqSubtypeEquivUnit`, `equiv_of_punctured`, `crossStable_equinumerous`, the two inclusions
`sameOrbit_of_same_eqTypedCount` and `eqTypedCount_crossStable_invariant`, and the conclusions
`orbit_partition_is_eqTypedCount` and `eqTypedCount_is_finest_structural`. Spec 9.24.

THE FINDING THIS FILE OWNS. It dissolved a presentation choice rather than settling one. An abstract structure
clause carried no finiteness but said little; a concrete one said what the rungs are but needed `Fintype` on
every fibre. Grouping coordinates by the EXISTENCE OF A BIJECTION rather than by a cardinal gives one object
that is general, concrete, and equal to the cardinal count on finite fibres. The step that appeared to need
finiteness, reading fibre size off the graph by counting a line, needed only that the line be TRANSPORTED, and
a set transports as well as a number counts.

The cardinal and homogeneous forms are corollaries in canonical, derived rather than reproved. Typechecks
standalone. -/

/-! # Experiment (LIVE): does the classification lift off finiteness?

The typed count needs `Fintype` because it groups coordinates by fibre CARDINALITY. But the mechanism that
makes it the orbit partition is that a cross-stable map relates two coordinates only when their fibres are
EQUINUMEROUS, and equinumerosity needs no finiteness. This tests whether the whole classification lifts by
replacing the cardinal with the equinumerosity class.

The presentation question rides on it: if the lift works there is one object and no choice between an abstract
and a concrete structure clause.

Register-neutral throughout: no statement and no proof mentions any domain.

Live experiment. No canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.EquinumerosityCount

/-! ### GRADUATED (external-relation pass)

The spine of this file IS the graduated classification, into `Model/NaryAssemblage` under the same names:
`Equinumerous` with its equivalence lemmas, `eqTypedCount`, `eqTypedCount_eq_typedCount_of_finite`, the
finiteness-free mechanism `lineSet`, `lineSet_eq`, `lineEquiv`, `mem_lineSet_map`, `eqSubtypeEquivUnit`,
`equiv_of_punctured`, `crossStable_equinumerous`, and the two inclusions
`sameOrbit_of_same_eqTypedCount` and `eqTypedCount_crossStable_invariant`, culminating in
`orbit_partition_is_eqTypedCount` and `eqTypedCount_is_finest_structural`. Spec 9.24.

This is the STRUCTURE clause. The abstract and concrete candidates it replaced are both corollaries now: the
reachability form is the definition of `SameOrbit`, and the cardinal form is spec 9.25.

This file is fully graduated. -/

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-! ## The differing set and adjacency, restated -/

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

def Adjacent (a b : Pt X) : Prop := ∃ i, differsInOne a b i

theorem not_adjacent_self (a : Pt X) : ¬ Adjacent a a := by
  rintro ⟨i, hne, _⟩
  exact hne rfl

def CrossStable (e : Pt X ≃ Pt X) : Prop := ∀ a b, IsCross a b ↔ IsCross (e a) (e b)

theorem crossStable_iff_adjacent (e : Pt X ≃ Pt X) :
    CrossStable e ↔ ∀ a b, Adjacent a b ↔ Adjacent (e a) (e b) := by
  constructor
  · intro h a b; exact not_iff_not.mp (h a b)
  · intro h a b; exact not_iff_not.mpr (h a b)

/-- The common-neighbour characterization, restated. NOTE: this is a POINTWISE equivalence and uses no
counting, so it carries no finiteness. That is what makes the lift below possible. -/
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

/-! ## Part 1: the equinumerosity type of a coordinate

The grouping the typed count does by cardinal, done instead by the existence of a bijection. Nothing here
mentions finiteness. -/

/-- Two coordinates are of the same type when their fibres admit a bijection. -/
def Equinumerous (i j : Fin n) : Prop := Nonempty (X i ≃ X j)

theorem equinumerous_refl (i : Fin n) : Equinumerous (X := X) i i := ⟨Equiv.refl _⟩

theorem equinumerous_symm {i j : Fin n} (h : Equinumerous (X := X) i j) :
    Equinumerous (X := X) j i := ⟨h.some.symm⟩

theorem equinumerous_trans {i j k : Fin n} (h : Equinumerous (X := X) i j)
    (h' : Equinumerous (X := X) j k) : Equinumerous (X := X) i k := ⟨h.some.trans h'.some⟩

open Classical in
/-- **THE EQUINUMEROSITY-TYPED COUNT.** How many of the differing coordinates share a coordinate's type. The
grouping is by the existence of a bijection between fibres, so the definition carries NO finiteness. -/
noncomputable def eqTypedCount (a b : Pt X) (j : Fin n) : ℕ :=
  ((diffSet a b).filter (fun i => Equinumerous (X := X) i j)).card

/-- **It reduces to the cardinal typed count on finite fibres**, because equinumerosity of finite types is
equality of cardinality. So the finite reading is a special case, not a different object. -/
theorem eqTypedCount_eq_typedCount_of_finite [∀ i, Fintype (X i)] (a b : Pt X) (j : Fin n) :
    eqTypedCount a b j
      = ((diffSet a b).filter (fun i => Fintype.card (X i) = Fintype.card (X j))).card := by
  classical
  rw [eqTypedCount]
  congr 1
  apply Finset.filter_congr
  intro i _
  exact ⟨fun h => Fintype.card_eq.mpr h, fun h => Fintype.card_eq.mp h⟩

/-! ## Part 2: does the invariance lift?

The finite proof read the fibre SIZE off the graph by counting a line. That count needs finiteness. The
finiteness-free replacement reads the line as a SET and transports it, which gives a bijection rather than an
equal number. -/

/-- The line through `a` spanned by an adjacent `c`, characterized graph-theoretically: the neighbours of `a`
that are `c` or adjacent to `c`. No coordinate is named and no counting occurs. -/
def lineSet (a c : Pt X) : Set (Pt X) := {d | Adjacent a d ∧ (d = c ∨ Adjacent c d)}

/-- **The graph-theoretic line IS the coordinate line.** Finiteness-free, by `common_neighbours`. -/
theorem lineSet_eq (a c : Pt X) (i : Fin n) (hac : differsInOne a c i) :
    lineSet a c = {d | differsInOne a d i} := by
  ext d
  simp only [lineSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hadj, hd | hd⟩
    · subst hd; exact hac
    · exact ((common_neighbours a c i hac d).mp ⟨hadj, hd⟩).1
  · intro hd
    by_cases hdc : d = c
    · subst hdc; exact ⟨⟨i, hd⟩, Or.inl rfl⟩
    · exact ⟨⟨i, hd⟩, Or.inr ((common_neighbours a c i hac d).mpr ⟨hd, hdc⟩).2⟩

/-- The coordinate line is the fibre with one point removed: a point of the line is determined by its value at
that coordinate, which is anything other than the base point's value. -/
def lineEquiv (a : Pt X) (i : Fin n) :
    {d : Pt X // differsInOne a d i} ≃ {v : X i // v ≠ a i} where
  toFun d := ⟨d.1 i, fun h => d.2.1 h.symm⟩
  invFun v := ⟨Function.update a i v.1, by
    refine ⟨?_, fun j hj => ?_⟩
    · rw [Function.update_self]; exact fun h => v.2 h.symm
    · rw [Function.update_of_ne hj]⟩
  left_inv d := by
    refine Subtype.ext (funext fun j => ?_)
    show Function.update a i (d.1 i) j = d.1 j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]
    · rw [Function.update_of_ne hj]; exact d.2.2 j hj
  right_inv v := by
    refine Subtype.ext ?_
    show Function.update a i v.1 i = v.1
    rw [Function.update_self]

/-- A cross-stable bijection carries a line to a line: membership is defined by adjacency alone. -/
theorem mem_lineSet_map (e : Pt X ≃ Pt X) (he : CrossStable e) (a c d : Pt X) :
    d ∈ lineSet a c ↔ e d ∈ lineSet (e a) (e c) := by
  have hadj := (crossStable_iff_adjacent e).mp he
  simp only [lineSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨(hadj a d).mp h1, Or.inl (by rw [h2])⟩
    · exact ⟨(hadj a d).mp h1, Or.inr ((hadj c d).mp h2)⟩
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨(hadj a d).mpr h1, Or.inl (e.injective h2)⟩
    · exact ⟨(hadj a d).mpr h1, Or.inr ((hadj c d).mpr h2)⟩

/-- Punctured types with a bijection between them have a bijection between the wholes: add the removed point
back on each side. Finiteness-free. -/
def eqSubtypeEquivUnit {A : Type} (x : A) : {v : A // v = x} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨x, rfl⟩
  left_inv v := Subtype.ext v.2.symm
  right_inv _ := rfl

theorem equiv_of_punctured {A B : Type} [DecidableEq A] [DecidableEq B] (x : A) (y : B)
    (h : {v : A // v ≠ x} ≃ {v : B // v ≠ y}) : Nonempty (A ≃ B) :=
  ⟨(Equiv.sumCompl (· = x)).symm.trans
    ((Equiv.sumCongr (eqSubtypeEquivUnit x) h).trans
      ((Equiv.sumCongr (eqSubtypeEquivUnit y).symm (Equiv.refl _)).trans
        (Equiv.sumCompl (· = y))))⟩

/-- **THE INVARIANCE MECHANISM, LIFTED OFF FINITENESS.** If a cross-stable bijection carries a pair differing
at coordinate `i` to a pair differing at coordinate `j`, then the two fibres are EQUINUMEROUS. The finite proof
counted a line; this one transports the line as a set and reads a bijection off it, so no finiteness is used
anywhere. -/
theorem crossStable_equinumerous (e : Pt X ≃ Pt X) (he : CrossStable e) (a c : Pt X) (i j : Fin n)
    (hac : differsInOne a c i) (hej : differsInOne (e a) (e c) j) :
    Equinumerous (X := X) i j := by
  have hline : {d : Pt X // differsInOne a d i} ≃ {d : Pt X // differsInOne (e a) d j} := by
    refine ⟨fun d => ⟨e d.1, ?_⟩, fun d => ⟨e.symm d.1, ?_⟩, ?_, ?_⟩
    · have hmem : d.1 ∈ lineSet a c := by rw [lineSet_eq a c i hac]; exact d.2
      have := (mem_lineSet_map e he a c d.1).mp hmem
      rwa [lineSet_eq (e a) (e c) j hej] at this
    · have hmem : d.1 ∈ lineSet (e a) (e c) := by rw [lineSet_eq (e a) (e c) j hej]; exact d.2
      have := (mem_lineSet_map e he a c (e.symm d.1)).mpr (by rwa [Equiv.apply_symm_apply])
      rwa [lineSet_eq a c i hac] at this
    · intro d; exact Subtype.ext (Equiv.symm_apply_apply e d.1)
    · intro d; exact Subtype.ext (Equiv.apply_symm_apply e d.1)
  exact equiv_of_punctured (a i) ((e a) j)
    (((lineEquiv a i).symm.trans hline).trans (lineEquiv (e a) j))


/-! ### Reused machinery: the orbit relation and the exchange -/

theorem exists_differsInOne_iff_card (a b : Pt X) :
    (∃ k, differsInOne a b k) ↔ (diffSet a b).card = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    rw [(differsInOne_iff_diffSet a b k).mp hk]
    exact Finset.card_singleton k
  · intro h
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h
    exact ⟨k, (differsInOne_iff_diffSet a b k).mpr hk⟩

/-- A bijection permuting the differing set by a fixed index permutation is cross-stable: the differing sets
correspond, so their sizes agree, and being cross is the size not being one. -/
theorem crossStable_of_diffSet_perm (e : Pt X ≃ Pt X) (σ : Equiv.Perm (Fin n))
    (h : ∀ a b k, k ∈ diffSet (e a) (e b) ↔ σ k ∈ diffSet a b) : CrossStable e := by
  intro a b
  have hmap : diffSet (e a) (e b) = (diffSet a b).map σ.symm.toEmbedding := by
    ext k
    rw [h a b k, Finset.mem_map]
    constructor
    · intro hk
      refine ⟨σ k, hk, ?_⟩
      show σ.symm (σ k) = k
      rw [Equiv.symm_apply_apply]
    · rintro ⟨m, hm, rfl⟩
      show σ (σ.symm m) ∈ _
      rw [Equiv.apply_symm_apply]
      exact hm
  have hcard : (diffSet (e a) (e b)).card = (diffSet a b).card := by
    rw [hmap, Finset.card_map]
  show (¬ ∃ k, differsInOne a b k) ↔ (¬ ∃ k, differsInOne (e a) (e b) k)
  rw [exists_differsInOne_iff_card, exists_differsInOne_iff_card, hcard]

def SameOrbit (a b a' b' : Pt X) : Prop :=
  ∃ e : Pt X ≃ Pt X, CrossStable e ∧ e a = a' ∧ e b = b'

theorem crossStable_trans {e f : Pt X ≃ Pt X} (he : CrossStable e) (hf : CrossStable f) :
    CrossStable (e.trans f) := fun a b => (he a b).trans (hf (e a) (e b))

theorem sameOrbit_trans {a b a' b' a'' b'' : Pt X}
    (h : SameOrbit a b a' b') (h' : SameOrbit a' b' a'' b'') : SameOrbit a b a'' b'' := by
  obtain ⟨e, he, h1, h2⟩ := h
  obtain ⟨f, hf, k1, k2⟩ := h'
  refine ⟨e.trans f, crossStable_trans he hf, ?_, ?_⟩
  · show f (e a) = a''; rw [h1, k1]
  · show f (e b) = b''; rw [h2, k2]

theorem exists_equiv_pair {Y : Type} [DecidableEq Y] {u v u' v' : Y} (huv : u ≠ v) (huv' : u' ≠ v') :
    ∃ f : Y ≃ Y, f u = u' ∧ f v = v' := by
  refine ⟨(Equiv.swap u u').trans (Equiv.swap (Equiv.swap u u' v) v'), ?_, ?_⟩
  · show Equiv.swap (Equiv.swap u u' v) v' (Equiv.swap u u' u) = u'
    rw [Equiv.swap_apply_left]
    by_cases hw : Equiv.swap u u' v = v'
    · rw [hw, Equiv.swap_self]
      rfl
    · refine Equiv.swap_apply_of_ne_of_ne ?_ huv'
      intro hc
      by_cases hvu' : v = u'
      · rw [hvu', Equiv.swap_apply_right] at hc
        exact huv (hvu'.trans hc).symm
      · rw [Equiv.swap_apply_of_ne_of_ne (fun hx => huv hx.symm) hvu'] at hc
        exact hvu' hc.symm
  · show Equiv.swap (Equiv.swap u u' v) v' (Equiv.swap u u' v) = v'
    exact Equiv.swap_apply_left _ _

noncomputable def movePair {Y : Type} [DecidableEq Y] (u v u' v' : Y) : Y ≃ Y :=
  if h : u ≠ v ∧ u' ≠ v' then Classical.choose (exists_equiv_pair h.1 h.2)
  else Equiv.swap u u'

theorem movePair_spec_ne {Y : Type} [DecidableEq Y] {u v u' v' : Y} (huv : u ≠ v) (huv' : u' ≠ v') :
    movePair u v u' v' u = u' ∧ movePair u v u' v' v = v' := by
  have hd : u ≠ v ∧ u' ≠ v' := ⟨huv, huv'⟩
  rw [movePair, dif_pos hd]
  exact Classical.choose_spec (exists_equiv_pair hd.1 hd.2)

theorem movePair_spec_eq {Y : Type} [DecidableEq Y] {u v u' v' : Y} (huv : u = v) (huv' : u' = v') :
    movePair u v u' v' u = u' ∧ movePair u v u' v' v = v' := by
  have hd : ¬ (u ≠ v ∧ u' ≠ v') := fun h => h.1 huv
  rw [movePair, dif_neg hd]
  refine ⟨Equiv.swap_apply_left u u', ?_⟩
  rw [← huv, Equiv.swap_apply_left u u']
  exact huv'

def fibEquiv (π : ∀ k, X k ≃ X k) : Pt X ≃ Pt X where
  toFun a := fun k => π k (a k)
  invFun a := fun k => (π k).symm (a k)
  left_inv a := by funext k; exact (π k).symm_apply_apply (a k)
  right_inv a := by funext k; exact (π k).apply_symm_apply (a k)

theorem diffSet_fibEquiv (π : ∀ k, X k ≃ X k) (a b : Pt X) :
    diffSet (fibEquiv π a) (fibEquiv π b) = diffSet a b := by
  ext k
  rw [mem_diffSet, mem_diffSet]
  show π k (a k) ≠ π k (b k) ↔ a k ≠ b k
  exact ⟨fun h hc => h (by rw [hc]), fun h hc => h ((π k).injective hc)⟩

theorem fibEquiv_crossStable (π : ∀ k, X k ≃ X k) : CrossStable (fibEquiv π) :=
  crossStable_of_diffSet_perm _ (Equiv.refl _) (fun a b k => by
    rw [diffSet_fibEquiv]; exact Iff.rfl)

/-- The coordinatewise half: two cells with the same differing set lie in one orbit, no hypothesis. -/
theorem sameOrbit_of_same_diffSet (a b a' b' : Pt X) (h : diffSet a b = diffSet a' b') :
    SameOrbit a b a' b' := by
  refine ⟨fibEquiv (fun k => movePair (a k) (b k) (a' k) (b' k)),
    fibEquiv_crossStable _, ?_, ?_⟩
  · funext k
    show movePair (a k) (b k) (a' k) (b' k) (a k) = a' k
    by_cases hk : a k = b k
    · have hk' : a' k = b' k := by
        by_contra hc
        have h1 : k ∈ diffSet a' b' := mem_diffSet.mpr hc
        rw [← h] at h1
        exact (mem_diffSet.mp h1) hk
      exact (movePair_spec_eq hk hk').1
    · have hk' : a' k ≠ b' k := by
        intro hc
        have h1 : k ∈ diffSet a b := mem_diffSet.mpr hk
        rw [h] at h1
        exact (mem_diffSet.mp h1) hc
      exact (movePair_spec_ne hk hk').1
  · funext k
    show movePair (a k) (b k) (a' k) (b' k) (b k) = b' k
    by_cases hk : a k = b k
    · have hk' : a' k = b' k := by
        by_contra hc
        have h1 : k ∈ diffSet a' b' := mem_diffSet.mpr hc
        rw [← h] at h1
        exact (mem_diffSet.mp h1) hk
      exact (movePair_spec_eq hk hk').2
    · have hk' : a' k ≠ b' k := by
        intro hc
        have h1 : k ∈ diffSet a b := mem_diffSet.mpr hk
        rw [h] at h1
        exact (mem_diffSet.mp h1) hc
      exact (movePair_spec_ne hk hk').2

/-! ## Part 1: the exchange between equinumerous fibres

The map below is the one the previous build did not attempt. It exchanges coordinates `i` and `j` while
carrying the value across an equivalence `X i` to `X j`. The value at `i` has type `X i` and must be delivered
at `j`, which needs a CAST, and every lemma about the map passes through it. -/

/-- **THE TYPED EXCHANGE.** Swap coordinates `i` and `j`, transporting the values along `ψ`. The two casts are
what make the definition typecheck at all: the branch for `k = i` produces a value of type `X i` and must be
delivered at type `X k`. -/
def swapT (i j : Fin n) (ψ : X i ≃ X j) (a : Pt X) : Pt X :=
  fun k =>
    if hi : k = i then cast (congrArg X hi.symm) (ψ.symm (a j))
    else if hj : k = j then cast (congrArg X hj.symm) (ψ (a i))
    else a k

/-- Reading the exchange at `i`: the cast is along `rfl` and vanishes. -/
theorem swapT_i (ψ : X i ≃ X j) (a : Pt X) : swapT i j ψ a i = ψ.symm (a j) := by
  show (if hi : i = i then cast (congrArg X hi.symm) (ψ.symm (a j))
        else if hj : i = j then cast (congrArg X hj.symm) (ψ (a i)) else a i) = ψ.symm (a j)
  rw [dif_pos (rfl : i = i)]
  rfl

/-- Reading the exchange at `j`. -/
theorem swapT_j (hij : i ≠ j) (ψ : X i ≃ X j) (a : Pt X) : swapT i j ψ a j = ψ (a i) := by
  show (if hi : j = i then cast (congrArg X hi.symm) (ψ.symm (a j))
        else if hj : j = j then cast (congrArg X hj.symm) (ψ (a i)) else a j) = ψ (a i)
  rw [dif_neg (fun h => hij h.symm), dif_pos (rfl : j = j)]
  rfl

/-- Reading the exchange anywhere else: untouched. -/
theorem swapT_other (ψ : X i ≃ X j) (a : Pt X) {k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    swapT i j ψ a k = a k := by
  show (if hi : k = i then cast (congrArg X hi.symm) (ψ.symm (a j))
        else if hj : k = j then cast (congrArg X hj.symm) (ψ (a i)) else a k) = a k
  rw [dif_neg hki, dif_neg hkj]

theorem swapT_involutive (hij : i ≠ j) (ψ : X i ≃ X j) (a : Pt X) :
    swapT i j ψ (swapT i j ψ a) = a := by
  funext k
  by_cases hki : k = i
  · subst hki
    rw [swapT_i, swapT_j hij, Equiv.symm_apply_apply]
  · by_cases hkj : k = j
    · subst hkj
      rw [swapT_j hij, swapT_i, Equiv.apply_symm_apply]
    · rw [swapT_other ψ _ hki hkj, swapT_other ψ a hki hkj]

/-- The exchange as a bijection of the carrier. -/
def coordSwapT (hij : i ≠ j) (ψ : X i ≃ X j) : Pt X ≃ Pt X :=
  ⟨swapT i j ψ, swapT i j ψ, swapT_involutive hij ψ, swapT_involutive hij ψ⟩

/-- **The exchange permutes the differing set by the index swap.** Every clause passes through a cast, and the
casts are discharged by the three reading lemmas above rather than by any tactic guessing. -/
theorem mem_diffSet_swapT (hij : i ≠ j) (ψ : X i ≃ X j) (a b : Pt X) (k : Fin n) :
    k ∈ diffSet (swapT i j ψ a) (swapT i j ψ b) ↔ Equiv.swap i j k ∈ diffSet a b := by
  rw [mem_diffSet, mem_diffSet]
  by_cases hki : k = i
  · subst hki
    rw [swapT_i, swapT_i, Equiv.swap_apply_left]
    exact ⟨fun h hc => h (by rw [hc]), fun h hc => h (ψ.symm.injective hc)⟩
  · by_cases hkj : k = j
    · subst hkj
      rw [swapT_j hij, swapT_j hij, Equiv.swap_apply_right]
      exact ⟨fun h hc => h (by rw [hc]), fun h hc => h (ψ.injective hc)⟩
    · rw [swapT_other ψ a hki hkj, swapT_other ψ b hki hkj,
        Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem diffSet_swapT (hij : i ≠ j) (ψ : X i ≃ X j) (a b : Pt X) :
    diffSet (swapT i j ψ a) (swapT i j ψ b)
      = (diffSet a b).map (Equiv.swap i j).toEmbedding := by
  ext k
  rw [mem_diffSet_swapT hij, Finset.mem_map]
  constructor
  · intro hk
    refine ⟨Equiv.swap i j k, hk, ?_⟩
    show Equiv.swap i j (Equiv.swap i j k) = k
    rw [Equiv.swap_apply_self]
  · rintro ⟨m, hm, rfl⟩
    show Equiv.swap i j (Equiv.swap i j m) ∈ _
    rw [Equiv.swap_apply_self]
    exact hm

/-- **The exchange is cross-stable.** -/
theorem coordSwapT_crossStable (hij : i ≠ j) (ψ : X i ≃ X j) :
    CrossStable (coordSwapT hij ψ) :=
  crossStable_of_diffSet_perm _ (Equiv.swap i j) (fun a b k => mem_diffSet_swapT hij ψ a b k)

/-- The exchange step, at the level of the set difference. -/
theorem sdiff_after_swapT (S T : Finset (Fin n)) {i j : Fin n}
    (hi : i ∈ S) (hiT : i ∉ T) (hj : j ∈ T) (hjS : j ∉ S) :
    (S.map (Equiv.swap i j).toEmbedding) \ T = (S \ T).erase i := by
  ext k
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hkT⟩
    have hpi : p ≠ i := by
      intro hc
      subst hc
      rw [Equiv.swap_apply_left] at hkT
      exact hkT hj
    have hpj : p ≠ j := fun hc => hjS (hc ▸ hp)
    rw [Equiv.swap_apply_of_ne_of_ne hpi hpj] at hkT ⊢
    exact ⟨hpi, hp, hkT⟩
  · rintro ⟨hki, hkS, hkT⟩
    have hkj : k ≠ j := fun hc => hkT (hc ▸ hj)
    exact ⟨⟨k, hkS, Equiv.swap_apply_of_ne_of_ne hki hkj⟩, hkT⟩

/-! ## Part 2b: does the transitivity lift?

The exchange takes a bijection between two fibres as a parameter and never mentions cardinality. The finite
proof obtained that bijection from equal cardinalities; here it comes straight from equinumerosity, which is
the only place finiteness entered. -/

/-- **The exchange preserves every equinumerosity-typed count.** It swaps two coordinates of the SAME type, so
each type class keeps its membership count. Finiteness-free. -/
theorem eqTypedCount_swapT {i j : Fin n} (hij : i ≠ j) (ψ : X i ≃ X j)
    (heq : Equinumerous (X := X) i j) (a b : Pt X) (m : Fin n) :
    eqTypedCount (swapT i j ψ a) (swapT i j ψ b) m = eqTypedCount a b m := by
  classical
  have hP : ∀ p : Fin n,
      Equinumerous (X := X) (Equiv.swap i j p) m ↔ Equinumerous (X := X) p m := by
    intro p
    by_cases hpi : p = i
    · subst hpi
      rw [Equiv.swap_apply_left]
      exact ⟨fun h => equinumerous_trans heq h, fun h => equinumerous_trans (equinumerous_symm heq) h⟩
    · by_cases hpj : p = j
      · subst hpj
        rw [Equiv.swap_apply_right]
        exact ⟨fun h => equinumerous_trans (equinumerous_symm heq) h,
          fun h => equinumerous_trans heq h⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj]
  have hset : ((diffSet a b).map (Equiv.swap i j).toEmbedding).filter
        (fun p => Equinumerous (X := X) p m)
      = ((diffSet a b).filter (fun p => Equinumerous (X := X) p m)).map
        (Equiv.swap i j).toEmbedding := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hk⟩
      exact ⟨p, ⟨hp, (hP p).mp hk⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hq⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, (hP p).mpr hq⟩
  rw [eqTypedCount, eqTypedCount, diffSet_swapT hij, hset, Finset.card_map]

/-- **THE TRANSITIVITY, FINITENESS-FREE.** Two cells with the same equinumerosity-typed count lie in one
orbit, at any product carrier, finite or not. The induction is the finite one with the bijection sourced from
equinumerosity instead of from equal cardinalities. -/
theorem sameOrbit_of_same_eqTypedCount_aux : ∀ (N : ℕ) (a b a' b' : Pt X),
    (diffSet a b \ diffSet a' b').card = N →
    (∀ m, eqTypedCount a b m = eqTypedCount a' b' m) →
    SameOrbit a b a' b' := by
  classical
  intro N
  induction N with
  | zero =>
    intro a b a' b' hN hq
    have hsub : diffSet a b ⊆ diffSet a' b' := by
      rw [← Finset.sdiff_eq_empty_iff_subset]
      exact Finset.card_eq_zero.mp hN
    refine sameOrbit_of_same_diffSet a b a' b' ?_
    by_contra hne
    obtain ⟨j, hj⟩ : (diffSet a' b' \ diffSet a b).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hc
      exact hne (Finset.Subset.antisymm hsub hc)
    rw [Finset.mem_sdiff] at hj
    have hss : (diffSet a b).filter (fun p => Equinumerous (X := X) p j)
        ⊂ (diffSet a' b').filter (fun p => Equinumerous (X := X) p j) := by
      refine ⟨Finset.filter_subset_filter _ hsub, ?_⟩
      intro hc
      have : j ∈ (diffSet a b).filter (fun p => Equinumerous (X := X) p j) :=
        hc (Finset.mem_filter.mpr ⟨hj.1, equinumerous_refl j⟩)
      exact hj.2 (Finset.mem_filter.mp this).1
    have := Finset.card_lt_card hss
    rw [← eqTypedCount, ← eqTypedCount, hq j] at this
    omega
  | succ M ih =>
    intro a b a' b' hN hq
    set S := diffSet a b with hS
    set T := diffSet a' b' with hT
    have hne : (S \ T).Nonempty := Finset.card_pos.mp (by rw [hN]; omega)
    obtain ⟨k, hkST⟩ := hne
    rw [Finset.mem_sdiff] at hkST
    set A := S.filter (fun p => Equinumerous (X := X) p k) with hA
    set B := T.filter (fun p => Equinumerous (X := X) p k) with hB
    have hkA : k ∈ A := Finset.mem_filter.mpr ⟨hkST.1, equinumerous_refl k⟩
    have hkB : k ∉ B := fun hc => hkST.2 (Finset.mem_filter.mp hc).1
    have hABcard : A.card = B.card := hq k
    have hBA : (B \ A).Nonempty := by
      refine Finset.card_pos.mp ?_
      have h1 : (A \ B).card + (A ∩ B).card = A.card := Finset.card_sdiff_add_card_inter A B
      have h2 : (B \ A).card + (B ∩ A).card = B.card := Finset.card_sdiff_add_card_inter B A
      have h3 : (A ∩ B).card = (B ∩ A).card := by rw [Finset.inter_comm]
      have h4 : 0 < (A \ B).card :=
        Finset.card_pos.mpr ⟨k, Finset.mem_sdiff.mpr ⟨hkA, hkB⟩⟩
      omega
    obtain ⟨j, hjBA⟩ := hBA
    rw [Finset.mem_sdiff] at hjBA
    have hjT : j ∈ T := (Finset.mem_filter.mp hjBA.1).1
    have hjq : Equinumerous (X := X) j k := (Finset.mem_filter.mp hjBA.1).2
    have hjS : j ∉ S := fun hc => hjBA.2 (Finset.mem_filter.mpr ⟨hc, hjq⟩)
    have hkj : k ≠ j := fun hc => hjS (hc ▸ hkST.1)
    have hkjEq : Equinumerous (X := X) k j := equinumerous_symm hjq
    let ψ : X k ≃ X j := hkjEq.some
    have hstep : SameOrbit a b (swapT k j ψ a) (swapT k j ψ b) :=
      ⟨coordSwapT hkj ψ, coordSwapT_crossStable hkj ψ, rfl, rfl⟩
    refine sameOrbit_trans hstep (ih (swapT k j ψ a) (swapT k j ψ b) a' b' ?_ ?_)
    · rw [diffSet_swapT hkj, ← hS, ← hT,
        sdiff_after_swapT S T hkST.1 hkST.2 hjT hjS,
        Finset.card_erase_of_mem (Finset.mem_sdiff.mpr hkST)]
      omega
    · intro r
      rw [eqTypedCount_swapT hkj ψ hkjEq]
      exact hq r

theorem sameOrbit_of_same_eqTypedCount (a b a' b' : Pt X)
    (h : ∀ m, eqTypedCount a b m = eqTypedCount a' b' m) : SameOrbit a b a' b' :=
  sameOrbit_of_same_eqTypedCount_aux _ a b a' b' rfl h


/-! ### Reused machinery: chains and first steps -/

theorem diffSet_eq_empty_iff (a b : Pt X) : diffSet a b = ∅ ↔ a = b := by
  constructor
  · intro h
    funext i
    by_contra hne
    have : i ∈ (∅ : Finset (Fin n)) := by rw [← h]; exact mem_diffSet.mpr hne
    simp at this
  · intro h
    subst h
    exact Finset.filter_eq_empty_iff.mpr (fun _ _ => by simp)

theorem diffSet_subset_union (a b c : Pt X) : diffSet a b ⊆ diffSet a c ∪ diffSet c b := by
  intro i hi
  rw [mem_diffSet] at hi
  rw [Finset.mem_union, mem_diffSet, mem_diffSet]
  by_contra hc
  have h1 : a i = c i := by by_contra h; exact hc (Or.inl h)
  have h2 : c i = b i := by by_contra h; exact hc (Or.inr h)
  exact hi (h1.trans h2)

def Steps : Nat → Pt X → Pt X → Prop
  | 0, a, b => a = b
  | (m + 1), a, b => ∃ c, Adjacent a c ∧ Steps m c b

theorem steps_of_diffSet : ∀ (k : Nat) (a b : Pt X), (diffSet a b).card = k → Steps k a b := by
  intro k
  induction k with
  | zero =>
    intro a b h
    exact (diffSet_eq_empty_iff a b).mp (Finset.card_eq_zero.mp h)
  | succ m ih =>
    intro a b h
    have hne : (diffSet a b).Nonempty := Finset.card_pos.mp (by rw [h]; omega)
    obtain ⟨i, hi⟩ := hne
    refine ⟨Function.update a i (b i), ⟨i, ?_⟩, ?_⟩
    · refine ⟨?_, fun j hj => ?_⟩
      · rw [Function.update_self]
        exact mem_diffSet.mp hi
      · rw [Function.update_of_ne hj]
    · refine ih _ b ?_
      have hset : diffSet (Function.update a i (b i)) b = (diffSet a b).erase i := by
        ext j
        rw [mem_diffSet, Finset.mem_erase, mem_diffSet]
        by_cases hj : j = i
        · subst hj
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hj]
          exact ⟨fun hc => ⟨hj, hc⟩, fun hc => hc.2⟩
      rw [hset, Finset.card_erase_of_mem hi, h]
      omega

theorem card_le_of_steps : ∀ (m : Nat) (a b : Pt X), Steps m a b → (diffSet a b).card ≤ m := by
  intro m
  induction m with
  | zero =>
    intro a b h
    have hab : a = b := h
    subst hab
    simp [(diffSet_eq_empty_iff a a).mpr rfl]
  | succ m ih =>
    intro a b h
    obtain ⟨c, ⟨i, hi⟩, hrest⟩ := h
    have hac : (diffSet a c).card = 1 := by
      rw [(differsInOne_iff_diffSet a c i).mp hi]
      exact Finset.card_singleton i
    have hcb := ih c b hrest
    calc (diffSet a b).card
        ≤ (diffSet a c ∪ diffSet c b).card := Finset.card_le_card (diffSet_subset_union a b c)
      _ ≤ (diffSet a c).card + (diffSet c b).card := Finset.card_union_le _ _
      _ ≤ 1 + m := Nat.add_le_add (le_of_eq hac) hcb
      _ = m + 1 := by omega

theorem crossStable_symm {e : Pt X ≃ Pt X} (he : CrossStable e) : CrossStable e.symm := by
  intro a b
  have h := he (e.symm a) (e.symm b)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact h.symm

theorem steps_transport {e : Pt X ≃ Pt X} (he : CrossStable e) :
    ∀ (m : Nat) (a b : Pt X), Steps m a b → Steps m (e a) (e b) := by
  intro m
  induction m with
  | zero => intro a b h; exact congrArg e h
  | succ m ih =>
    intro a b h
    obtain ⟨c, hadj, hrest⟩ := h
    exact ⟨e c, ((crossStable_iff_adjacent e).mp he a c).mp hadj, ih c b hrest⟩

/-- The plain differing count is preserved: cross-stability is adjacency preservation, and the count is the
shortest chain length. -/
theorem crossStable_preserves_diffCard {e : Pt X ≃ Pt X} (he : CrossStable e) (a b : Pt X) :
    (diffSet (e a) (e b)).card = (diffSet a b).card := by
  refine Nat.le_antisymm ?_ ?_
  · exact card_le_of_steps _ _ _ (steps_transport he _ a b (steps_of_diffSet _ a b rfl))
  · have hs := steps_of_diffSet (diffSet (e a) (e b)).card (e a) (e b) rfl
    have ht := steps_transport (crossStable_symm he) _ (e a) (e b) hs
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at ht
    exact card_le_of_steps _ _ _ ht

/-- The point one step from `p` toward `q` along coordinate `i`. -/
def stepAt (p q : Pt X) (i : Fin n) : Pt X := Function.update p i (q i)

theorem diffSet_stepAt_left {p q : Pt X} {i : Fin n} (hi : i ∈ diffSet p q) :
    diffSet p (stepAt p q i) = {i} := by
  ext j
  rw [mem_diffSet, Finset.mem_singleton]
  by_cases hj : j = i
  · subst hj
    rw [stepAt, Function.update_self]
    exact ⟨fun _ => rfl, fun _ => mem_diffSet.mp hi⟩
  · rw [stepAt, Function.update_of_ne hj]
    exact ⟨fun hc => absurd rfl hc, fun hc => absurd hc hj⟩

theorem diffSet_stepAt_right (p q : Pt X) (i : Fin n) :
    diffSet (stepAt p q i) q = (diffSet p q).erase i := by
  ext j
  rw [mem_diffSet, Finset.mem_erase, mem_diffSet]
  by_cases hj : j = i
  · subst hj
    rw [stepAt, Function.update_self]
    exact ⟨fun hc => absurd rfl hc, fun hc => absurd rfl hc.1⟩
  · rw [stepAt, Function.update_of_ne hj]
    exact ⟨fun hc => ⟨hj, hc⟩, fun hc => hc.2⟩

theorem stepAt_injOn (p q : Pt X) :
    ∀ i ∈ diffSet p q, ∀ j ∈ diffSet p q, stepAt p q i = stepAt p q j → i = j := by
  intro i hi j _ h
  by_contra hij
  have := congrFun h i
  rw [stepAt, stepAt, Function.update_self, Function.update_of_ne hij] at this
  exact (mem_diffSet.mp hi) this.symm

/-! ## Part 2c: assembling the mechanism into arbitrary-distance invariance

The mechanism is local, so it must be lifted to a whole cell by the first steps: each differing coordinate
sends its first step across, and the image is a first step of the image cell at an equinumerous coordinate. -/

/-- The image of a first step is a first step. -/
theorem image_step_adjacent (e : Pt X ≃ Pt X) (he : CrossStable e) (a b : Pt X) {i : Fin n}
    (hi : i ∈ diffSet a b) : ∃ j, differsInOne (e a) (e (stepAt a b i)) j := by
  have hadj : Adjacent a (stepAt a b i) := ⟨i, (differsInOne_iff_diffSet _ _ i).mpr
    (diffSet_stepAt_left hi)⟩
  exact (crossStable_iff_adjacent e).mp he a (stepAt a b i) |>.mp hadj

/-- And it lands at a differing coordinate of the image cell, because the plain count is preserved and the
step reduced it by one. -/
theorem image_step_mem (e : Pt X ≃ Pt X) (he : CrossStable e) (a b : Pt X) {i : Fin n}
    (hi : i ∈ diffSet a b) {j : Fin n} (hj : differsInOne (e a) (e (stepAt a b i)) j) :
    j ∈ diffSet (e a) (e b) := by
  by_contra hmem
  have hstep : (diffSet (e (stepAt a b i)) (e b)).card + 1 = (diffSet (e a) (e b)).card := by
    rw [crossStable_preserves_diffCard he, crossStable_preserves_diffCard he,
      diffSet_stepAt_right, Finset.card_erase_of_mem hi]
    have := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have hins : diffSet (e (stepAt a b i)) (e b) = insert j (diffSet (e a) (e b)) := by
    ext p
    rw [mem_diffSet, Finset.mem_insert, mem_diffSet]
    by_cases hp : p = j
    · subst hp
      have hpq : (e a) p = (e b) p := by
        by_contra hc
        exact hmem (mem_diffSet.mpr hc)
      exact ⟨fun _ => Or.inl rfl, fun _ hc => hj.1 (hpq.trans hc.symm)⟩
    · rw [hj.2 p hp]
      exact ⟨fun hc => Or.inr hc, fun hc => hc.resolve_left hp⟩
  rw [hins, Finset.card_insert_of_notMem hmem] at hstep
  omega

/-- The image of a first step is the first step of the image cell at that coordinate, so the correspondence is
injective. -/
theorem image_step_eq (e : Pt X ≃ Pt X) (he : CrossStable e) (a b : Pt X) {i : Fin n}
    (hi : i ∈ diffSet a b) {j : Fin n} (hj : differsInOne (e a) (e (stepAt a b i)) j) :
    e (stepAt a b i) = stepAt (e a) (e b) j := by
  have hjm := image_step_mem e he a b hi hj
  have hval : (e (stepAt a b i)) j = (e b) j := by
    by_contra hval
    have hsame : diffSet (e (stepAt a b i)) (e b) = diffSet (e a) (e b) := by
      ext p
      rw [mem_diffSet, mem_diffSet]
      by_cases hp : p = j
      · subst hp
        exact ⟨fun _ => mem_diffSet.mp hjm, fun _ => hval⟩
      · rw [hj.2 p hp]
    have hcnt : (diffSet (e (stepAt a b i)) (e b)).card + 1 = (diffSet (e a) (e b)).card := by
      rw [crossStable_preserves_diffCard he, crossStable_preserves_diffCard he,
        diffSet_stepAt_right, Finset.card_erase_of_mem hi]
      have := Finset.card_pos.mpr ⟨i, hi⟩
      omega
    rw [hsame] at hcnt
    omega
  funext p
  by_cases hp : p = j
  · subst hp
    show e (stepAt a b i) p = Function.update (e a) p ((e b) p) p
    rw [Function.update_self]
    exact hval
  · show e (stepAt a b i) p = Function.update (e a) j ((e b) j) p
    rw [Function.update_of_ne hp]
    exact (hj.2 p hp).symm

open Classical in
/-- **THE INVARIANCE, FINITENESS-FREE.** Every cross-stable bijection preserves every equinumerosity-typed
count, at arbitrary distance and at any carrier. The counting is over coordinates, which are finite by the
arity; nothing counts values. -/
theorem eqTypedCount_crossStable_invariant (e : Pt X ≃ Pt X) (he : CrossStable e) (a b : Pt X)
    (m : Fin n) : eqTypedCount (e a) (e b) m = eqTypedCount a b m := by
  classical
  have key : ∀ (f : Pt X ≃ Pt X), CrossStable f → ∀ p q : Pt X,
      ((diffSet p q).filter (fun i => Equinumerous (X := X) i m)).card
        ≤ ((diffSet (f p) (f q)).filter (fun i => Equinumerous (X := X) i m)).card := by
    intro f hf p q
    refine Finset.card_le_card_of_injOn
      (fun i => if hi : i ∈ diffSet p q then (image_step_adjacent f hf p q hi).choose else i)
      ?_ ?_
    · intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      simp only [Finset.mem_coe, Finset.mem_filter, dif_pos hi.1]
      have hspec := (image_step_adjacent f hf p q hi.1).choose_spec
      refine ⟨image_step_mem f hf p q hi.1 hspec, ?_⟩
      have heq := crossStable_equinumerous f hf p (stepAt p q i) i _
        ((differsInOne_iff_diffSet _ _ i).mpr (diffSet_stepAt_left hi.1)) hspec
      exact equinumerous_trans (equinumerous_symm heq) hi.2
    · intro i hi j hj hij
      rw [Finset.mem_coe, Finset.mem_filter] at hi hj
      simp only [dif_pos hi.1, dif_pos hj.1] at hij
      have e1 := image_step_eq f hf p q hi.1 (image_step_adjacent f hf p q hi.1).choose_spec
      have e2 := image_step_eq f hf p q hj.1 (image_step_adjacent f hf p q hj.1).choose_spec
      have : f (stepAt p q i) = f (stepAt p q j) := by rw [e1, e2, hij]
      exact stepAt_injOn p q i hi.1 j hj.1 (f.injective this)
  refine Nat.le_antisymm ?_ (key e he a b)
  have hback := key e.symm (crossStable_symm he) (e a) (e b)
  rwa [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hback

/-! ## Part 3: the classification, finiteness-free -/

/-- **THE ORBIT PARTITION IS THE EQUINUMEROSITY-TYPED COUNT, over ANY product carrier**, finite or not. Both
inclusions, no `Fintype` anywhere in the statement or in either proof. -/
theorem orbit_partition_is_eqTypedCount (a b a' b' : Pt X) :
    SameOrbit a b a' b' ↔ ∀ m, eqTypedCount a b m = eqTypedCount a' b' m := by
  constructor
  · rintro ⟨e, he, rfl, rfl⟩ m
    exact (eqTypedCount_crossStable_invariant e he a b m).symm
  · exact sameOrbit_of_same_eqTypedCount a b a' b'

/-- Every structural label is a coarsening of the equinumerosity-typed count, and the count is itself
structural, so it is the finest rung. Finiteness-free. -/
theorem eqTypedCount_is_finest_structural {Q : Type} (lab : Pt X → Pt X → Q)
    (hstruct : ∀ (e : Pt X ≃ Pt X), CrossStable e → ∀ p q, lab (e p) (e q) = lab p q)
    (a b a' b' : Pt X) (h : ∀ m, eqTypedCount a b m = eqTypedCount a' b' m) :
    lab a b = lab a' b' := by
  obtain ⟨e, he, rfl, rfl⟩ := (orbit_partition_is_eqTypedCount a b a' b').mpr h
  exact (hstruct e he a b).symm

/-! ## THE VERDICTS

PART 1: the equinumerosity-typed count is defined without finiteness, and the finite count is its special case.

`Equinumerous` groups coordinates by the existence of a bijection between their fibres, not by a cardinal.
`equinumerous_refl`, `_symm`, `_trans` make it an equivalence with no finiteness anywhere.
`eqTypedCount` counts, for each coordinate type, how many differing coordinates share it. THE COUNTING IS OVER
COORDINATES, which are finite because the arity is; nothing counts values, which is where the old definition
needed `Fintype`.

`eqTypedCount_eq_typedCount_of_finite` shows the reduction: with finite fibres, equinumerosity is equality of
cardinality, so the two objects coincide. The finite typed count is a reading of this one, not a rival.

PART 2: THE LIFT WORKS, and the step that looked like it needed finiteness had a replacement.

THE INVARIANCE MECHANISM, which was the doubtful half. The finite proof read the fibre SIZE off the graph by
COUNTING a line, and that count is irreducibly finite. The replacement reads the same line as a SET and
transports it, which yields a BIJECTION where the old proof yielded an equal number. `lineSet` characterizes
the line graph-theoretically, `lineSet_eq` identifies it with the coordinate line by `common_neighbours`, which
is a pointwise equivalence and carries no finiteness, `lineEquiv` identifies the line with the fibre minus one
point, `mem_lineSet_map` transports it along a cross-stable bijection, and `equiv_of_punctured` puts the removed
point back on each side. `crossStable_equinumerous` is the result: a cross-stable bijection relates two
coordinates only if their fibres are EQUINUMEROUS, proved with no finiteness at all.

THE TRANSITIVITY, which was the easy half and stayed easy. `swapT` takes a bijection between two fibres as a
parameter and never mentions cardinality; the finite proof manufactured that bijection with
`Fintype.equivOfCardEq`, and here it comes straight from the equinumerosity hypothesis.
`eqTypedCount_swapT` and `sameOrbit_of_same_eqTypedCount` follow the finite argument line for line.

THE ASSEMBLY. `image_step_adjacent`, `image_step_mem` and `image_step_eq` carry the local mechanism to a whole
cell: each differing coordinate sends its first step across, the image is a first step of the image cell, and
the correspondence is injective. `eqTypedCount_crossStable_invariant` concludes, by injecting both ways rather
than exhibiting a bijection, that every cross-stable bijection preserves every equinumerosity-typed count at
arbitrary distance.

NO STEP GENUINELY NEEDED FINITENESS. The one that appeared to, the link count, needed only that a line be
transported, and a set transports as well as a number counts.

A NOTE ON THE AUDIT, since a false lift was the thing to watch. Several results carry `Classical.choice`. In
every case it extracts a bijection that the hypothesis ASSERTS to exist, or decides a proposition for a filter
over the coordinate index. Nowhere does it manufacture a bijection out of finite structure, which is what
`Fintype.equivOfCardEq` did in the finite proof and what a false lift would have hidden. The distinction is
visible in the statements: no theorem below mentions `Fintype` except the one that names it to compare.

PART 3: THE PRESENTATION CHOICE DISSOLVES.

`orbit_partition_is_eqTypedCount` is both inclusions over ANY product carrier, with no `Fintype` in the
statement or in either proof. So there is ONE object, and it is at once

  GENERAL, since it needs no finiteness and so covers every carrier the framework admits;
  CONCRETE, since it says exactly what the rungs are, namely differing coordinates grouped by fibre type; and
  REDUCIBLE, since on finite fibres it IS the cardinal typed count.

The abstract and concrete forms were not two readings of one fact; they were one fact and a finiteness-bound
approximation of it. The choice was an artefact of stating the concrete form with cardinals.

PART 4: the resolved structure clause.

THE STRUCTURE CLAUSE SHOULD SAY: the invariant readings of the cross are exactly the coarsenings of the
EQUINUMEROSITY-TYPED DIFFERING COUNT. That is concrete and carries no finiteness hypothesis, so it replaces
both candidates rather than choosing between them. `eqTypedCount_is_finest_structural` is the tower statement:
every structural label is a coarsening of it and it is itself structural, so it is the finest rung.

The cardinal typed count keeps a place as the finite reading, cited by
`eqTypedCount_eq_typedCount_of_finite`, and the reachability form remains available as the definition of the
orbit partition. Neither is primary any more; both are corollaries.

GRADUATION SHELF. The classification group graduates as before, at `Model/NaryAssemblage`, with this file
replacing the cardinal-typed clause: the equinumerosity vocabulary and `eqTypedCount` first, then the lifted
mechanism, then the two inclusions, then the finite reduction as a corollary. The one dependency worth noting
is that `eqTypedCount` is `noncomputable` because its filter is classically decided; canonical `nary` is
already noncomputable, so this adds nothing new to the module.

VOCABULARY NOTE FOR THE SPEC, NOT FOR ANY THEOREM NAME. Equinumerosity classes of coordinates are the alphabet
TYPES; the equinumerosity-typed count is the class scheme of a product of Hamming schemes grouped by alphabet
type rather than alphabet size, which is the infinite-friendly form of the same object. Those names belong in a
spec entry citing the known setting, and nothing above is claimed as new relative to them.

WHAT REMAINS OPEN

1. The coordinate index is `Fin n`, so the ARITY is still finite. Only the fibres were lifted. An infinite
   arity would change the differing set from a `Finset` to something else and is not considered.
2. Nothing here is graduated; this readies the graduable form.
-/

#print axioms diffSet
#print axioms mem_diffSet
#print axioms differsInOne_iff_diffSet
#print axioms Adjacent
#print axioms not_adjacent_self
#print axioms CrossStable
#print axioms crossStable_iff_adjacent
#print axioms common_neighbours
#print axioms Equinumerous
#print axioms equinumerous_refl
#print axioms equinumerous_symm
#print axioms equinumerous_trans
#print axioms eqTypedCount
#print axioms eqTypedCount_eq_typedCount_of_finite
#print axioms lineSet
#print axioms lineSet_eq
#print axioms lineEquiv
#print axioms mem_lineSet_map
#print axioms eqSubtypeEquivUnit
#print axioms equiv_of_punctured
#print axioms crossStable_equinumerous
#print axioms exists_differsInOne_iff_card
#print axioms crossStable_of_diffSet_perm
#print axioms SameOrbit
#print axioms crossStable_trans
#print axioms sameOrbit_trans
#print axioms exists_equiv_pair
#print axioms movePair
#print axioms movePair_spec_ne
#print axioms movePair_spec_eq
#print axioms fibEquiv
#print axioms diffSet_fibEquiv
#print axioms fibEquiv_crossStable
#print axioms sameOrbit_of_same_diffSet
#print axioms swapT
#print axioms swapT_i
#print axioms swapT_j
#print axioms swapT_other
#print axioms swapT_involutive
#print axioms coordSwapT
#print axioms mem_diffSet_swapT
#print axioms diffSet_swapT
#print axioms coordSwapT_crossStable
#print axioms sdiff_after_swapT
#print axioms eqTypedCount_swapT
#print axioms sameOrbit_of_same_eqTypedCount_aux
#print axioms sameOrbit_of_same_eqTypedCount
#print axioms diffSet_eq_empty_iff
#print axioms diffSet_subset_union
#print axioms Steps
#print axioms steps_of_diffSet
#print axioms card_le_of_steps
#print axioms crossStable_symm
#print axioms steps_transport
#print axioms crossStable_preserves_diffCard
#print axioms stepAt
#print axioms diffSet_stepAt_left
#print axioms diffSet_stepAt_right
#print axioms stepAt_injOn
#print axioms image_step_adjacent
#print axioms image_step_mem
#print axioms image_step_eq
#print axioms eqTypedCount_crossStable_invariant
#print axioms orbit_partition_is_eqTypedCount
#print axioms eqTypedCount_is_finest_structural

end Chiralogy.EquinumerosityCount
