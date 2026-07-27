import Chiralogy.Model.AssemblageRelations

/-! ARCHIVED (fully graduated, across two modules). The structure of variance, packaged.

  Model/NaryAssemblage: e -> importMap, kernel_clause -> importMap_kernel, CrossSupported,
    e_injective_on_crossSupported -> importMap_injective_on_crossSupported,
    e_is_a_meet_embedding -> importMap_is_a_meet_embedding,
    singles_out_emptiness_refuses_content -> importMap_singles_out_emptiness (spec 9.18)
  Model/AssemblageRelations: structure_of_variance (spec 9.20), swap_transport and its section (spec 9.21)

The clause names did not multiply: `split_clause` IS `absence_carried_downward_closed`, and `order_clause`,
`meet_clause`, `bottom_clause`, `bottom_unique_clause`, `maxima_clause` ARE the `ImportSpace` results graduated
in the NaryAssemblage pass, cited rather than restated. The swap went in under its own section variables, which
is the fix for the two-regime hazard that produced a sorryAx here during the dry run. Typechecks standalone. -/

/-! # Experiment (LIVE): the structure of variance, packaged

`ImportSpace` proved the free region carries the classification space's own order-theoretic shape, but as a
CONJUNCTION narrated across six theorems. The readiness pass filed that as STAYS-LIVE: a reading, not a
statement. This packages it into one carrier-general object.

Consolidation only. Every clause reuses an `ImportSpace` result restated as a property of the map `e`; the
proofs are the same proofs. Live experiment, no canonical edit, nothing graduated. -/

open Chiralogy

set_option linter.unusedSectionVars false

namespace Chiralogy.VarianceStructure


/-! ### GRADUATED (Model/AssemblageRelations pass, with one half in the NaryAssemblage pass)

The package graduated under mechanism names, and the graph split it across two modules exactly as the readiness
pass predicted:

  Model/NaryAssemblage (needs nothing from the absence shelf)
    e ................................... importMap
    kernel_clause ....................... importMap_kernel
    CrossSupported ...................... same name
    e_injective_on_crossSupported ....... importMap_injective_on_crossSupported
    e_is_a_meet_embedding ............... importMap_is_a_meet_embedding
    singles_out_emptiness_refuses_content  importMap_singles_out_emptiness

  Model/AssemblageRelations (needs presentCarried)
    split_clause ........................ IS `absence_carried_downward_closed`, one name not two
    structure_of_variance ............... same name
    swap_transport and its section ...... same names, `Q` renamed `TwoCoord`, `rel` is canonical `relabel`

CONSOLIDATED: `order_clause`, `meet_clause`, `bottom_clause`, `bottom_unique_clause` and `maxima_clause` did
not graduate as separate names; they ARE canonical `import_order_embeds`, `nary_meet`, `import_bottom`,
`bottom_is_unique` and `maxima_are_plural`, graduated from `ImportSpace` in the NaryAssemblage pass, and the
bundles cite them directly.

The swap half went in under its own section variables, which is the fix for the hazard that produced a
`sorryAx` here during the dry run. -/

section General

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

abbrev Cls (X : Fin n → Type) := (∀ i, X i) → (∀ i, X i) → Option Bool

/-- A cross cell: a pair no factor reads. -/
def IsCross (a b : ∀ i, X i) : Prop := ¬ ∃ i, differsInOne a b i

theorem diagAt (a : ∀ i, X i) : IsCross a a := by
  rintro ⟨i, hne, _⟩; exact hne rfl

/-- **THE MAP.** With the factors held fixed, the assembly construction read as a map from the import space to
the classification space. This is the object the whole file is about: variance as a MAP, never a point. -/
noncomputable def e (c : ∀ i, X i → X i → Option Bool) (imp : Cls X) : Cls X := nary c imp

/-! ## Part 1: e as a single structured object -/

theorem order_clause (c : ∀ i, X i → X i → Option Bool) (imp imp' : Cls X) :
    cLE (e c imp) (e c imp') ↔ ∀ a b, IsCross a b → optLE (imp a b) (imp' a b) := by
  simp only [e]
  constructor
  · intro h a b hc
    have hcell := h a b
    rwa [nary_apply_imp c imp hc, nary_apply_imp c imp' hc] at hcell
  · intro h a b
    by_cases hex : ∃ i, differsInOne a b i
    · rw [nary_apply_differ c imp hex.choose_spec, nary_apply_differ c imp' hex.choose_spec]
      exact optLE_refl _
    · rw [nary_apply_imp c imp hex, nary_apply_imp c imp' hex]
      exact h a b hex

theorem optMeet_self (a : Option Bool) : optMeet a a = a := by
  cases a with
  | none => rfl
  | some x => simp [optMeet]

theorem meet_clause (c : ∀ i, X i → X i → Option Bool) (imp imp' : Cls X) :
    e c (cMeet imp imp') = cMeet (e c imp) (e c imp') := by
  simp only [e]
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · rw [nary_apply_differ c (cMeet imp imp') hex.choose_spec]
    show _ = optMeet (nary c imp a b) (nary c imp' a b)
    rw [nary_apply_differ c imp hex.choose_spec, nary_apply_differ c imp' hex.choose_spec,
      optMeet_self]
  · rw [nary_apply_imp c (cMeet imp imp') hex]
    show cMeet imp imp' a b = optMeet (nary c imp a b) (nary c imp' a b)
    rw [nary_apply_imp c imp hex, nary_apply_imp c imp' hex]
    rfl

/-- **The kernel of e, exactly.** Two imports have the same image precisely when they agree on the cross
region. This is the honest form of faithfulness: e is NOT injective on raw imports, because imports differing
only on region cells are overwritten by the factors. The narrative phrase "faithful copy" means injective
modulo cross-agreement, and that is what this states. -/
theorem kernel_clause (c : ∀ i, X i → X i → Option Bool) (imp imp' : Cls X) :
    e c imp = e c imp' ↔ ∀ a b, IsCross a b → imp a b = imp' a b := by
  simp only [e]
  constructor
  · intro h a b hc
    have hcell := congrFun (congrFun h a) b
    rwa [nary_apply_imp c imp hc, nary_apply_imp c imp' hc] at hcell
  · intro h
    funext a b
    by_cases hex : ∃ i, differsInOne a b i
    · rw [nary_apply_differ c imp hex.choose_spec, nary_apply_differ c imp' hex.choose_spec]
    · rw [nary_apply_imp c imp hex, nary_apply_imp c imp' hex]
      exact h a b hex

/-- The domain on which e is literally injective: imports supported on the cross region, the canonical
representatives of the kernel classes. -/
def CrossSupported (imp : Cls X) : Prop := ∀ a b, ¬ IsCross a b → imp a b = none

/-- **FAITHFUL, literally.** On cross-supported representatives e is injective, at any carrier. -/
theorem e_injective_on_crossSupported (c : ∀ i, X i → X i → Option Bool) (imp imp' : Cls X)
    (h : CrossSupported imp) (h' : CrossSupported imp') (heq : e c imp = e c imp') : imp = imp' := by
  funext a b
  by_cases hc : IsCross a b
  · exact (kernel_clause c imp imp').1 heq a b hc
  · rw [h a b hc, h' a b hc]

/-- **PART 1, ONE STATEMENT.** e is a meet-embedding of the import order into the classification order, with
its kernel identified exactly: the order is transmitted both ways, meets are preserved on the nose, and two
imports collide precisely when they agree on the cross region. Carrier-general: arbitrary `n`, arbitrary fibre
types, no finiteness and no inhabitation used. -/
theorem e_is_a_meet_embedding (c : ∀ i, X i → X i → Option Bool) :
    (∀ imp imp' : Cls X, cLE (e c imp) (e c imp') ↔ ∀ a b, IsCross a b → optLE (imp a b) (imp' a b))
      ∧ (∀ imp imp' : Cls X, e c (cMeet imp imp') = cMeet (e c imp) (e c imp'))
      ∧ (∀ imp imp' : Cls X, e c imp = e c imp' ↔ ∀ a b, IsCross a b → imp a b = imp' a b)
      ∧ (∀ imp imp' : Cls X, CrossSupported imp → CrossSupported imp' → e c imp = e c imp' → imp = imp') :=
  ⟨order_clause c, meet_clause c, kernel_clause c, e_injective_on_crossSupported c⟩

/-! ## Part 2: the sub-structure carried along e -/

theorem bottom_clause (c : ∀ i, X i → X i → Option Bool) (imp : Cls X) :
    cLE (e c (botC (∀ i, X i))) (e c imp) :=
  (order_clause c _ imp).2 (fun _ _ _ => Or.inl rfl)

/-- The bottom is the empty import and nothing else: anything at or below it supplies nothing on the whole
cross region. Emptiness, distinguished. -/
theorem bottom_unique_clause (c : ∀ i, X i → X i → Option Bool) (imp : Cls X)
    (h : cLE (e c imp) (e c (botC (∀ i, X i)))) : ∀ a b, IsCross a b → imp a b = none := by
  intro a b hc
  rcases (order_clause c imp _).1 h a b hc with h1 | h1
  · exact h1
  · exact h1

/-- **Plural maxima.** Two total imports give incomparable images, so the image branches. This is the ONE clause
needing `Inhabited`, to name a cross cell at which to separate them. -/
theorem maxima_clause [∀ i, Inhabited (X i)] (c : ∀ i, X i → X i → Option Bool) :
    ¬ cLE (e c cTrue) (e c cFalse) ∧ ¬ cLE (e c cFalse) (e c cTrue) := by
  have hd : IsCross (fun i => (default : X i)) (fun i => (default : X i)) := diagAt _
  constructor
  · intro h
    rcases (order_clause c cTrue cFalse).1 h _ _ hd with h1 | h1
    · exact absurd h1 (by simp [cTrue])
    · exact absurd h1 (by simp [cTrue, cFalse])
  · intro h
    rcases (order_clause c cFalse cTrue).1 h _ _ hd with h1 | h1
    · exact absurd h1 (by simp [cFalse])
    · exact absurd h1 (by simp [cTrue, cFalse])

theorem presentCarried_mono {Y : Type} {A B : Y → Y → Option Bool} (h : cLE A B) {x x' : Y}
    (hp : presentCarried A x x') : presentCarried B x x' := by
  obtain ⟨z, b, b', h1, h2, hb⟩ := hp
  refine ⟨z, b, b', ?_, ?_, hb⟩
  · rcases h x z with hc | hc
    · exact absurd hc (by rw [h1]; exact Option.some_ne_none b)
    · rw [← hc, h1]
  · rcases h x' z with hc | hc
    · exact absurd hc (by rw [h2]; exact Option.some_ne_none b')
    · rw [← hc, h2]

/-- **The present and absence split, carried down.** At any fixed pair of image points, the imports leaving the
distinction absence-carried form a downward-closed subset of the import order. The framework's central
distinction re-enters through e as an order-theoretic, not arbitrary, partition. -/
theorem split_clause (c : ∀ i, X i → X i → Option Bool) (a a' : ∀ i, X i) (imp imp' : Cls X)
    (hle : ∀ p q, IsCross p q → optLE (imp p q) (imp' p q))
    (h : ¬ presentCarried (e c imp') a a') : ¬ presentCarried (e c imp) a a' :=
  fun hp => h (presentCarried_mono ((order_clause c imp imp').2 hle) hp)

/-- **PART 2, ONE STATEMENT.** The image of e carries a bottom, that bottom uniquely, plural incomparable
maxima, and a downward-closed present/absence split. Carrier-general; the generality MINIMUM over the clauses
is `Inhabited`, contributed by the maxima clause alone. -/
theorem e_carries_the_substructure [∀ i, Inhabited (X i)] (c : ∀ i, X i → X i → Option Bool) :
    (∀ imp : Cls X, cLE (e c (botC (∀ i, X i))) (e c imp))
      ∧ (∀ imp : Cls X, cLE (e c imp) (e c (botC (∀ i, X i))) → ∀ a b, IsCross a b → imp a b = none)
      ∧ (¬ cLE (e c cTrue) (e c cFalse) ∧ ¬ cLE (e c cFalse) (e c cTrue))
      ∧ (∀ (a a' : ∀ i, X i) (imp imp' : Cls X),
          (∀ p q, IsCross p q → optLE (imp p q) (imp' p q)) →
          ¬ presentCarried (e c imp') a a' → ¬ presentCarried (e c imp) a a') :=
  ⟨bottom_clause c, bottom_unique_clause c, maxima_clause c, split_clause c⟩

/-! ## Part 3: the single theorem, and the discipline check -/

/-- **THE STRUCTURE OF VARIANCE.** For fixed factors over an arbitrary finite product carrier, the import map
`e` is a meet-embedding with kernel exactly cross-agreement, injective on cross-supported representatives, whose
image carries the classification order's own shape: a bottom, that bottom alone, plural incomparable maxima, and
a downward-closed present/absence split.

Variance is not a second axis. It is the same structure re-entering one level in, and this is that reading as a
single carrier-general object. Generality minimum: `Inhabited` fibres, from the maxima clause. -/
theorem structure_of_variance [∀ i, Inhabited (X i)] (c : ∀ i, X i → X i → Option Bool) :
    ((∀ imp imp' : Cls X, cLE (e c imp) (e c imp') ↔ ∀ a b, IsCross a b → optLE (imp a b) (imp' a b))
      ∧ (∀ imp imp' : Cls X, e c (cMeet imp imp') = cMeet (e c imp) (e c imp'))
      ∧ (∀ imp imp' : Cls X, e c imp = e c imp' ↔ ∀ a b, IsCross a b → imp a b = imp' a b)
      ∧ (∀ imp imp' : Cls X, CrossSupported imp → CrossSupported imp' → e c imp = e c imp' → imp = imp'))
    ∧ ((∀ imp : Cls X, cLE (e c (botC (∀ i, X i))) (e c imp))
      ∧ (∀ imp : Cls X, cLE (e c imp) (e c (botC (∀ i, X i))) → ∀ a b, IsCross a b → imp a b = none)
      ∧ (¬ cLE (e c cTrue) (e c cFalse) ∧ ¬ cLE (e c cFalse) (e c cTrue))
      ∧ (∀ (a a' : ∀ i, X i) (imp imp' : Cls X),
          (∀ p q, IsCross p q → optLE (imp p q) (imp' p q)) →
          ¬ presentCarried (e c imp') a a' → ¬ presentCarried (e c imp) a a')) :=
  ⟨e_is_a_meet_embedding c, e_carries_the_substructure c⟩

/-- **THE DISCIPLINE CHECK.** The packaged theorem singles out emptiness and refuses to single out content: the
empty import is the least element, and there is NO greatest element at all. Packaging introduced no canonical
import, so the fold-probe error did not enter with the bundling. -/
theorem singles_out_emptiness_refuses_content [∀ i, Inhabited (X i)]
    (c : ∀ i, X i → X i → Option Bool) :
    (∀ imp : Cls X, cLE (e c (botC (∀ i, X i))) (e c imp))
      ∧ ¬ ∃ t : Cls X, ∀ imp : Cls X, cLE (e c imp) (e c t) := by
  refine ⟨bottom_clause c, ?_⟩
  rintro ⟨t, ht⟩
  have hd : IsCross (fun i => (default : X i)) (fun i => (default : X i)) := diagAt _
  have h1 := (order_clause c cTrue t).1 (ht cTrue) _ _ hd
  have h2 := (order_clause c cFalse t).1 (ht cFalse) _ _ hd
  rcases h1 with h1 | h1
  · exact absurd h1 (by simp [cTrue])
  rcases h2 with h2 | h2
  · exact absurd h2 (by simp [cFalse])
  have e1 : (some true : Option Bool) = t (fun i => (default : X i)) (fun i => (default : X i)) := h1
  have e2 : (some false : Option Bool) = t (fun i => (default : X i)) (fun i => (default : X i)) := h2
  exact absurd (e1.trans e2.symm) (by simp)

end General

/-! ## Part 3 continued: the one non-copy feature, and where it sits

The swap is `ImportSpace`'s single non-copy finding: a symmetry the free region has and the determined part
does not. It is stated on a homogeneous two-coordinate carrier and is NOT a clause of the packaged theorem, so
it does not lower the packaged generality. This section locates it. -/

section Swap

variable {Y : Type} [DecidableEq Y]

abbrev Q (Y : Type) := ∀ _ : Fin 2, Y

theorem fin2_ne : ∀ i j : Fin 2, j ≠ i ↔ j = i + 1 := by decide

theorem fin2_twice (i : Fin 2) : i + 1 + 1 = i := by revert i; decide

def swapP (a : Q Y) : Q Y := fun i => a (i + 1)

theorem swapP_involutive (a : Q Y) : swapP (swapP a) = a := by
  funext i
  show a (i + 1 + 1) = a i
  rw [fin2_twice]

theorem swapP_differsInOne (a b : Q Y) (i : Fin 2) :
    differsInOne (swapP a) (swapP b) i ↔ differsInOne a b (i + 1) := by
  constructor
  · rintro ⟨hne, hoth⟩
    refine ⟨hne, fun j hj => ?_⟩
    have hji : j = i := by rw [fin2_ne] at hj; rw [hj, fin2_twice]
    have hi : swapP a (i + 1) = swapP b (i + 1) := hoth (i + 1) (by rw [fin2_ne])
    rw [hji]
    show a i = b i
    have : a (i + 1 + 1) = b (i + 1 + 1) := hi
    rwa [fin2_twice] at this
  · rintro ⟨hne, hoth⟩
    refine ⟨hne, fun j hj => ?_⟩
    show a (j + 1) = b (j + 1)
    refine hoth (j + 1) ?_
    rw [fin2_ne] at hj ⊢
    rw [hj]

/-- The swap fixes the cross region setwise: it acts on the import space. -/
theorem swap_fixes_cross (a b : Q Y) : IsCross a b ↔ IsCross (swapP a) (swapP b) := by
  constructor
  · rintro h ⟨i, hd⟩
    exact h ⟨i + 1, (swapP_differsInOne a b i).1 hd⟩
  · rintro h ⟨i, hd⟩
    refine h ⟨i + 1, (swapP_differsInOne a b (i + 1)).2 ?_⟩
    rwa [fin2_twice]

def swapImp (imp : Q Y → Q Y → Option Bool) : Q Y → Q Y → Option Bool :=
  fun a b => imp (swapP a) (swapP b)

def swapFactors (c : ∀ _ : Fin 2, Y → Y → Option Bool) : ∀ _ : Fin 2, Y → Y → Option Bool :=
  fun i => c (i + 1)


/-- **WHERE THE SWAP SITS.** It is not a property of `e` at fixed factors. It passes through `e` only as a
transport law that SWAPS THE FACTORS: relabelling the image by the swap equals the image of the swapped import
under the swapped factors. So the swap relates e over `c` to e over `swapFactors c`; it is a statement about the
pair (free region, determined part), not structure inside the free part. -/
theorem swap_transport (c : ∀ _ : Fin 2, Y → Y → Option Bool) (imp : Q Y → Q Y → Option Bool) :
    relabel swapP (nary c imp) = nary (swapFactors c) (swapImp imp) := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · obtain ⟨i, hd⟩ := hex
    have hd' : differsInOne (swapP a) (swapP b) (i + 1) :=
      (swapP_differsInOne a b (i + 1)).2 (by rwa [fin2_twice])
    show nary c imp (swapP a) (swapP b) = nary (swapFactors c) (swapImp imp) a b
    rw [nary_apply_differ c imp hd', nary_apply_differ (swapFactors c) (swapImp imp) hd]
    show c (i + 1) (a (i + 1 + 1)) (b (i + 1 + 1)) = c (i + 1) (a i) (b i)
    rw [fin2_twice]
  · have hc' : IsCross (swapP a) (swapP b) := (swap_fixes_cross a b).1 hex
    show nary c imp (swapP a) (swapP b) = nary (swapFactors c) (swapImp imp) a b
    rw [nary_apply_imp c imp hc', nary_apply_imp (swapFactors c) (swapImp imp) hex]
    rfl

end Swap

def cAsym : ∀ _ : Fin 2, Fin 2 → Fin 2 → Option Bool :=
  fun i x _ => if i = 0 then (if x = 0 then some true else none) else none

/-- **And the transport genuinely moves.** For asymmetric factors the swapped family differs from the original,
so the transport law does not close at fixed factors: the swap is a symmetry of the free region that the
determined part does not share. -/
theorem swapFactors_can_differ : swapFactors cAsym ≠ cAsym := by decide

/-! ## THE VERDICTS

PART 1: e is a carrier-general injective meet-embedding, once "injective" is stated correctly.

`e_is_a_meet_embedding` is the single statement: the order transmits both ways (`order_clause`, an iff), meets
are preserved on the nose (`meet_clause`), the kernel is exactly cross-agreement (`kernel_clause`), and on
cross-supported representatives e is literally injective (`e_injective_on_crossSupported`). Arbitrary `n`,
arbitrary fibre types, no finiteness, no inhabitation.

ONE PRECISION THE NARRATIVE GLOSSED. e is NOT injective on raw imports. Imports differing only on region cells
have the same image, because the factors overwrite them there. `ImportSpace` knew this
(`cross_agree_same_composite`) but the phrase "faithful copy" did not carry it. The packaged statement carries
it two ways: the kernel is identified exactly, and injectivity is asserted on the canonical representatives.
That is what faithfulness means here, and stating it any more simply would be false.

PART 2: the sub-structure packages, with one generality mismatch, flagged.

`e_carries_the_substructure` bundles the bottom, its uniqueness, plural maxima, and the downward-closed
present/absence split. Per-clause generality:

  order, meet, kernel, injectivity, bottom, bottom-unique, split .... fully carrier-general, no side condition
  plural maxima ................................................... needs `[∀ i, Inhabited (X i)]`

The mismatch is real and is not papered over. The maxima clause must name a cross cell at which two total
imports disagree, and on an empty carrier there is no such cell. THE PACKAGED THEOREM'S GENERALITY IS THE
MINIMUM OVER ITS CLAUSES, so `structure_of_variance` carries `Inhabited` and says so. Seven of eight clauses
would hold without it.

Nothing regressed to `Fin`-bound. The one `Fin 2` result in this file, the swap, is deliberately not a clause.

PART 3: the single theorem, the discipline check, and the swap's location.

`structure_of_variance` is the object: for fixed factors over an arbitrary finite product carrier, e is a
meet-embedding with kernel exactly cross-agreement, injective on cross-supported representatives, whose image
carries a bottom, that bottom alone, plural incomparable maxima, and a downward-closed present/absence split.

DISCIPLINE CHECK, PASSED, and it strengthened under packaging.
`singles_out_emptiness_refuses_content` proves not merely that the maxima are plural but that THERE IS NO
GREATEST ELEMENT AT ALL: any candidate top would have to agree with both the all-true and the all-false import
at a cross cell. So the packaged theorem distinguishes exactly one point, the empty import, and proves no
content-bearing import can be distinguished by the order. Packaging introduced no canonical import. No fold-probe
failure.

THE NON-COPY FEATURE SITS OUTSIDE e, and `swap_transport` says precisely where. Relabelling the image by the
swap equals the image of the swapped import under the SWAPPED FACTORS. So the swap does not act on e at fixed
factors; it relates e over `c` to e over `swapFactors c`, and `swapFactors_can_differ` shows those are genuinely
different families. The swap is a statement about the pair (free region, determined part), not structure inside
the free region, which is why it does not package and should not.

PART 4: the graph places it HIGHER than its pieces, and that is the surprise.

`lake exe depgraph-preview VarianceStructure`, hook-sets extracted per declaration (canonical targets reached
through this file's own lemmas):

  e ................................ Model/NaryAssemblage: nary
  e_is_a_meet_embedding ............ Model/NaryAssemblage: nary, differsInOne, nary_apply_differ,
                                       nary_apply_imp
                                     Model/InformationOrder: cLE, cMeet, optLE, optLE_refl, optMeet
  e_carries_the_substructure ....... the above, plus Model/InformationOrder: botC, cTrue, cFalse
                                     plus Model/Apophatic: presentCarried
  singles_out_emptiness_refuses_content .. Model/NaryAssemblage and Model/InformationOrder only
  swap_transport ................... Model/NaryAssemblage only
  structure_of_variance ............ Model/InformationOrder 8 declarations / 34 references
                                     Model/NaryAssemblage 4 declarations / 15 references
                                     Model/Apophatic 1 declaration / 4 references

THE CONCENTRATION FLIPS, AND THE PLACEMENT MOVES, FOR DIFFERENT REASONS.

By weight the consolidated theorem is an INFORMATION-ORDER object, not an assemblage one: eight order
declarations against four assemblage ones. But weight does not place it. `Model/InformationOrder` is imported
BY `Model/NaryAssemblage`, so it is below and cannot host anything mentioning `nary`.

What moves the placement is the ONE hook the readiness pass did not have in view. The split clause reaches
`presentCarried` in `Model/Apophatic`, and `Model/NaryAssemblage` does not import that branch: `Apophatic` sits
on `Model/Moves`, `NaryAssemblage` on `Model/InformationOrder`. The lowest canonical module importing both is
`Model/AssemblageRelations`, by way of `NaryAssemblage` on one side and `AssemblageDynamics` to `Assemblage` to
`Grounds` to `Apophatic` on the other.

SO THE GRAPH SAYS: the packaged theorem does not fit where its pieces fit. Part 1 alone
(`e_is_a_meet_embedding`) hooks only `NaryAssemblage` and `InformationOrder` and would sit at
`Model/NaryAssemblage`, which is exactly where the readiness pass put the `ImportSpace` survivors. Bundling the
present/absence split onto it pulls the whole object up to `Model/AssemblageRelations`. That is a real cost of
consolidation and it is the thing to decide before any graduation: place the bundle at `AssemblageRelations`,
or split it and keep the order half low.

WHAT REMAINS OPEN

1. The split clause is at a FIXED pair of image points, inherited from `ImportSpace`. The intersection over all
   pairs is still unmeasured, so the packaged split is pointwise, not global.
2. `maxima_clause` uses two constant imports, so "plural maxima" means "at least two incomparable points", not
   an antichain characterization. Whether the image's maximal elements form an antichain is not proved.
3. The swap is stated on a homogeneous two-coordinate carrier. The general statement, for a permutation of
   coordinates on a carrier whose fibres are not all equal, would need the permutation to preserve the fibre
   types, and is not attempted here.
4. The placement fork above is not decided here. Nothing graduates in this file; it readies one object and
   locates it. -/

#print axioms diagAt
#print axioms order_clause
#print axioms optMeet_self
#print axioms meet_clause
#print axioms kernel_clause
#print axioms e_injective_on_crossSupported
#print axioms e_is_a_meet_embedding
#print axioms bottom_clause
#print axioms bottom_unique_clause
#print axioms maxima_clause
#print axioms presentCarried_mono
#print axioms split_clause
#print axioms e_carries_the_substructure
#print axioms structure_of_variance
#print axioms singles_out_emptiness_refuses_content
#print axioms fin2_ne
#print axioms fin2_twice
#print axioms swapP_involutive
#print axioms swapP_differsInOne
#print axioms swap_fixes_cross
#print axioms swap_transport
#print axioms swapFactors_can_differ

end Chiralogy.VarianceStructure
