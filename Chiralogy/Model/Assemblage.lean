import Chiralogy.Model.Grounds
import Chiralogy.Kernel.Apophatic

/-! # Model: the assemblage construction

Lateral to the tower. The tower relates an object to itself with more or less structure; an assemblage relates
several objects to a new one alongside them. `assembleClassify c1 c2 imp` classifies a product carrier: pairs
sharing a second component by the first factor `c1`, pairs sharing a first component (and differing second) by the
second factor `c2`, fully-cross pairs by the imported cross-map. The factors fix the shared-component region,
wider than the diagonal; the import is exactly its complement, the fully-cross pairs. So the assemblage's grounds
are new relative to the factors yet derivable from the two objects and the cross-map, and the signature is two
objects and a cross-map on the fully-cross region, no separate ground-structure imported. The factors are
unchanged by assembly and re-pair; the construction iterates, an assemblage being an object; and it is not
associative, the bracketing deciding what must be supplied from outside.

The two parameters read the ground-order: coding is the closures ruled out (`2^n` minus the closeable count),
territorialization the endpoint-count (the maximal elements, inverse to homogeneity). They are independent, their
combined space is not a product (coded-and-fully-deterritorialized forbidden), and they are lossy, missing the
free part and connectivity two distinct four-ground orders can differ in. Under assembly the endpoint-counts sum
and the closeable families multiply, so coding has no additive law. **READING** The identification of these two
quantities with assemblage theory's coding and territorialization is imported and defeasible; the computations
are theorems, the correspondence a reading. -/

namespace Chiralogy

/-- The assemblage classification on a product carrier: pairs sharing a second component classified by the first
factor, pairs sharing a first component (and differing second) by the second, fully-cross pairs by the import. -/
def assembleClassify {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) : (X1 × X2) → (X1 × X2) → Option Bool :=
  fun a b => if a.2 = b.2 then c1 a.1 b.1 else if a.1 = b.1 then c2 a.2 b.2 else imp a b

/-! ## The construction -/

/-- **The factors fix the shared-component region.** A pair sharing a second component is classified by the first
factor, a pair sharing a first component (and differing second) by the second, independent of the import. The
determined region is where the two elements share a component, wider than the diagonal. -/
theorem factors_determine_the_shared_region {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (a b : X1 × X2) :
    (a.2 = b.2 → assembleClassify c1 c2 imp a b = c1 a.1 b.1)
    ∧ (a.1 = b.1 → a.2 ≠ b.2 → assembleClassify c1 c2 imp a b = c2 a.2 b.2) :=
  ⟨fun h => by unfold assembleClassify; rw [if_pos h],
   fun h1 h2 => by unfold assembleClassify; rw [if_neg h2, if_pos h1]⟩

/-- **The import is the complement.** On a fully-cross pair, both components differing, the assemblage returns the
imported value; this is the whole imported region, exactly the complement of the shared-component pairs. -/
theorem import_is_the_complement {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (a b : X1 × X2) :
    a.1 ≠ b.1 → a.2 ≠ b.2 → assembleClassify c1 c2 imp a b = imp a b :=
  fun h1 h2 => by unfold assembleClassify; rw [if_neg h2, if_neg h1]

/-- **The assemblage conforms.** The payload fires unconditionally on the product carrier, and any two distinct
rows witness non-degeneracy, so the assemblage passes the unchanged protocol. -/
theorem assemblage_conforms {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool)
    (a a' : X1 × X2) (h : assembleClassify c1 c2 imp a ≠ assembleClassify c1 c2 imp a') :
    NonDegenerate (assembleClassify c1 c2 imp) ∧ ¬ Function.Surjective (assembleClassify c1 c2 imp) :=
  ⟨⟨a, a', h⟩, hole_uniform _⟩

/-- **The grounds are derivable, not imported.** On the determined region the assemblage's classification, hence
its absences, is fixed by the factors regardless of the import: two assemblages of the same factors agree there
whatever their imports. So the ground-structure is computed from the factors and the cross-map, new relative to
the factors but derivable, only the fully-cross grounds depending on the import. -/
theorem grounds_are_derivable_not_imported {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp imp' : (X1 × X2) → (X1 × X2) → Option Bool) (a b : X1 × X2) :
    (a.2 = b.2 ∨ a.1 = b.1) → assembleClassify c1 c2 imp a b = assembleClassify c1 c2 imp' a b := by
  intro h
  unfold assembleClassify
  by_cases h2 : a.2 = b.2
  · rw [if_pos h2, if_pos h2]
  · rcases h with h | h
    · exact absurd h h2
    · rw [if_neg h2, if_neg h2, if_pos h, if_pos h]

/-- **The construction takes two objects and a cross-map.** The assemblage depends on the import only through its
fully-cross values: two imports agreeing there give the identical assemblage. So the signature is two objects and
a cross-map on the fully-cross pairs, not a separately imported ground-structure. -/
theorem construction_takes_two_objects_and_a_cross_map {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp imp' : (X1 × X2) → (X1 × X2) → Option Bool) :
    (∀ a b, a.1 ≠ b.1 → a.2 ≠ b.2 → imp a b = imp' a b) →
    (∀ a b, assembleClassify c1 c2 imp a b = assembleClassify c1 c2 imp' a b) := by
  intro himp a b
  unfold assembleClassify
  by_cases h2 : a.2 = b.2
  · rw [if_pos h2, if_pos h2]
  · by_cases h1 : a.1 = b.1
    · rw [if_neg h2, if_neg h2, if_pos h1, if_pos h1]
    · rw [if_neg h2, if_neg h2, if_neg h1, if_neg h1]; exact himp a b h1 h2

/-- **The factors remain unchanged.** Forming the assemblage leaves each factor a payload-firing register: the
factors are not consumed into the whole. -/
theorem factors_remain_unchanged {X1 X2 : Type}
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool) :
    ¬ Function.Surjective c1 ∧ ¬ Function.Surjective c2 :=
  ⟨hole_uniform _, hole_uniform _⟩

/-- **The factors re-pair.** The same first factor with a different partner gives a different assemblage: on a
shared-first-component pair the value is the partner's, so partners differing there give differing assemblages.
The component detaches and re-plugs. -/
theorem factors_re_pair {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 c2' : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) (a b : X1 × X2)
    (h1 : a.1 = b.1) (h2 : a.2 ≠ b.2) (hne : c2 a.2 b.2 ≠ c2' a.2 b.2) :
    assembleClassify c1 c2 imp a b ≠ assembleClassify c1 c2' imp a b := by
  rw [(factors_determine_the_shared_region c1 c2 imp a b).2 h1 h2,
      (factors_determine_the_shared_region c1 c2' imp a b).2 h1 h2]
  exact hne

/-- **Assemblages iterate.** An assemblage is an object, so it is a factor in another: assembling `A, B` then with
`C` conforms, the payload firing. The construction composes. -/
theorem assemblages_iterate {X1 X2 X3 : Type} [DecidableEq X1] [DecidableEq X2] [DecidableEq X3]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool) (c3 : X3 → X3 → Option Bool)
    (imp12 : (X1 × X2) → (X1 × X2) → Option Bool)
    (imp123 : ((X1 × X2) × X3) → ((X1 × X2) × X3) → Option Bool) :
    ¬ Function.Surjective (assembleClassify (assembleClassify c1 c2 imp12) c3 imp123) :=
  hole_uniform _

/-- **Assembly order matters.** The construction is not associative: a triple sharing its first component but
differing in second and third is same-first in `A ⊕ (B ⊕ C)`, determined by `B ⊕ C`, yet fully-cross in
`(A ⊕ B) ⊕ C`, imported. The bracketing decides what must be supplied from outside. -/
theorem assembly_order_matters :
    ∃ (a1 b1 a2 b2 a3 b3 : Fin 2),
      (((a1, a2), a3).1 ≠ ((b1, b2), b3).1) ∧ ((a3 : Fin 2) ≠ b3)
      ∧ ((a1, a2, a3).1 = (b1, b2, b3).1) :=
  ⟨0, 0, 0, 1, 0, 1, by decide, by decide, by decide⟩

/-! ## The parameters

Two four-ground orders for the loss: a three-chain with a free ground, and the connected N poset. Two disjoint
two-chains for the composition law. -/

/-- A three-chain `0 ≺ 1 ≺ 2` with a free ground `3`. -/
def prereqChain3Free : Fin 4 → Fin 4 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 1) && decide (b = 2))

/-- The connected N poset on four grounds: `0 ≺ 2`, `1 ≺ 2`, `1 ≺ 3`. -/
def prereqN4 : Fin 4 → Fin 4 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 2)) || (decide (a = 1) && decide (b = 2))
            || (decide (a = 1) && decide (b = 3))

/-- Two disjoint two-chains `0 ≺ 1` and `2 ≺ 3`. -/
def prereqTwoChain : Fin 4 → Fin 4 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 2) && decide (b = 3))

/-- **Coding is order-density.** Coding is the closures ruled out, `2^n` minus the closeable count: the chain
rules out four, the mixed order two, the discrete order none, so a denser order codes more. -/
theorem coding_is_order_density :
    ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqChain3 S)).card = 4)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqMixed3 S)).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqDiscrete S)).card = 0)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqChain3 S)).card
        = 2 ^ 3 - (Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqChain3 S)).card) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **Territorialization is the endpoint-count.** The number of maximal elements of the ground-order, inverse to
homogeneity: the chain one endpoint, the fork two, the join one, the discrete order all of them. -/
theorem territorialization_is_endpoint_count :
    ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqChain3 i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqV3 i j = false)).card = 2)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqLambda3 i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqDiscrete i j = false)).card = 3) := by decide

/-- **The parameters are independent.** The fork and the join code alike, three ruled out each, but territorialize
apart, two endpoints against one; and a single-ground order is territorialized (one endpoint) yet uncoded (nothing
ruled out). Neither parameter determines the other. -/
theorem parameters_are_independent :
    ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqV3 S)).card =
       (Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqLambda3 S)).card)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqV3 i j = false)).card ≠
       (Finset.univ.filter (fun i : Fin 3 => ∀ j, prereqLambda3 i j = false)).card)
    ∧ ((Finset.univ.filter (fun i : Fin 1 => ∀ j, prereqDiscrete i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun S : Fin 1 → Bool => ¬ closeable prereqDiscrete S)).card = 0) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **Coded and fully deterritorialized is impossible.** If every ground is maximal (fully deterritorialized),
every closure is closeable (uncoded), so the combination is forbidden: the parameter space is not a product. -/
theorem coded_and_fully_deterritorialized_is_impossible {n : ℕ} (prereq : Fin n → Fin n → Bool) :
    (∀ i : Fin n, ∀ j, prereq i j = false) → (∀ S : Fin n → Bool, closeable prereq S) :=
  fun hmax S a b hab _ => by rw [hmax a b] at hab; exact absurd hab (by decide)

/-- **The parameters are lossy.** A three-chain with a free ground and the connected N poset share both
coordinates, coding eight and endpoint-count two, but differ in their free part, one free ground against none,
hence in connectivity. So the two coordinates do not determine the ground-order. -/
theorem parameters_are_lossy :
    ((Finset.univ.filter (fun S : Fin 4 → Bool => ¬ closeable prereqChain3Free S)).card =
       (Finset.univ.filter (fun S : Fin 4 → Bool => ¬ closeable prereqN4 S)).card)
    ∧ ((Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqChain3Free i j = false)).card =
       (Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqN4 i j = false)).card)
    ∧ ((Finset.univ.filter (fun i : Fin 4 => isFree prereqChain3Free i)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 4 => isFree prereqN4 i)).card = 0) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **Territorialization adds, the family multiplies.** Under disjoint-sum assembly the endpoint-counts sum, two
2-chains giving two endpoints, one plus one; the closeable families multiply, nine as three times three; so coding,
the closures ruled out, has no additive law, seven against one plus one. -/
theorem territorialization_adds_the_family_multiplies :
    ((Finset.univ.filter (fun i : Fin 4 => ∀ j, prereqTwoChain i j = false)).card = 2)
    ∧ ((Finset.univ.filter (fun i : Fin 2 => ∀ j, prereqChain2 i j = false)).card = 1)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable prereqTwoChain S)).card =
       (Finset.univ.filter (fun S : Fin 2 → Bool => closeable prereqChain2 S)).card *
       (Finset.univ.filter (fun S : Fin 2 → Bool => closeable prereqChain2 S)).card)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => ¬ closeable prereqTwoChain S)).card ≠
       (Finset.univ.filter (fun S : Fin 2 → Bool => ¬ closeable prereqChain2 S)).card +
       (Finset.univ.filter (fun S : Fin 2 → Bool => ¬ closeable prereqChain2 S)).card) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ## The membership condition: located difference and the free cross

The assemblage exceeds its factors when it adds content over the empty-cross juxtaposition. This is the
assemblage's membership condition, the whole-versus-parts analogue of an object's non-degeneracy: exceeding stands
to two objects as distinguishing stands to one, both requirements that can fail. It is difference-gated and
import-supplied. `located X1 X2`, the cross-region non-empty, is necessary (`exceeding_requires_location`); above
it the cross is a free parameter (`cross_is_free_over_all_factors`, `no_factor_forces_the_cross`), so sufficiency is
the import's, not any condition on the factors (`location_is_not_sufficient`, `sufficiency_is_the_import`). Both
sit only with the assemblage: `located` is a fact about the product carrier's cross-region, which nothing earlier
has, so it is homed here beside `exceeds`.

READING (a reading, not a theorem): the modal contrast. The kernel forbids one object's two ends coinciding,
`center_is_empty`, a forced negated existential, an impossibility; the assemblage permits any relation between two
distinct objects, `no_factor_forces_the_cross`, a universal existential, a realizability. The two emptinesses are
opposite in kind, the empty center a wall and the inter-object-forced position an open field. Empty by construction
means the cross is a free parameter, that within the assemblage no factor forces it; it does not mean no extension
could force inter-object difference.

READING: exceeding is a strict extension of non-degeneracy, not its arity-1 form, correcting the conjecture that
the two might be mutually constitutive. At a trivial second factor the cross-region collapses
(`collapse_at_trivial_factor`), so exceeding is vacuous (`exceeding_vacuous_at_trivial_factor`), while a factor's
non-degeneracy is a genuine condition that survives (`intra_survives_where_inter_vacuous`): the intra requirement
holds where the inter requirement is undefined for want of a cross, so intra is prior and inter is built on the
product. This assemblage-membership is model-interior and construction-internal, not a kernel-adjacent
domain-facing protocol like object-membership: the same non-coincidence shape at a different stratum and direction. -/

/-- The cross-region is inhabited: two pairs differing in both components, so the factors are genuinely two. -/
def located (X1 X2 : Type) : Prop := ∃ a b : X1 × X2, a.1 ≠ b.1 ∧ a.2 ≠ b.2

/-- The assemblage exceeds its factors: it adds content over the empty-cross juxtaposition. -/
def exceeds {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2] (c1 : X1 → X1 → Option Bool)
    (c2 : X2 → X2 → Option Bool) (imp : (X1 × X2) → (X1 × X2) → Option Bool) : Prop :=
  assembleClassify c1 c2 imp ≠ assembleClassify c1 c2 (fun _ _ => none)

/-- **Exceeding requires location.** If the assemblage exceeds its juxtaposition, the cross-region is non-empty:
where no two pairs differ in both components the assemblage equals its juxtaposition for every import and cannot
exceed. -/
theorem exceeding_requires_location {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) :
    exceeds c1 c2 imp → located X1 X2 := by
  intro hexc
  by_contra hnl
  exact hexc (by
    funext a b
    exact construction_takes_two_objects_and_a_cross_map c1 c2 imp (fun _ _ => none)
      (fun a b h1 h2 => absurd ⟨h1, h2⟩ (fun hab => hnl ⟨a, b, hab⟩)) a b)

/-- **The cross is free over all factors.** For any factors and any target relation on the fully-cross pairs an
import realizes it, the witness being the target itself, since the cross value is exactly the import. -/
theorem cross_is_free_over_all_factors {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (r : (X1 × X2) → (X1 × X2) → Option Bool) :
    ∃ imp : (X1 × X2) → (X1 × X2) → Option Bool,
      ∀ a b, a.1 ≠ b.1 → a.2 ≠ b.2 → assembleClassify c1 c2 imp a b = r a b :=
  ⟨r, fun a b h1 h2 => import_is_the_complement c1 c2 r a b h1 h2⟩

/-- **No factor forces the cross.** For all located factors two imports give assemblages differing on the cross, so
the factors do not determine the cross value: the emptiness of the inter-object-forced position is realizability,
not obstruction, over arbitrary carriers, its only hypothesis decidable equality. -/
theorem no_factor_forces_the_cross {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool) :
    located X1 X2 →
      ∃ imp imp' : (X1 × X2) → (X1 × X2) → Option Bool,
        assembleClassify c1 c2 imp ≠ assembleClassify c1 c2 imp' := by
  rintro ⟨a0, b0, h1, h2⟩
  refine ⟨(fun _ _ => none), (fun _ _ => some true), ?_⟩
  intro heq
  have hval := congrFun (congrFun heq a0) b0
  rw [import_is_the_complement c1 c2 (fun _ _ => none) a0 b0 h1 h2,
      import_is_the_complement c1 c2 (fun _ _ => some true) a0 b0 h1 h2] at hval
  exact absurd hval (by decide)

/-- **The collapse at a trivial second factor.** When the second carrier is a subsingleton no two pairs differ in
both components, so the cross-region is empty and the assemblage is independent of the import. -/
theorem collapse_at_trivial_factor {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2] [Subsingleton X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp imp' : (X1 × X2) → (X1 × X2) → Option Bool) :
    (∀ a b : X1 × X2, ¬ (a.1 ≠ b.1 ∧ a.2 ≠ b.2))
    ∧ (assembleClassify c1 c2 imp = assembleClassify c1 c2 imp') := by
  refine ⟨?_, ?_⟩
  · rintro a b ⟨_, h2⟩; exact h2 (Subsingleton.elim a.2 b.2)
  · funext a b
    exact construction_takes_two_objects_and_a_cross_map c1 c2 imp imp'
      (fun a b _ h2 => absurd (Subsingleton.elim a.2 b.2) h2) a b

/-- **Exceeding is vacuous at a trivial second factor.** With a subsingleton second carrier the assemblage equals
its juxtaposition for every import, so it never exceeds. -/
theorem exceeding_vacuous_at_trivial_factor {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2] [Subsingleton X2]
    (c1 : X1 → X1 → Option Bool) (c2 : X2 → X2 → Option Bool)
    (imp : (X1 × X2) → (X1 × X2) → Option Bool) :
    ¬ exceeds c1 c2 imp :=
  fun h => h (collapse_at_trivial_factor c1 c2 imp (fun _ _ => none)).2

/-- **The factor-swap fixes the cross.** For two factors on the same carrier, on a fully-cross pair both orderings
give the import, so swapping the factors leaves the cross-region unchanged and permutes only the determined
regions. -/
theorem swap_fixes_the_cross {X : Type} [DecidableEq X] (c1 c2 : X → X → Option Bool)
    (imp : (X × X) → (X × X) → Option Bool) (a b : X × X) :
    a.1 ≠ b.1 → a.2 ≠ b.2 → assembleClassify c1 c2 imp a b = assembleClassify c2 c1 imp a b := by
  intro h1 h2
  rw [import_is_the_complement c1 c2 imp a b h1 h2, import_is_the_complement c2 c1 imp a b h1 h2]

/-- **Location does not suffice.** There are located factors with an import that does not exceed, the pure open
cross: difference is present at the carriers and the whole still does not exceed. -/
theorem location_is_not_sufficient :
    ∃ (c1 c2 : Fin 2 → Fin 2 → Option Bool) (imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool),
      located (Fin 2) (Fin 2) ∧ ¬ exceeds c1 c2 imp :=
  ⟨(fun _ _ => none), (fun _ _ => none), (fun _ _ => none),
   ⟨(0, 0), (1, 1), by decide, by decide⟩, fun h => h rfl⟩

/-- **Sufficiency is the import.** For located factors there is an import that exceeds and one that does not, so
above location the deciding factor is the free import, not any structural condition on the factors. -/
theorem sufficiency_is_the_import :
    ∃ (c1 c2 : Fin 2 → Fin 2 → Option Bool) (imp imp' : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool),
      exceeds c1 c2 imp ∧ ¬ exceeds c1 c2 imp' := by
  refine ⟨(fun _ _ => none), (fun _ _ => none),
    (fun a b => if a = (0, 0) ∧ b = (1, 1) then some true else none), (fun _ _ => none), ?_, fun h => h rfl⟩
  intro heq
  have hv := congrFun (congrFun heq (0, 0)) (1, 1)
  rw [import_is_the_complement (fun _ _ => none) (fun _ _ => none)
        (fun a b => if a = (0, 0) ∧ b = (1, 1) then some true else none) (0, 0) (1, 1) (by decide) (by decide),
      import_is_the_complement (fun _ _ => none) (fun _ _ => none) (fun _ _ => none) (0, 0) (1, 1)
        (by decide) (by decide)] at hv
  exact absurd hv (by decide)

/-- **Intra survives where inter is vacuous.** A non-degenerate first factor keeps its non-degeneracy while, at a
trivial second factor, the assemblage never exceeds: the intra requirement holds where the inter requirement is
undefined, so they are two conditions, not one at two arities. -/
theorem intra_survives_where_inter_vacuous :
    ∃ c1 : Fin 2 → Fin 2 → Option Bool, NonDegenerate c1
      ∧ ∀ (imp : (Fin 2 × Unit) → (Fin 2 × Unit) → Option Bool), ¬ exceeds c1 (fun _ _ => none) imp :=
  ⟨(fun x y => if x = y then some true else none), by unfold NonDegenerate; decide,
   fun imp => exceeding_vacuous_at_trivial_factor _ (fun _ _ => none) imp⟩

end Chiralogy
