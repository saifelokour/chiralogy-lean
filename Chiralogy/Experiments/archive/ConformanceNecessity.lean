import Chiralogy

/-! # Experiment (ARCHIVED, GRADUATED): does conformance require the hole or the floor?

GRADUATED. `member_requires_a_kernel_condition` and `no_total_self_description_of_the_object_condition`
landed in `Protocol/Membership` (they depend on `Member`); `no_total_internal_self_description` and
`no_self_description_equiv` landed in `Kernel/Apophatic` beside `no_reflexive_object` / `empty_center`
(the diagonal they instantiate). Placement followed the dependency graph, not intuition: the Member
instance was pulled up to the protocol by its `Member` dependency (the kernel cannot import the protocol),
splitting the self-description trio 2 (kernel) + 1 (protocol). This archived record is namespaced
`ConformanceNecessityRecord` so its decls do not collide with the canonical homes; it typechecks
standalone against canonical. Original investigation preserved intact below.

The cohesion inquiry found, as a graph property of `depgraph-proof.json`, that the framework coheres at two
forced kernel conditions: the hole (impossibility of self-total-classification) and non-degeneracy (the object
floor), reported as mutually redundant. The statability check found the application side is expressible as a
Lean proposition while self-description is not. This file attempts the theorem-level necessity question for the
application side, and computes all three outcomes rather than aiming at one.

## The real definitions (read before stating)

`CataphaticConformant` (`Model/Cataphatic.lean`) is
```
structure CataphaticConformant where
  X : Type
  T : Type
  build : X → T
```
It has NO `classify : X → X → B`, only a one-place `build : X → T`, and `cataphatic_is_loose` proves everything
conforms (`⟨X, X, id⟩`). So the target as the prompt writes it, `CataphaticConformant X → hole ∨ NonDegenerate
X.classify`, is not even STATABLE against it: there is no classification field to be non-surjective or
non-degenerate, and `NonDegenerate` is a two-place predicate (`X → X → B`) that does not typecheck on a one-place
`build`. This is a second, subtler dissolution than "a witness satisfies neither": the loose form has nothing for
the conditions to attach to. `Member` (`Protocol/Membership.lean`) is the genuine discriminating predicate: five
data including `classify : X → X → B` and a `nondegenerate` field, with `payload` proving the hole.

## The three outcomes, computed

1. `CataphaticConformant`, read through the natural one-place analogue on `build` (build is surjective / build
   distinguishes two inputs): REFUTED. The witness `⟨Unit, Unit, id⟩` conforms, and its `build` is surjective
   (no hole) and distinguishes no two inputs (no floor). Conformance to the cataphatic form forces NEITHER
   condition. The graph cohesion is structural-only for this predicate.
2. `Member`, the genuine application predicate: PROVES, and CONJUNCTIVELY, stronger than the predicted
   disjunction. Every member satisfies the hole (`payload`) AND the floor (the `nondegenerate` field, which is
   `NonDegenerate M.classify` by `Iff.rfl`). The two conditions are both entailed, from two distinct sources (a
   proved theorem and a structural field), not one-or-the-other.

So the graph's disjunctive middle prediction ("requires at least one") is realized by NEITHER predicate: the
loose form requires neither, the strict form requires both. Non-degeneracy and the hole are not consequences
that conformance-in-general forces; they are absent from the cataphatic form and built into `Member` (the field
and the `canDiffer`-driven payload). Mutual redundancy at the connectivity level corresponds, at the content
level, to two conditions that live together in `Member` by construction and are simply absent elsewhere.

## The boundary

`member_requires_both` proves that the CONTENT of membership entails both conditions (the same within-language
idiom as `payload` itself), not the unprovable "every conceivable proof routes through them." It is a theorem
about what the predicate `Member` contains, not a claim about all formalizations.

## Self-description (a reading, not a theorem)

The dual question, does self-description require the conditions, is NOT posable as a Lean theorem. Self-description
is a meta-family: `ChiasmType : Absence → Prop` (`Model/Boundary.lean`) is a case-split describing the kernel's
own shape, and the chiasm theorems (`double_chiasm_conjunction`, `two_inversions_share_center`, `model_arms_invert`)
are meta-statements ABOUT that shape, not instances of a single predicate over objects. There is no `SD X : Prop`
to quantify, so there is no necessity theorem to state; its content already IS the hole (`KernelChiasmStmt` is two
non-surjectivities) and the floor never appears in it. This asymmetry is the theorem-level shadow of the two-spine
split: application is INTERNAL to the framework's language (a predicate one can prove things of), while
self-description is META (a family describing the system from outside), arguably an echo of the empty center, a
system's account of its own shape being meta to the system. Reading only; no theorem is claimed here. -/

namespace ConformanceNecessityRecord
open Chiralogy

/-- **Cataphatic conformance forces neither condition.** `CataphaticConformant` carries no `classify`; read
through the natural one-place analogue on its `build`, the loose form is refuted: `⟨Unit, Unit, id⟩` conforms,
its build is surjective (no hole) and distinguishes no two inputs (no floor). Conformance to the cataphatic
form is content-empty as to the two kernel conditions. -/
theorem cataphatic_forces_neither :
    ∃ cc : CataphaticConformant,
      Function.Surjective cc.build ∧ ¬ ∃ x x', cc.build x ≠ cc.build x' := by
  refine ⟨⟨Unit, Unit, id⟩, fun y => ⟨y, rfl⟩, ?_⟩
  rintro ⟨x, x', h⟩
  exact h (Subsingleton.elim x x')

/-- **Membership requires BOTH conditions.** For the genuine application predicate `Member`, conformance
entails the hole (the classification is not surjective, `payload`) AND the floor (`NonDegenerate M.classify`,
which is the `nondegenerate` field by `Iff.rfl`). Stronger than the graph's disjunctive prediction: the two
conditions are jointly entailed, from a proved theorem and a structural field respectively. Within-language
entailment (the content of `Member` requires them), not a claim about all proofs. -/
theorem member_requires_both (M : Member) :
    ¬ Function.Surjective M.classify ∧ NonDegenerate M.classify :=
  ⟨payload M, M.nondegenerate⟩

/-- The disjunctive form the graph predicted is a weakening of `member_requires_both`, recorded for the exact
comparison to the prediction: it holds, but only because the conjunction does. -/
theorem member_requires_a_condition (M : Member) :
    ¬ Function.Surjective M.classify ∨ NonDegenerate M.classify :=
  Or.inl (member_requires_both M).1

#print axioms cataphatic_forces_neither
#print axioms member_requires_both
#print axioms member_requires_a_condition

/-! ## Closing the loop: no total internal self-description, by the hole

The companion reading held that self-description is meta because a TOTAL INTERNAL self-description would be the
reflexive self-classification `no_reflexive_object` / `center_is_empty` forbids. Here that reading is discharged
into a theorem, stated against the real machinery.

What is "the framework's own carrier", and what is its "space of descriptions"? Read against the source, a
description of a carrier `D` is a Boolean classification of it, an element of the classifier space `D → Bool`
(the source names `D → Bool` the "classifier space" at `empty_center` / `center_is_empty`). A self-classification
`desc : D → D → Bool` is, curried, a `D`-indexed family of such descriptions: each `d` gives the row `desc d :
D → Bool`, its view of the whole. A TOTAL internal self-description is such a `desc` that is SURJECTIVE onto the
description space: every possible description is realized as some element's view. That is exactly the reflexive
surjection `no_reflexive_object` rules out (`Bool` carries the fixed-point-free `not`). So "total internal
self-description" IS statable as a reflexive-surjection proposition, and its impossibility IS the founding hole.

One honesty point on "the framework's OWN carrier": the framework is carrier-neutral (register-neutral, a flat
rhizome with no distinguished object), so there is no single Lean type that is "the framework's carrier". This is
not an obstruction, it sharpens the result: the diagonal holds for EVERY carrier `D`, so a fortiori for any the
framework would use to host its own descriptions. Below, `no_total_internal_self_description` is the uniform form
(every carrier), and `no_total_self_description_of_the_object_condition` instantiates it at `Member`, the
framework's own object condition, making the self-application vivid: the same diagonal, at the type of the
framework's own conformant objects. -/

/-- **No total internal self-description (uniform).** For any descriptive carrier `D`, no self-classification
`desc : D → D → Bool` is surjective onto the description space `D → Bool`: no `D`-indexed family of Boolean
descriptions realizes every description. This IS `no_reflexive_object` (the diagonal, `fixedPoint_of_surjection`)
read as self-description: `Bool` carries the fixed-point-free `not`. -/
theorem no_total_internal_self_description {D : Type u} (desc : D → D → Bool) :
    ¬ Function.Surjective desc :=
  no_reflexive_object (g := fun b => !b) (by decide) desc

/-- **The equivalence form.** No carrier is equivalent to its own description space `D → Bool`: the reflexive
equivalence a total self-description would need does not exist. The content of `center_is_empty`, here derived
from the surjection form (an equivalence would give a surjective self-description). -/
theorem no_self_description_equiv {D : Type u} : ¬ Nonempty (D ≃ (D → Bool)) := by
  rintro ⟨e⟩
  exact no_total_internal_self_description (fun a => e a) e.surjective

/-- **The self-application, at the framework's own object condition.** No total internal self-description of the
framework's own objects: no `desc : Member → Member → Bool` is surjective onto `Member → Bool`. The framework's
founding theorem (`no_reflexive_object`, the empty center) applied to `Member`, the very predicate by which the
framework's application is internal. The framework proves the hole governs itself. -/
theorem no_total_self_description_of_the_object_condition (desc : Member → Member → Bool) :
    ¬ Function.Surjective desc :=
  no_reflexive_object (g := fun b => !b) (by decide) desc

#print axioms no_total_internal_self_description
#print axioms no_self_description_equiv
#print axioms no_total_self_description_of_the_object_condition

end ConformanceNecessityRecord
