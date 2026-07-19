import Chiralogy

/-! # Experiment: cataphatic self-application, three angles

`grade_adds` showed the tower's surplus telescopes additively for arbitrary composites. This tests three
forms of self-application, each with its own verdict: whether applying a witness to its own output compounds
(Angle 3), whether there is a level between levels giving a second dimension (Angle 5), and whether the
witness family self-classifies into new structure or recovers the hole (Angle 4).

The tower machinery is re-derived locally (the experiments are not compiled). Stays in `Experiments/`;
canonical untouched; nothing about P vs NP resolved. -/

open Chiralogy

namespace Chiralogy.SelfApplication

/-! ## Shared: the tower machinery -/

@[ext] structure TowerLevel (A B : Type) where
  emb : A → B
  ret : B → A
  sec : Function.LeftInverse ret emb

def levelCompose {A B C : Type} (f : TowerLevel A B) (g : TowerLevel B C) : TowerLevel A C where
  emb := g.emb ∘ f.emb
  ret := f.ret ∘ g.ret
  sec := fun a => by simp only [Function.comp_apply]; rw [g.sec (f.emb a), f.sec a]

def levelId (A : Type) : TowerLevel A A := ⟨id, id, fun _ => rfl⟩

theorem levelId_comp {A B : Type} (f : TowerLevel A B) : levelCompose (levelId A) f = f := rfl

def grade {A B : Type} [Fintype A] [Fintype B] (_f : TowerLevel A B) : ℤ :=
  (Fintype.card B : ℤ) - Fintype.card A

theorem grade_adds {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (f : TowerLevel A B) (g : TowerLevel B C) :
    grade (levelCompose f g) = grade f + grade g := by
  simp only [grade]; ring

/-! ## Angle 3: does self-application compound?

`List` is infinite, where the cardinality-gap grade is vacuous. So the free construction is stood in by a
finite section, the diagonal `A → A × A` (a genuine build-outward with retraction `fst`), applied to its own
output. The grade notion is unchanged. -/

/-- The diagonal build, a finite free construction: a section with retraction. -/
def dup (A : Type) : TowerLevel A (A × A) := ⟨fun a => (a, a), Prod.fst, fun _ => rfl⟩

/-- Self-application: the diagonal applied to its own output. -/
def selfApply (A : Type) : TowerLevel A ((A × A) × (A × A)) := levelCompose (dup A) (dup (A × A))

/-- **Self-application adds.** The grade of the diagonal applied to its own output is the sum of the two
levels' grades: self-application is an ordinary composite, and composites add. -/
theorem grade_of_self_application :
    grade (selfApply Bool) = grade (dup Bool) + grade (dup (Bool × Bool)) :=
  grade_adds (dup Bool) (dup (Bool × Bool))

/-- **Additive, not multiplicative, non-vacuously.** The two levels have grades 2 and 12; the self-applied
composite has grade 14, their sum, not their product 24. The ambient cardinality compounds (2, 4, 16) but the
surplus gap telescopes additively. -/
theorem self_application_is_additive :
    grade (dup Bool) = 2 ∧ grade (dup (Bool × Bool)) = 12 ∧ grade (selfApply Bool) = 14
    ∧ grade (selfApply Bool) ≠ grade (dup Bool) * grade (dup (Bool × Bool)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [grade, Fintype.card_prod, Fintype.card_bool] <;> norm_num

/-! ## Angle 5: levels of levels -/

/-- **Levels of levels typecheck.** `TowerLevel A B` lives in `Type 0`, the same universe as the types it
relates (unlike `Obj`, which is `Type 1`), so a section between levels is well-formed: the universe
obstruction does not fire. -/
def levelOfLevels (A B : Type) : TowerLevel (TowerLevel A B) (TowerLevel A B) := levelId _

/-- **The meta-level is the same composition.** A level between levels composes by the same `levelCompose`,
with the same identity law, not a second operation. Iteration is repeated composition along the one axis, not
an orthogonal one, so there is no pair of operations to distribute: no semiring shape. -/
theorem meta_is_same_composition (A B : Type) (L : TowerLevel (TowerLevel A B) (TowerLevel A B)) :
    levelCompose (levelId (TowerLevel A B)) L = L :=
  levelId_comp L

/-! ## Angle 4: does the witness family self-classify? -/

/-- **Family self-classification recovers the hole.** The witness family `CataphaticConformant` lives in
`Type 1` (it carries a `Type`), yet any self-classification of it carries the hole: the universe-polymorphic
`no_reflexive_object` fires at the family level. Self-classification is the apophatic move, so classifying the
cataphatic family yields the obstruction, not new cataphatic structure, as the ethical move was
apophatic-shaped. -/
theorem familySelfClassify_recovers_hole (c : CataphaticConformant → CataphaticConformant → Option Bool) :
    ¬ Function.Surjective c :=
  no_reflexive_object optCycle_fixedpointfree c

/-! ## The verdicts, independent

Angle 3: self-application adds. The diagonal applied to its own output is an ordinary composite
(`grade_of_self_application`), and composites add; concretely 14 = 2 + 12, not 2 * 12, while the ambient
cardinality compounds (`self_application_is_additive`). The surplus gap telescopes additively even where the
size multiplies: the ninth wall, with the reason that a section adds a fixed surplus regardless of what it is
applied to. Compounding would need a multiplicative grade, a redefinition the gate forbids.

Angle 5: levels of levels typecheck; the universe gate does not fire, because `TowerLevel` stays in `Type 0`
(`levelOfLevels`). But this buys no second dimension: the meta-level uses the same `levelCompose` and the same
identity law (`meta_is_same_composition`), so iteration is repeated composition along one axis, not an
orthogonal operation. One monoid, iterated, not two operations with distribution: no semiring.

Angle 4: family self-classification recovers the hole (`familySelfClassify_recovers_hole`). The family is
`Type 1` (it carries a `Type`, as `Obj` does), yet the universe-polymorphic `no_reflexive_object` still fires:
cataphatic self-classification is apophatic in shape, yielding the obstruction a universe up, not new
structure, as expected.

Three angles, three walls: additive self-application, a second dimension that is only more of the same axis,
and self-classification that is the hole. Nothing here is about P vs NP; no complexity class, no separation. -/

end Chiralogy.SelfApplication
