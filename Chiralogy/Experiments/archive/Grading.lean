import Chiralogy

/-! # Experiment: does the cataphatic tower carry a grading?

An M-graded category over a pomonoid `(M, ≤, 1, ·)` with monotone `·` has morphisms carrying grades that
compose multiplicatively: `grade (f ∘ g) = grade f · grade g`. The distinction that matters: an order gives
levels (ordinal); a monoid with `·` gives magnitudes that compose multiplicatively (cardinal), which is what
blowup requires. Additive counting is an order, not a magnitude.

The tower composes, but there is no composition operator on levels, only specific composites. This build
supplies one, then asks whether a grade read off the level multiplies under composition (cardinal, blowup
expressible), only adds (ordinal, an order), or fails to cohere.

Stays in `Experiments/`; canonical untouched; nothing about P vs NP resolved. -/

open Chiralogy

namespace Chiralogy.Grading

/-! ## Part 1: the composition operator and its laws -/

/-- A tower level: a section with a retraction between two ambients (generalizing `embed`/`restrict`). -/
@[ext] structure TowerLevel (A B : Type) where
  emb : A → B
  ret : B → A
  sec : Function.LeftInverse ret emb

/-- Composition of levels: sections compose, retractions compose in reverse, and the retraction law is
preserved. Sections-with-retractions compose to a section-with-retraction, as an operation. -/
def levelCompose {A B C : Type} (f : TowerLevel A B) (g : TowerLevel B C) : TowerLevel A C where
  emb := g.emb ∘ f.emb
  ret := f.ret ∘ g.ret
  sec := fun a => by simp only [Function.comp_apply]; rw [g.sec (f.emb a), f.sec a]

/-- The identity level: the trivial embedding. -/
def levelId (A : Type) : TowerLevel A A := ⟨id, id, fun _ => rfl⟩

/-- **Composition is associative.** -/
theorem levelCompose_assoc {A B C D : Type}
    (f : TowerLevel A B) (g : TowerLevel B C) (h : TowerLevel C D) :
    levelCompose (levelCompose f g) h = levelCompose f (levelCompose g h) := rfl

/-- **The identity is a left unit.** -/
theorem levelId_comp {A B : Type} (f : TowerLevel A B) : levelCompose (levelId A) f = f := rfl

/-- **The identity is a right unit.** So levels form a category (a monoid on a fixed ambient): there is a
carrier for a grade to attach to. -/
theorem comp_levelId {A B : Type} (f : TowerLevel A B) : levelCompose f (levelId B) = f := rfl

/-! ## Part 2: is there a grade, and does it multiply? -/

/-- The grade read off a level: the surplus size, the cardinality gap the free move opens. Computed from the
level's ambients, not stipulated. -/
def grade {A B : Type} [Fintype A] [Fintype B] (_f : TowerLevel A B) : ℤ :=
  (Fintype.card B : ℤ) - Fintype.card A

/-- **The grade adds.** Under composition the surplus sizes sum: the cardinality gaps telescope. This is the
additive monoid `(ℤ, +, 0)`, an ordinal index. -/
theorem grade_adds {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (f : TowerLevel A B) (g : TowerLevel B C) :
    grade (levelCompose f g) = grade f + grade g := by
  simp only [grade]; ring

/-- **The grade does not multiply.** Two levels of grade one compose to grade two, not one: composition adds
the surplus, it does not multiply a magnitude. The grade is a function of the level and it is additive. -/
theorem grade_does_not_multiply :
    ∃ (f : TowerLevel Unit Bool) (g : TowerLevel Bool (Fin 3)),
      grade (levelCompose f g) ≠ grade f * grade g := by
  refine ⟨⟨fun _ => true, fun _ => (), fun _ => Subsingleton.elim _ _⟩,
          ⟨fun b => if b then 1 else 0, fun x => decide (x = 1), by decide⟩, ?_⟩
  simp only [grade, Fintype.card_fin, Fintype.card_unit, Fintype.card_bool]
  decide

/-! ## Part 3: the bound adds, it does not compound -/

/-- **A grade bound adds.** Composing two levels each within grade `m` stays within `m + m`, the additive
bound. Exponential blowup is multiplicative (`m * m`), so an additive bound counts surplus linearly and does
not express it. This is where a multiplicative grade would have made a bound compound. -/
theorem grade_bound_is_additive {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (f : TowerLevel A B) (g : TowerLevel B C) (m : ℤ)
    (hf : grade f ≤ m) (hg : grade g ≤ m) : grade (levelCompose f g) ≤ m + m := by
  rw [grade_adds]; exact add_le_add hf hg

/-! ## The verdict: additive only, ordinal

Part 1: levels compose as an operation with laws, associative (`levelCompose_assoc`) and unital
(`levelId_comp`, `comp_levelId`), so there is a carrier for a grade, a category of levels. Part 2: the grade
read off a level is its surplus size (the cardinality gap), a function of the level, not stipulated. It adds
under composition (`grade_adds`) and does not multiply (`grade_does_not_multiply`): the surplus sizes
telescope additively. Part 3: a grade bound therefore adds (`grade_bound_is_additive`), `m + m`, not `m * m`.

The cataphatic tower carries an ordinal grade, not a magnitude. It orders by accumulated surplus but does not
compute a product, so blowup, which is multiplicative, is not expressible. This is the eighth appearance of
the same wall, now with the reason on the term: composition of sections adds surplus (the added points sum,
the cardinality gaps telescope), it does not multiply. Dressing the additive grade as multiplicative by
exponentiation would carry the same ordinal information, not a computed magnitude. Nothing here is about P vs
NP; no complexity class is defined and no separation is claimed. -/

end Chiralogy.Grading
