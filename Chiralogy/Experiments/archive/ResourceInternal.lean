import Chiralogy

/-! # Experiment: internalize the resource lattice (does the kernel see cost?)

External grading was decoration each prior time because the parameter was not carrier content. Here the
resource lattice is internalized: an object is a family indexed by resource level (a presheaf over `(L, ⪯)`),
so cost is the object's shape, not an annotation. This is the only option meeting the context-index condition.

The kernel needs only a fixed-point-free `g : B → B` and `f : X → X → B`. The decisive question is whether the
level index does work in the hole (cost visible, per-level) or is selected-and-discarded (scale-freeness
reasserts, uniform across levels). The test is the same discriminator as every prior discard: grep the proof
term for whether `r` is used essentially or only to pick the instance.

Uses `L := ℕ` with `≤` as the resource ordering and the explicit family formulation (lighter than presheaf
machinery; the question is about the hole, not the packaging). Stays in `Experiments/`; canonical untouched;
nothing about P vs NP resolved. -/

open Chiralogy

namespace Chiralogy.ResourceInternal

/-! ## Part 1: the resource-indexed base, minimally -/

/-- A resource-indexed object: a carrier and distinction space per level, a classification at each level, and
restriction maps on the distinction space (functor laws omitted, irrelevant to the hole). -/
structure ResObj where
  X : ℕ → Type
  B : ℕ → Type
  classify : ∀ r, X r → X r → B r
  restB : ∀ {r₁ r₂ : ℕ}, r₁ ≤ r₂ → B r₁ → B r₂

/-! ## Part 2: the kernel transports levelwise -/

/-- **The hole at each level.** At every resource level `r`, given a fixed-point-free endomap on that level's
distinction space, the classification is non-surjective. This is `no_reflexive_object` at level `r`, a genuine
instance: the levelwise cartesian-closed structure is all it needs. -/
theorem hole_at_each_level (O : ResObj) (g : ∀ r, O.B r → O.B r)
    (hg : ∀ r, ∀ b, g r b ≠ b) (r : ℕ) : ¬ Function.Surjective (O.classify r) :=
  no_reflexive_object (hg r) (O.classify r)

/-! ## Part 3: the decisive question, per-level or uniform -/

/-- **The hole is uniform across levels.** The obstruction at every level is the one diagonal lemma; the level
index selects which instance and then does no work. The hole holds at all levels the same way. -/
theorem hole_is_uniform_across_levels (O : ResObj) (g : ∀ r, O.B r → O.B r)
    (hg : ∀ r, ∀ b, g r b ≠ b) : ∀ r, ¬ Function.Surjective (O.classify r) :=
  fun r => no_reflexive_object (hg r) (O.classify r)

/-- **The index is selected-and-discarded.** A resource object constant across levels (the level changes
nothing) has, at every level, exactly the base object's hole, proved by the un-indexed lemma. Remove the
index and the obstruction is unchanged: `r` is pure selection, as context and grade were. -/
theorem constant_family_hole {X B : Type} (c : X → X → B) {g : B → B} (hg : ∀ b, g b ≠ b) (r : ℕ) :
    ¬ Function.Surjective ((fun _ : ℕ => c) r) :=
  no_reflexive_object hg c

/-- **The holes do not compare levels.** Even when the fixed-point-free endomap differs by level, each level's
hole is proved from that level's endomap alone; no level's obstruction refers to another's. Two levels give a
conjunction of independent instances, not a relation that ranks levels: the level-varying endomap does not
make the obstruction discriminate. -/
theorem holes_do_not_compare_levels (O : ResObj) (g : ∀ r, O.B r → O.B r)
    (hg : ∀ r, ∀ b, g r b ≠ b) (r₁ r₂ : ℕ) :
    (¬ Function.Surjective (O.classify r₁)) ∧ (¬ Function.Surjective (O.classify r₂)) :=
  ⟨no_reflexive_object (hg r₁) (O.classify r₁), no_reflexive_object (hg r₂) (O.classify r₂)⟩

/-! ## Part 4: do the restriction maps relate the holes? -/

/-- **The restriction maps do not relate the holes.** The hole at a higher level holds on its own, by that
level's endomap; the ordering `_h` and the restriction map `O.restB _h` are unused. The presheaf's structure
maps add no cross-level relation between obstructions: the picture is pointwise, one level up, as transport
was. -/
theorem restrictions_do_not_relate_holes (O : ResObj) (g : ∀ r, O.B r → O.B r)
    (hg : ∀ r, ∀ b, g r b ≠ b) {r₁ r₂ : ℕ} (_h : r₁ ≤ r₂) :
    ¬ Function.Surjective (O.classify r₂) :=
  no_reflexive_object (hg r₂) (O.classify r₂)

/-! ## The verdict: the sixth discard

Part 2: the kernel transports levelwise, a genuine `no_reflexive_object` at each level. Part 3: the level
index is selected-and-discarded. The obstruction is the one diagonal lemma at every level
(`hole_is_uniform_across_levels`); a constant family has the un-indexed hole with the index literally dropped
(`constant_family_hole`); and even a level-varying endomap yields independent instances, never a comparison
(`holes_do_not_compare_levels`). Per-level fails: the index does no work. Part 4: the restriction maps are
unused in the obstruction (`restrictions_do_not_relate_holes`), so the holes are independent across levels,
the pointwise picture one level up.

Internalizing the resource lattice does not make cost visible to the kernel. The hole is uniform across levels
even when the lattice is the object's shape rather than an annotation: the framework's scale-freeness survives
internalization, the sixth discard in its strongest form. Nothing here is about P vs NP; this tests whether
cost is expressible to the hole, and it is not. -/

end Chiralogy.ResourceInternal
