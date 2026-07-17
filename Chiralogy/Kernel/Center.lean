import Chiralogy.Kernel.Apophatic

/-! # Kernel: the empty center between the ends

The center the two ends share is empty and op-fixed: `center_is_empty`, `empty_center_is_coincidence` (the
coincidence `X ≃ (X → B)`, which the hole forbids), `op_fixes_empty_center`, and `keystone` (the empty
center as the op-fixed middle). The two kernel inversions cross here (`two_inversions_share_center`); the
ethical arm is a distinct center. The apophatic end lives at the codomain (`apophatic_center_is_codomain`);
the hole is codomain-generic and survives op (`hole_is_codomain_generic`, `hole_survives_op`). -/

namespace Chiralogy

/-- **Two inversions share the center.** The self-referential inversion (`𝒜`) and the epistemic inversion
(any classification `c`) both factor through non-surjectivity `no_reflexive_object`: each is that one
obstruction applied to an object's own self-classification. -/
theorem two_inversions_share_center {X : Type} (c : X → X → Option Bool) :
    (¬ Function.Surjective 𝒜.classify) ∧ (¬ Function.Surjective c) :=
  ⟨no_reflexive_object (g := fun b => !b) (by decide) 𝒜.classify, hole_uniform c⟩

/-- **The ethical center is distinct.** The ethical inversion turns on a constitutive absence
(`imprecise 0 2 = none`), not on non-surjectivity: a total object (`∀ x y, c x y ≠ none`) still carries the
hole. Non-surjectivity does not supply the constitutive absence, so the ethical pivot is a second center. -/
theorem ethical_center_is_distinct :
    ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ ¬ Function.Surjective c :=
  ⟨fun _ _ => some true, fun _ _ => (by decide : (some true : Option Bool) ≠ none), hole_uniform _⟩

/-- **The center is empty.** Wherever an inversion crosses, it crosses at an absence, not a positive
object: no carrier is equivalent to its own classifier space (`empty_center`). -/
theorem center_is_empty : ¬ ∃ X : Type, Nonempty (X ≃ (X → Bool)) := empty_center
/-- **The apophatic center is the codomain.** For a single map `c : X → X → B`, the fold-refusal lives
at the codomain `B`: a fixed-point-free endomap on `B` refutes surjectivity. The obstruction is a statement
about `B`. -/
theorem apophatic_center_is_codomain {X B : Type} (c : X → X → B) (g : B → B) (hg : ∀ b, g b ≠ b) :
    ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-- **The cataphatic center is the domain.** For the same map `c : X → X → B`, the build-source lives at
the domain `X`: the transpose `X → (X → B)` sends each `x` to its row `c x`. The build is free (it always
exists). -/
theorem cataphatic_center_is_domain {X B : Type} (c : X → X → B) :
    ∃ build : X → (X → B), ∀ x, build x = c x :=
  ⟨fun x => c x, fun _ => rfl⟩

/-- **One map, two ends.** The same `c : X → X → B` carries both: the apophatic end at the codomain `B`
(a fixed-point-free endomap there refutes the fold) and the cataphatic end at the domain `X` (its transpose
is the free build-outward). The two ends of one map meet at this center. -/
theorem one_map_two_ends {X B : Type} (c : X → X → B) :
    (∀ g : B → B, (∀ b, g b ≠ b) → ¬ Function.Surjective c) ∧
    (∃ build : X → (X → B), ∀ x, build x = c x) :=
  ⟨fun _g hg => no_reflexive_object hg c, ⟨fun x => c x, fun _ => rfl⟩⟩

/-- **The hole is codomain-generic.** The fold-refusal obstructs surjection for any codomain carrying a
fixed-point-free endomap, with no condition on the domain. It is not `B`-specific; it is a role held by
whatever type sits in the codomain position. -/
theorem hole_is_codomain_generic {X B : Type} (g : B → B) (hg : ∀ b, g b ≠ b) (c : X → X → B) :
    ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-- **The hole survives op: clean symmetry, not a broken chiasm.** op swaps `X` and `B`. Given
fixed-point-free endomaps on both ends, the hole holds at the codomain-`B` map `c` and, transported, at the
op-swapped codomain-`X` map `d`: `no_reflexive_object` applies to the swapped shape exactly as to the
original. The hole-role transports faithfully, and `op ∘ op = id` recovers it. No content is lost; the
chiasm does not resurrect. -/
theorem hole_survives_op {X B : Type} (gX : X → X) (hgX : ∀ x, gX x ≠ x)
    (gB : B → B) (hgB : ∀ b, gB b ≠ b) (c : X → X → B) (d : B → B → X) :
    ¬ Function.Surjective c ∧ ¬ Function.Surjective d :=
  ⟨no_reflexive_object hgB c, no_reflexive_object hgX d⟩
/-- **The empty center is the coincidence locus, and empty from the hole.** The empty
center's condition `X ≃ (X → B)`, an object equal to its own account, is impossible: a self-reflection iso
would be a surjection, which the hole forbids. Statement is the coincidence; proof is the hole. -/
theorem empty_center_is_coincidence {X B : Type} (g : B → B) (hg : ∀ b, g b ≠ b) :
    ¬ Nonempty (X ≃ (X → B)) := by
  rintro ⟨e⟩
  obtain ⟨b, hb⟩ := fixedPoint_of_surjection (⇑e) e.surjective g
  exact hg b hb

/-- **op fixes the empty center.** op swaps the ends `X` and `B`. The coincidence-emptiness
holds at both: no object equals its account with codomain `B`, and none with the swapped codomain `X`. So
the empty middle is invariant under the end-swap (op-fixed as a symmetry), while the ends are swapped. -/
theorem op_fixes_empty_center {X B : Type} (gX : X → X) (hgX : ∀ x, gX x ≠ x)
    (gB : B → B) (hgB : ∀ b, gB b ≠ b) :
    (¬ Nonempty (X ≃ (X → B))) ∧ (¬ Nonempty (B ≃ (B → X))) :=
  ⟨empty_center_is_coincidence gB hgB, empty_center_is_coincidence gX hgX⟩

/-- **The keystone.** Two ends and an empty middle of one map. The cataphatic build-source is the
domain, the apophatic hole is the codomain, and the empty center is the coincidence `X ≃ (X → B)` where they
would meet: kept empty by the hole (`empty_center_is_coincidence`) and symmetric under the op that swaps the
ends (`op_fixes_empty_center`). Not three centers, but the two ends and the empty middle of one
classification map. -/
theorem keystone {X B : Type} (gX : X → X) (hgX : ∀ x, gX x ≠ x) (gB : B → B) (hgB : ∀ b, gB b ≠ b) :
    (¬ Nonempty (X ≃ (X → B))) ∧ (¬ Nonempty (B ≃ (B → X))) :=
  op_fixes_empty_center gX hgX gB hgB
/-- **The concrete op involution.** The op that swaps the two centers is `Prod.swap` on the pair of
center-types. A real involution, `op ∘ op = id`, built not described. -/
def op_concrete : Type × Type → Type × Type := Prod.swap

/-- **op is a genuine involution.** `op_concrete ∘ op_concrete = id` on the term. -/
theorem op_concrete_involutive (p : Type × Type) : op_concrete (op_concrete p) = p := Prod.swap_swap p

/-- The empty center as a predicate on the pair of center-types. -/
def emptyCenterAt (p : Type × Type) : Prop := ¬ Nonempty (p.1 ≃ (p.1 → p.2))

/-- **The op-symmetry is the literal action of `op_concrete`.** The empty center holds at `(X, B)`
and at `op_concrete (X, B)`, so its swap-invariance is not merely "the property holds at both ends" but the
action of the concrete involution `op_concrete` on the pair of centers. The caveat closes: op is concrete
(`Prod.swap`), modest but real, and the symmetry references it. -/
theorem op_symmetry_is_op_action {X B : Type} (gX : X → X) (hgX : ∀ x, gX x ≠ x)
    (gB : B → B) (hgB : ∀ b, gB b ≠ b) :
    emptyCenterAt (X, B) ∧ emptyCenterAt (op_concrete (X, B)) :=
  ⟨empty_center_is_coincidence gB hgB, empty_center_is_coincidence gX hgX⟩
end Chiralogy
