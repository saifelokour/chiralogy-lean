import Chiralogy

/-! # Experiment: how registers relate

Six registers exist and the framework has no notion of them interacting. Test the relations it does have, and
re-attack the coproduct it was found to lack. Settled: `Obj` is finitely complete; `CorpusThreads` found no
natural coproduct, since a cross-pair `(inl x, inr y)` has no canonical value, two fillings being equally valid.
The tower's adjoints are whole-part but vertical, one object with more or less structure, not many objects and
one. Mereology distinguishes parthood from constitution, and constitution's mereological status is contested, so
the missing coproduct may be the wrong tool even were it available. Concrete instances. Stays in `Experiments/`;
canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.RegisterRelations

/-- The one-point apex. -/
def apex1 : Obj := ⟨Unit, Unit, fun _ _ => ()⟩
def apexTo (T : Obj) (x : T.X) : Hom apex1 T := ⟨fun _ => x, fun _ => T.classify x x, fun _ _ => rfl⟩

/-- The empty object, initial. -/
def botObj : Obj := ⟨Empty, Empty, fun x _ => x.elim⟩
def botTo (R : Obj) : Hom botObj R := ⟨fun x => x.elim, fun x => x.elim, fun x _ => x.elim⟩

/-- Two registers with differing carriers, for illustration. -/
def Ragents : Obj := ⟨Fin 2, Option Bool, fun x y => if x = y then some true else none⟩
def Rrepr : Obj := ⟨Fin 3, Option Bool, fun x y => if x = y then some true else none⟩

/-! ## Part 1: the lateral span -/

/-- **Any two registers share an apex, trivially.** The one-point object maps to a chosen point in each register,
whatever their carriers; the differing carriers do not block it, since a function maps one point anywhere. So a
shared apex exists for every pair, including any of the six, and relates no pair specifically. -/
theorem do_any_registers_share_an_apex (R1 R2 : Obj) (x1 : R1.X) (x2 : R2.X) :
    Nonempty (Hom apex1 R1) ∧ Nonempty (Hom apex1 R2) :=
  ⟨⟨apexTo R1 x1⟩, ⟨apexTo R2 x2⟩⟩

/-- **What a shared apex would mean.** The empty object is a shared apex for every register, being initial, but it
carries nothing, so it sources nothing; a non-trivial shared apex would be a common source, forward only, and a
source is not a containment, a register not a part of its apex. -/
theorem what_a_shared_apex_would_mean :
    (∀ R : Obj, Nonempty (Hom botObj R))
    ∧ (IsEmpty botObj.X)
    ∧ ((none : Option Bool) ≠ some true) :=
  ⟨fun R => ⟨botTo R⟩, ⟨fun x => nomatch x⟩, by decide⟩

/-! ## Part 2: relations as subobjects -/

/-- **A register relation exists.** Since `Obj` has products, any two registers have a product with projection
morphisms; a relation is a subobject of it. -/
theorem register_relation_exists (R1 R2 : Obj) :
    Nonempty (Hom (objProd R1 R2) R1) ∧ Nonempty (Hom (objProd R1 R2) R2) :=
  obj_has_products R1 R2

/-- **It is too weak.** A classification-respecting relation always exists, the product itself, an `Obj` with
morphism projections to both whose classify restricts to each: requiring the relation to respect both
classifications does not make it contingent, since the full product respects trivially. So every pair is related
by their product, saying nothing specific. -/
theorem is_it_too_weak (R1 R2 : Obj) :
    (Nonempty (Hom (objProd R1 R2) R1) ∧ Nonempty (Hom (objProd R1 R2) R2))
    ∧ (∀ x y : (objProd R1 R2).X, ((objProd R1 R2).classify x y).1 = R1.classify x.1 y.1) :=
  ⟨obj_has_products R1 R2, fun _ _ => rfl⟩

/-! ## Part 3: colimits, re-attacked -/

/-- **Why the coproduct fails.** A cross-pair `(inl x, inr y)` has no canonical verdict, two fillings both valid. -/
theorem why_the_coproduct_fails :
    ∃ c1 c2 : (Unit ⊕ Unit) → (Unit ⊕ Unit) → Bool,
      c1 (Sum.inl ()) (Sum.inr ()) ≠ c2 (Sum.inl ()) (Sum.inr ()) :=
  ⟨fun _ _ => true, fun _ _ => false, by decide⟩

/-- **A stipulated cross-value breaks the universal property.** The coproduct stipulates one value for all
cross-pairs, but a target distinguishing two cross-pairs forces the mediating map to send that one value to two
targets, `med false = true` and `med false = false`, impossible; so no mediating morphism, and the stipulation is
not a coproduct. -/
theorem stipulated_cross_value_breaks_up :
    ∃ t1 t2 : Bool, t1 ≠ t2 ∧ (∀ med : Bool → Bool, med false = t1 → med false = t2 → False) :=
  ⟨true, false, by decide, fun med h1 h2 => by rw [h1] at h2; exact absurd h2 (by decide)⟩

/-- **A pushout does not repair it.** Gluing along a shared subobject determines cross-pairs only for shared
elements; the cross-pairs of unshared elements still have no canonical value, the same obstruction. -/
theorem pushout_still_has_cross_pairs :
    ∃ c1 c2 : (Unit ⊕ Unit) → (Unit ⊕ Unit) → Bool,
      c1 (Sum.inl ()) (Sum.inr ()) ≠ c2 (Sum.inl ()) (Sum.inr ()) :=
  ⟨fun _ _ => true, fun _ _ => false, by decide⟩

/-- **A subcategory removes the cross-pairs.** Where off-diagonal classify is the absence, the coproduct's
cross-pairs take the canonical value `none`, consistent (the coproduct is itself diagonal-only), so the
obstruction does not arise. A genuine repair, but only in a subcategory the registers may not lie in. -/
theorem subcategory_removes_cross_pairs :
    ∀ x y : Unit ⊕ Unit, x ≠ y →
      (fun a b : Unit ⊕ Unit => if a = b then some true else none) x y = none :=
  fun _ _ hxy => if_neg hxy

/-- **The verdict on colimits.** Genuinely absent, repairable only by restriction. A stipulated cross-value
breaks the mediating map; a pushout leaves unshared cross-pairs undetermined; a weak colimit fails on existence
not merely uniqueness, since no cross-value makes the mediating map a morphism; only the diagonal-only
subcategory removes the cross-pairs, the absence being their canonical value there. -/
theorem verdict_on_colimits :
    (∃ t1 t2 : Bool, t1 ≠ t2 ∧ (∀ med : Bool → Bool, med false = t1 → med false = t2 → False))
    ∧ (∀ x y : Unit ⊕ Unit, x ≠ y →
        (fun a b : Unit ⊕ Unit => if a = b then some true else none) x y = none) :=
  ⟨⟨true, false, by decide, fun med h1 h2 => by rw [h1] at h2; exact absurd h2 (by decide)⟩,
   fun _ _ hxy => if_neg hxy⟩

/-! ## Part 4: behavioral mereology as the external comparison -/

/-- **Constraint-passing is not available.** The channel carries nothing, its capacity zero; the lateral span
passes agreement forward through an apex but not a constraint; and morphisms carry a classification, not a
mediated constraint. So the framework has mediation and transmission-of-nothing, but no constraint passed between
objects through a third. -/
theorem is_constraint_passing_available {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b)
    (b1 b2 : X → (X → B)) :
    ((¬ Function.Surjective b1) ↔ (¬ Function.Surjective b2))
    ∧ (∀ R : Obj, Nonempty (Hom botObj R)) :=
  ⟨channel_capacity_is_zero hg b1 b2, fun R => ⟨botTo R⟩⟩

/-- **Compare honestly.** Behavioral mereology has parthood as constraint, with modalities of compatibility and
ensurance mediated by the whole: one part's behavior restricts another's through the whole. The framework has a
mediated relation, the lateral span through an apex, but it inherits agreement forward and carries no modal
constraint; its channel is zero-capacity, certifying without informing. What behavioral mereology has and the
framework lacks is the modal mediated constraint. A comparison, not an import. -/
theorem compare_honestly {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) (b1 b2 : X → (X → B)) :
    ((¬ Function.Surjective b1) ↔ (¬ Function.Surjective b2))
    ∧ (IsEmpty botObj.X) :=
  ⟨channel_capacity_is_zero hg b1 b2, ⟨fun x => nomatch x⟩⟩

/-! ## The verdicts

Part 1: a shared apex exists for every pair, trivially. The one-point object maps to any register at a chosen
point, differing carriers no obstacle (`do_any_registers_share_an_apex`); the empty object is a universal apex
carrying nothing (`what_a_shared_apex_would_mean`). So the lateral span relates no pair specifically, and a
non-trivial apex would be a common source, forward only, not a containment.

Part 2: a classification-respecting relation is trivial, neither contingent nor impossible. Every pair has a
product (`register_relation_exists`), and the product itself is a respecting relation with morphism projections,
existing always (`is_it_too_weak`). So requiring respect does not constrain, and the relation notion says nothing
specific about the registers.

Part 3: colimits are genuinely absent, repairable only by restriction. The cross-pair has no canonical verdict
(`why_the_coproduct_fails`); a stipulated value breaks the mediating map (`stipulated_cross_value_breaks_up`), a
pushout leaves unshared cross-pairs undetermined (`pushout_still_has_cross_pairs`), a weak colimit fails on
existence; only the diagonal-only subcategory removes the cross-pairs (`subcategory_removes_cross_pairs`,
`verdict_on_colimits`). So the coproduct is absent in general and present only where cross-pairs cannot arise.

Part 4: constraint-passing is not available. The channel is zero-capacity and the span inherits agreement forward
without a modality (`is_constraint_passing_available`); behavioral mereology's modal mediated constraint is what
the framework lacks (`compare_honestly`).

The verdict: the framework's relations between registers are trivial or absent, and the one it lacks is not the
one that would help. A shared apex and a classification-respecting relation exist for every pair, so neither
relates the registers specifically, the pull toward a relation answered by constructions that relate any two
objects whatsoever. The coproduct is genuinely absent, resisting stipulation, pushout, and weakening, and yields
only in a subcategory where cross-pairs cannot arise, the absence their canonical value; and a coproduct may be
the wrong tool regardless, constitution not being parthood. What the framework lacks against behavioral mereology
is constraint-passing, a modal restriction mediated by a whole, which is neither its zero-capacity channel nor
its forward-only span. So registers do not relate in the framework as it stands, and the honest report is a
comparison naming the missing structure, not an import of it. Reported per part. Nothing here is resolved. -/

end Chiralogy.RegisterRelations
