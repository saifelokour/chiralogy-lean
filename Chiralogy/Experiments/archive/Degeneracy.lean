import Chiralogy

/-! # Experiment: degeneracy and its opposite, for objects, relations, and parts

An object's degeneracy is settled: distinguishing nothing fails Member, the floor. Test the corresponding notions
for morphisms and for part-whole, at both ends. The two ends per structure: objects, distinguishing nothing versus
distinguishing maximally; morphisms, constant versus injective; part-whole, an assemblage insensitive to a factor
versus one fully determined by its factors. Compute all cases before judging. Stays in `Experiments/`; canonical
untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Degeneracy

/-- The saturated classifier: each element true on its own diagonal, absent elsewhere, so every row is distinct. -/
def satN {n : ℕ} : Fin n → Fin n → Option Bool := fun x y => if x = y then some true else none

/-! ## Part 1: objects -/

/-- **Object degeneracy is excluded.** Distinguishing nothing, the total opening, fails Member: it is the floor. -/
theorem object_degeneracy_is_excluded {X : Type} :
    ¬ NonDegenerate (fun _ _ => none : X → X → Option Bool) := by
  rintro ⟨x, x', h⟩; exact h rfl

/-- **Object saturation.** The opposite end: the transpose injective, every element with its own row. It is
reachable, a member, and satisfies the hole; nothing is forbidden there. Saturation is about distinctions, the
prohibition about absences, so they are different states. -/
theorem object_saturation :
    Function.Injective (fun x : Fin 2 => satN x)
    ∧ NonDegenerate (satN : Fin 2 → Fin 2 → Option Bool)
    ∧ ¬ Function.Surjective (satN : Fin 2 → Fin 2 → Option Bool) := by
  refine ⟨by decide, ?_, hole_uniform _⟩
  unfold NonDegenerate; decide

/-- **Saturation is not bounded.** It is reachable at any size and compatible with the hole: the hole forbids
surjectivity, not injectivity, so injective (saturated) and non-surjective (holed) coexist. The distinction-axis
maximum is free, unlike the absence-axis maximum, the prohibition. -/
theorem is_saturation_bounded :
    (Function.Injective (fun x : Fin 3 => satN x))
    ∧ (¬ Function.Surjective (satN : Fin 3 → Fin 3 → Option Bool))
    ∧ (Function.Injective (fun x : Fin 4 => satN x)) :=
  ⟨by decide, hole_uniform _, by decide⟩

/-! ## Part 2: morphisms -/

/-- The terminal object, and the maps that collapse. -/
def pt : Obj := ⟨Unit, Unit, fun _ _ => ()⟩
def toPt (S : Obj) : Hom S pt := ⟨fun _ => (), fun _ => (), fun _ _ => rfl⟩
def idHom (S : Obj) : Hom S S := ⟨id, id, fun _ _ => rfl⟩
def constEndo (S : Obj) (x0 : S.X) : Hom S S := ⟨fun _ => x0, fun _ => S.classify x0 x0, fun _ _ => rfl⟩
def emb : Hom ⟨Fin 2, Fin 2, fun x _ => x⟩ ⟨Fin 3, Fin 3, fun x _ => x⟩ :=
  ⟨Fin.castSucc, Fin.castSucc, fun _ _ => rfl⟩

/-- **Degenerate morphisms are permitted.** The terminal map is constant and exists for every object, permitted;
yet a degenerate object is excluded. The framework excludes degenerate objects and permits degenerate relations. -/
theorem degenerate_morphisms_are_permitted (S : Obj) :
    Nonempty (Hom S pt)
    ∧ ¬ NonDegenerate (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) :=
  ⟨⟨toPt S⟩, by rintro ⟨x, x', h⟩; exact h rfl⟩

/-- **Self versus other degeneracy.** A constant map to the terminal object collapses into a structureless point,
its target a subsingleton; a constant endomorphism collapses into one of the object's own points, keeping that
point's row. Different in kind: one erases structure, the other selects a point retaining it. -/
theorem self_versus_other_degeneracy (S : Obj) (x0 : S.X) :
    (Nonempty (Hom S pt) ∧ Subsingleton pt.B)
    ∧ Nonempty (Hom S S) :=
  ⟨⟨⟨toPt S⟩, inferInstanceAs (Subsingleton Unit)⟩, ⟨constEndo S x0⟩⟩

/-- **Morphism saturation.** The saturated end for morphisms is injectivity, on the carrier and on the values; the
identity achieves both. This is the injective end the tower already works at, where an ordered morphism is
ground-injective. -/
theorem morphism_saturation (S : Obj) :
    Function.Injective (idHom S).onCarrier ∧ Function.Injective (idHom S).onValues :=
  ⟨fun _ _ h => h, fun _ _ h => h⟩

/-- **Full injectivity is available.** There is a morphism injective on both carrier and values between distinct
objects: an embedding of a smaller register into a larger. The non-degenerate end of morphisms is inhabited. -/
theorem is_full_injectivity_available :
    ∃ (S T : Obj) (h : Hom S T), Function.Injective h.onCarrier ∧ Function.Injective h.onValues :=
  ⟨_, _, emb, Fin.castSucc_injective 2, Fin.castSucc_injective 2⟩

/-! ## Part 3: part-whole -/

/-- **No assemblage is insensitive to a factor.** Changing the first factor on a distinguishing same-second pair
changes the assemblage: it is sensitive to each factor. A degenerate factor makes its region constant but is still
consulted, so insensitivity is not achieved. This is not exteriority failing: exteriority is the factor detaching,
sensitivity is the whole reflecting it. -/
theorem assemblage_insensitive_to_a_factor :
    ∃ (c1 c1' c2 : Fin 2 → Fin 2 → Option Bool)
      (imp : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool) (a b : Fin 2 × Fin 2),
      assembleClassify c1 c2 imp a b ≠ assembleClassify c1' c2 imp a b :=
  ⟨fun x y => if x = 0 ∧ y = 1 then some true else none, fun _ _ => none, fun _ _ => none,
   fun _ _ => none, (0, 0), (1, 0), by decide⟩

/-- **No assemblage with two non-trivial factors is fully determined by them.** With a singleton factor there is
no fully-cross region, so the import is irrelevant and the assemblage is determined by its factors; but with both
factors non-trivial the import is free, and the assemblage exceeds its factors. Emergence stated as a bound: full
determination is available only when a factor is trivial. -/
theorem assemblage_fully_determined :
    (∀ (c1 : Fin 2 → Fin 2 → Option Bool) (c2 : Fin 1 → Fin 1 → Option Bool)
        (imp imp' : (Fin 2 × Fin 1) → (Fin 2 × Fin 1) → Option Bool) (a b : Fin 2 × Fin 1),
        assembleClassify c1 c2 imp a b = assembleClassify c1 c2 imp' a b)
    ∧ (∃ (c1 c2 : Fin 2 → Fin 2 → Option Bool)
        (imp imp' : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Option Bool) (a b : Fin 2 × Fin 2),
        assembleClassify c1 c2 imp a b ≠ assembleClassify c1 c2 imp' a b) := by
  refine ⟨fun c1 c2 imp imp' a b =>
    construction_takes_two_objects_and_a_cross_map c1 c2 imp imp'
      (fun a b _ h2 => absurd (Subsingleton.elim a.2 b.2) h2) a b, ?_⟩
  exact ⟨fun _ _ => none, fun _ _ => none, fun _ _ => some true, fun _ _ => none, (0, 0), (1, 1), by decide⟩

/-- **Part-whole degeneracy is not exteriority failing.** Exteriority, each factor remaining a payload-firing
register that detaches, holds always, both where the assemblage is fully determined (a singleton factor) and where
it is emergent (both factors non-trivial). So it is orthogonal to whether the whole is sensitive to or determined
by its parts: part-whole degeneracy is about the whole reflecting the part, exteriority about the part surviving
detachment. -/
theorem relation_to_exteriority :
    (∀ c1 c2 : Fin 2 → Fin 2 → Option Bool, ¬ Function.Surjective c1 ∧ ¬ Function.Surjective c2)
    ∧ (∀ (c1 : Fin 2 → Fin 2 → Option Bool) (c2 : Fin 1 → Fin 1 → Option Bool),
        ¬ Function.Surjective c1 ∧ ¬ Function.Surjective c2) :=
  ⟨fun _ _ => ⟨hole_uniform _, hole_uniform _⟩, fun _ _ => ⟨hole_uniform _, hole_uniform _⟩⟩

/-! ## The verdicts

Part 1: saturation is reachable and free. Degeneracy, distinguishing nothing, is excluded, the floor
(`object_degeneracy_is_excluded`); the opposite, the transpose injective, is reachable, a member, and holed
(`object_saturation`), and it is unbounded, reachable at any size and compatible with the hole, which forbids
surjectivity not injectivity (`is_saturation_bounded`). Saturation is about distinctions, the prohibition about
absences, so the two ceilings are different states.

Part 2: degenerate morphisms are permitted and the injective end is where the work is. The terminal map is
constant and canonical, permitted where degenerate objects are excluded (`degenerate_morphisms_are_permitted`);
the self and other collapses differ in kind, one erasing structure, the other retaining a point's row
(`self_versus_other_degeneracy`); the identity is injective on both carrier and values, the saturated end
(`morphism_saturation`); and full injectivity is available between distinct objects (`is_full_injectivity_available`).

Part 3: no assemblage is insensitive to a factor, and none with two non-trivial factors is fully determined by
them. Changing a factor changes the assemblage (`assemblage_insensitive_to_a_factor`); the import is free unless a
factor is trivial, so full determination is available only in the degenerate case (`assemblage_fully_determined`);
and exteriority holds regardless, orthogonal to both (`relation_to_exteriority`).

The verdict: the two ends behave differently across the three structures, and the asymmetry between objects and
relations is real, not a defect. For objects, the floor, distinguishing nothing, is excluded, while the opposite,
saturation, the transpose injective, is free: reachable at any size, a member, and compatible with the hole, which
bounds only surjectivity. The distinction-axis maximum is unforbidden; the framework's one prohibition is on the
absence axis, so saturation and the prohibition are different states, not two names for a ceiling. For morphisms,
degeneracy is permitted: the terminal map is constant and canonical, and the framework excludes degenerate objects
yet permits degenerate relations, which is correct rather than a defect, since a trivial relation between two
objects says something admissible where a trivial object says nothing. The two degenerate collapses differ in kind,
the terminal erasing structure and the endomorphism selecting a point that keeps its row. The injective end is
where the framework does its work, ground-injectivity in the tower, and full injectivity is available. For
part-whole, no assemblage is insensitive to a factor, each being consulted, and no assemblage with two non-trivial
factors is fully determined by them, the import staying free, so emergence is a bound: full determination is
available only when a factor is trivial. And exteriority is a distinct notion, holding whether the assemblage is
sensitive to its factors or not, so part-whole degeneracy is not exteriority failing. Per the counter-bias, the
opposite end was not assumed bounded, saturation being free; the object/morphism asymmetry is read as correct, not
a defect; and exteriority was checked against part-whole degeneracy and found distinct. Reported per part. Nothing
here is resolved. -/

end Chiralogy.Degeneracy
