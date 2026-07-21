import Chiralogy

/-! # Experiment: assemblages as registers

`RegisterRelations` found the framework's relations between registers trivial or absent, and the missing colimit
possibly the wrong tool since constitution is not parthood. Assemblage theory (DeLanda) says wholes are not
derived from parts. Test whether the framework can host an assemblage as a register rather than derive one. All
domain content IMPORTED, mappings READINGS, comparisons not imports. The imported criteria: exteriority
(components detach and re-plug), weak emergence (the whole not an aggregate of the parts), properties versus
capacities (manifest versus what a component can do in relation, real but unexercised), and two parameters, coding
(identity fixed by rules) and territorialization (boundaries sharp, components homogenized). Stays in
`Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Assemblage

/-- Two registers with different shapes, and their classifications. -/
def trustClassify : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none
def cogClassify : Fin 3 → Fin 3 → Option Bool := fun x y => if x = y then some true else none
def Rtrust : Obj := ⟨Fin 2, Option Bool, trustClassify⟩
def Rcog : Obj := ⟨Fin 3, Option Bool, cogClassify⟩

/-- The assemblage's cross-classification, IMPORTED (a stipulated cross-verdict, not derived from the factors,
since `RegisterRelations` showed no canonical coproduct value). -/
def assemblageClassify : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → Option Bool :=
  fun a b => if a = b then some true else if a.1 = b.1 then some false else none

/-- The assemblage as an object: carrier the product of the two carriers, classify imported. -/
def Rassemblage : Obj := ⟨Fin 2 × Fin 3, Option Bool, assemblageClassify⟩

/-! ## Part 1: an assemblage as a register -/

/-- **The assemblage is a register.** Its carrier is the product of the two factors' carriers and its classify is
IMPORTED, a stipulated cross-classification not derived from the factors (RegisterRelations, no canonical
coproduct value); the payload fires. The import is the point, not a construction. -/
theorem assemblage_register :
    (Rassemblage.X = (Fin 2 × Fin 3))
    ∧ (¬ Function.Surjective assemblageClassify) :=
  ⟨rfl, hole_uniform assemblageClassify⟩

/-- **It conforms.** The unchanged protocol asks only can-differ and non-degeneracy: distinct rows exist and the
payload fires, so the assemblage is a member. -/
theorem it_conforms :
    (NonDegenerate assemblageClassify) ∧ (¬ Function.Surjective assemblageClassify) :=
  ⟨⟨(0, 0), (0, 1), by decide⟩, hole_uniform assemblageClassify⟩

/-- **The grounds are not the union.** The assemblage carries an absence at a fully-cross pair and an emergent
verdict `some false` at a same-first-component pair, a distinction about the relation between the two axes that
neither factor carries alone: DeLanda's weak emergence, the whole not an aggregate, is cleared. The interactions
are IMPORTED, as RegisterRelations showed they must be, not derived. -/
theorem grounds_are_not_the_union :
    (assemblageClassify (0, 0) (1, 2) = none)
    ∧ (assemblageClassify (0, 0) (0, 1) = some false) :=
  ⟨by decide, by decide⟩

/-! ## Part 2: exteriority -/

/-- **The factors remain registers.** Forming the assemblage creates a new object and leaves each factor
unchanged, still a member with its own payload and non-degeneracy: the factors are not consumed into the whole. -/
theorem factors_remain_registers :
    (¬ Function.Surjective trustClassify) ∧ (¬ Function.Surjective cogClassify)
    ∧ (NonDegenerate trustClassify) :=
  ⟨hole_uniform _, hole_uniform _, ⟨0, 1, by decide⟩⟩

/-- A second partner and assemblage: trust with physics. -/
def assemblage2Classify : (Fin 2 × Fin 1) → (Fin 2 × Fin 1) → Option Bool :=
  fun a b => if a.1 = b.1 then some true else none
def Rassemblage2 : Obj := ⟨Fin 2 × Fin 1, Option Bool, assemblage2Classify⟩

/-- **Refactoring.** The same factor (trust, `Fin 2`) pairs with a different register (physics, `Fin 1`) giving a
different assemblage, its carrier and cross-classification different: the component detaches and re-plugs, its
interactions differing in the new whole. Detachability, testable not a gloss. -/
theorem refactoring :
    (Rassemblage.X = (Fin 2 × Fin 3)) ∧ (Rassemblage2.X = (Fin 2 × Fin 1))
    ∧ (¬ Function.Surjective assemblage2Classify) :=
  ⟨rfl, rfl, hole_uniform _⟩

/-! ## Part 3: the two knobs -/

/-- **Coding as order-density.** Measuring coding by the closures ruled out (`2^n` minus closeable), the chain is
most coded (four ruled out), the mixed order less (two), the discrete order uncoded (none): identity fixed by
rules is the order restricting the closeable family, the ordering across the shapes sensible. -/
theorem coding_as_order_density :
    ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqChain3 S)).card = 4)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqMixed3 S)).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqDiscrete S)).card = 0) :=
  ⟨by decide, by decide, by decide⟩

/-- **Territorialization as free-part.** The free-part size, the isolated grounds: the chain has none (sharply
bounded), the mixed order one, and physics's single ground is free. -/
theorem territorialization_as_free_part :
    ((Finset.univ.filter (fun i : Fin 3 => isFree prereqChain3 i)).card = 0)
    ∧ ((Finset.univ.filter (fun i : Fin 3 => isFree prereqMixed3 i)).card = 1)
    ∧ ((Finset.univ.filter (fun i : Fin 1 => isFree prereqDiscrete i)).card = 1) :=
  ⟨by decide, by decide, by decide⟩

/-- **Do the knobs hold.** Coding holds, the chain more coded than the discrete order (four ruled out against
none). Territorialization fails on physics: its single ground is free, so the free-part reading calls physics
maximally permeable, yet physics is the base, the most sharply defined register with one prohibition. The
identification is wrong there; territorialization does not reduce to the free-part, since an isolated single
ground reads as permeable when it bounds sharply. -/
theorem do_the_knobs_hold :
    ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqChain3 S)).card = 4)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => ¬ closeable prereqDiscrete S)).card = 0)
    ∧ (isFree (prereqDiscrete : Fin 1 → Fin 1 → Bool) 0) :=
  ⟨by decide, by decide, by decide⟩

/-! ## Part 4: properties and capacities -/

/-- **The ground-structure is properties.** Manifest and computed from the register alone: the permitted count,
the closeable family, and the order, five permitted at the mixed order. DeLanda's properties, what the component
manifestly is. -/
theorem ground_structure_is_properties :
    (Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqMixed3 S ∧ ¬ ∀ r, S r = true)).card = 5 := by
  decide

/-- **The cross-values are capacities.** What a register contributes to a cross-classification is not derivable
from its own grounds, two fillings equally valid (RegisterRelations); yet the assemblage carries a definite
cross-value once formed, `some false` at a same-first-component pair. DeLanda's capacity, real but not a property
of the factor alone. It strains on where the capacity resides: DeLanda's is latent in the component, here it is
imported at the whole, so the capacity is supplied to the assemblage rather than carried by the part. -/
theorem cross_values_are_capacities :
    (∃ c1 c2 : (Unit ⊕ Unit) → (Unit ⊕ Unit) → Bool,
        c1 (Sum.inl ()) (Sum.inr ()) ≠ c2 (Sum.inl ()) (Sum.inr ()))
    ∧ (assemblageClassify (0, 0) (0, 1) = some false) :=
  ⟨⟨fun _ _ => true, fun _ _ => false, by decide⟩, by decide⟩

/-! ## The verdicts

Part 1: an assemblage conforms as a register, its grounds new. It is an object on the product carrier with an
imported cross-classification, the payload firing (`assemblage_register`), passing the unchanged protocol
(`it_conforms`); its grounds are not the union, carrying an emergent distinction about the relation between the
axes that neither factor holds (`grounds_are_not_the_union`), DeLanda's weak emergence cleared. The
cross-classification is imported, as it must be, not derived.

Part 2: exteriority holds. The factors remain registers, unchanged (`factors_remain_registers`), and the same
factor re-pairs with a different register giving a different assemblage (`refactoring`): components detach and
re-plug.

Part 3: coding identifies with order-density, territorialization does not identify cleanly. Coding is the closures
ruled out, sensible across the shapes (`coding_as_order_density`); territorialization is the free-part
(`territorialization_as_free_part`), but it fails on physics, whose single free ground reads as maximally
permeable though physics is the base, the sharpest register (`do_the_knobs_hold`). The failure is informative: one
knob reduces to ground-structure, the other does not.

Part 4: the property/capacity distinction holds with a stated strain. The ground-structure is properties, manifest
and computed (`ground_structure_is_properties`); the cross-values are capacities, real once the assemblage forms
but not derivable from the factor (`cross_values_are_capacities`), straining on where the capacity resides, in the
component or imported at the whole.

The verdict: the framework can host an assemblage as a register, not derive one. The assemblage is an object on
the product carrier with an imported cross-classification, and it conforms, its grounds emergent rather than a
union, so DeLanda's weak bar is cleared and exteriority holds, the factors detaching and re-pairing. But the
import is the point and is stated as such: RegisterRelations showed the cross-values cannot be derived, so hosting
imports what deriving could not build. The two knobs split: coding reduces to the order-density, closures ruled
out, sensible across the six; territorialization does not, failing on physics where a single free ground reads as
permeable though the register is the sharpest. And the property/capacity distinction fits, with the capacity
imported at the whole rather than latent in the component, a stated strain. So the fit is real but partial, and
honest where it is imported and where a knob is wrong. The vocabulary stays a comparison; the framework's terms
remain its own. Reported per part. Nothing here is resolved. -/

end Chiralogy.Assemblage
