import Chiralogy.Model.NaryAssemblage
import Chiralogy.Kernel.Apophatic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-! # The structural-shadow survey

A SURVEY. When we reify into a register, instantiate the framework in a concrete carrier and supply an import,
does the reified field carry emergent structure that is (a) import-independent, (b) framework-level once
abstracted, yet (c) NOT already derivable in the bare framework, visible ONLY through the reification. Does a
register cast a structural SHADOW that apophatic ascent can deposit back into the framework, or is everything
general in a reified field already a framework theorem, so the reification is a DISCOVERY LENS, not a source.

No smuggled expectations. DEAD, everything general in a reified field is already a bare-framework theorem, is a
first-class outcome. The standing-name lesson at the meta-level: structure found in a concrete model is USUALLY
the general theorem it instantiates, re-derivation, not new framework structure. The (c) test is the crux:
prove genuine-shadow, do not assume it. The math decides.

Register neutral: readings are prose only. Nothing touches canonical or the stance core.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Chiralogy
namespace StructuralShadow

/-! ## PART A / B: a reified regularity IS the general theorem instantiated (LENS)

The import-independent structure a reified field displays is the framework's own carrier-general structure,
specialized. Two witnesses: the slot count and the hole. -/

/-- **THE REIFIED SLOT COUNT IS THE GENERAL THEOREM.** Reifying into the two-Bool-factor register and counting
the import slots gives eight, but this is `cross_cell_count` instantiated, not a discovery of the register: the
import-independent regularity found in the field is the framework theorem specialized. RE-DERIVATION, a lens. -/
theorem reified_count_is_the_general_theorem :
    Fintype.card {p : (Fin 2 → Bool) × (Fin 2 → Bool) // IsCross (X := fun _ => Bool) p.1 p.2} = 8 := by
  rw [cross_cell_count]; decide

/-- **THE REIFIED HOLE IS THE GENERAL THEOREM.** Every classification in the concrete register fails
surjectivity, but this is `hole_uniform` specialized, the framework casting its own theorem down into the
register. So the field's import-independent structure is bare-framework structure made visible. RE-DERIVATION,
a lens, and the descent direction of Part D. -/
theorem descent_specializes_the_hole (c : (Fin 2 → Bool) → (Fin 2 → Bool) → Option Bool) :
    ¬ Function.Surjective c :=
  hole_uniform c

/-! ## PART C: register-tied structure DISSOLVES on ascent

Structure that uses the concrete carrier's extra data, its order, is not framework-general and does not
abstract back. The order classification is transitive because the carrier is ordered, but transitivity is not
forced on classifications, so the structure is the register's import, not a shadow. -/

/-- The order classification over the concrete ordered carrier. -/
def leC : Fin 2 → Fin 2 → Bool := fun x y => decide (x ≤ y)

/-- **TRANSITIVITY IS REGISTER-TIED, NOT FRAMEWORK-GENERAL.** In the reified field the order classification is
transitive, using the carrier's own `≤`. But transitivity is NOT a framework fact about classifications: a
classification can fail it. So the transitivity found in the field belongs to the register's supplied order,
not to the framework, and on ascent, abstracting away the carrier's order, it dissolves. Not a shadow. -/
theorem transitivity_is_register_tied :
    (∀ a b d : Fin 2, leC a b = true → leC b d = true → leC a d = true)
      ∧ ¬ (∀ (c : Fin 2 → Fin 2 → Bool) (a b d : Fin 2),
            c a b = true → c b d = true → c a d = true) := by
  refine ⟨by decide, ?_⟩
  intro h
  have hbad := h (fun x y => decide (x ≠ y)) 0 1 0 (by decide) (by decide)
  exact absurd hbad (by decide)

/-! ## The verdict, as prose

PART A. A reified field DOES carry import-independent emergent structure, but it is the framework's own
carrier-general structure specialized: the two gates, the hole (`descent_specializes_the_hole`), the slot count
(`reified_count_is_the_general_theorem`), the information order, the forbidden triple. Each holds for all
imports and is emergent in the field in the sense of being visible there. So Part A is not empty, there is
import-independent structure, but the question is whether any of it is new.

PART B, the crux. Every import-independent, general structure the field displays is ALREADY a bare-framework
theorem, RE-DERIVATION, a lens. The slot count found by reifying and counting is `cross_cell_count`
instantiated; the surjectivity failure found in the field is `hole_uniform` instantiated. The reification made
the theorem VISIBLE and easy to find, but did not create it. The dichotomy is sharp: a statement that is
import-independent and abstractable to the bare carrier can use only the framework's structure, so it is a
framework theorem; a statement that uses the concrete carrier's extra data is not abstractable. There is no
middle, so no GENUINE-SHADOW: import-independent-and-general-and-not-bare-derivable is empty.

PART C, the ascent. For register-tied structure the ascent FAILS by dissolution. The reified order
classification is transitive, but transitivity uses the carrier's `≤` and is not forced on classifications
(`transitivity_is_register_tied`), so abstracting the order away loses it: it was the register's import, not a
framework universal. And for the import-independent structure the ascent is VACUOUS, it deposits only what was
already framework-level. So nothing new completes the ascent: register-tied structure dissolves, framework
structure was already there.

PART D, symmetry. The method is ASYMMETRIC. DESCENT is faithful and productive: every carrier-general framework
theorem specializes to every register, the framework casting its structure DOWN into each reified field
(`descent_specializes_the_hole` the witness, `reified_count_is_the_general_theorem` a computed instance). ASCENT
is DEAD as a source: what a register sends UP is either a re-derivation of an existing framework theorem or,
if it uses the carrier's own structure, dissolves on abstraction. So the framework and the register are not
equal poles: the framework is the source, the register a lens and a specialization site, and structure flows
DOWN faithfully but not UP as anything new.

THE VERDICT: DEAD, DISCOVERY-LENS-ONLY. A register casts no structural shadow the framework lacks. Every
general, import-independent regularity in a reified field is a bare-framework theorem specialized
(`reified_count_is_the_general_theorem`, `descent_specializes_the_hole`), and the register-specific structure
that is genuinely new to the field uses the carrier's supplied data and dissolves on abstraction
(`transitivity_is_register_tied`), so it never reaches the framework. Reification is a heuristic that helps
FIND and COMPUTE framework structure, a discovery lens, not a source of structure the framework did not
already hold. Cataphatic descent specializes; apophatic ascent recovers only what descent deposited. The
register surfaces the framework to itself and adds nothing general.

Register readings, output only. Building a concrete instance of the theory and exploring it can reveal general
truths, but those truths were already true of the theory itself, the instance only made them easy to see and
to count. Whatever genuinely new regularity a concrete instance seems to have turns out to rest on the extra
scaffolding that instance brought with it, its own ordering or arithmetic, and that scaffolding does not
survive being stripped back to the bare theory. So a worked example is a lamp, not a well: it lights up
structure that is already there, and carries nothing back up that the theory did not already contain.
-/

/-! ## The named targets -/

section Checks
#check @reified_count_is_the_general_theorem
#check @descent_specializes_the_hole
#check @transitivity_is_register_tied
end Checks

#print axioms reified_count_is_the_general_theorem
#print axioms descent_specializes_the_hole
#print axioms transitivity_is_register_tied

end StructuralShadow
end Chiralogy
