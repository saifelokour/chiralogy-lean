import Chiralogy.Kernel.Apophatic

/-! # The map/territory growth-loop survey

A SURVEY making the chiastic growth process explicit: the framework is the abstract MAP, registers are reified
TERRITORIES, and the survey assembles the three legs of how the map grows, marking exactly which are Lean
STRUCTURE and which are HELD reading. The special risk here is philosophy-as-structure, so the core job is
ruthless separation: a leg is PROVEN only if it compiles carrier-general, else it is HELD.

The claim being made explicit: (i) you must explore a TERRITORY to expand the map, the map being apophatic
with no directly searchable interior; (ii) ANY territory can expand it, the map being abstract and shared;
(iii) when expanded, ALL territories gain resolution, a refinement descending to every register by
instantiation. The compounding asymmetry: ascent from ONE territory is rare, the graduation event; descent to
ALL territories is automatic and faithful.

The key meta-constraint: the loop CANNOT be a CLOSED self-description, that would be the forbidden fixed point
the hole excludes, so the output is an OPEN procedure plus preconditions plus a held whole, never a single
closed theorem. Any drift toward a closed self-description of growth is flagged as the forbidden closure.

Register neutral: readings are prose only. Nothing touches canonical or the stance core.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Chiralogy
namespace GrowthLoop

/-! ## LEG 1: descent-to-all is INSTANTIATION (definitional, not new structure)

A carrier-general framework fact holds at every register by instantiation. This compiles, but its content is
exactly the meaning of universal quantification: the near-triviality IS the mechanism. -/

/-- **DESCENT TO ALL IS INSTANTIATION.** A framework fact, universal over carriers, holds at any register by
being applied to it. The proof is the instantiation and nothing more, so this is DEFINITIONAL, the honest
content of the compounding payoff: all territories gain resolution BECAUSE abstract structure is universally
instantiable, not by any further theorem. -/
theorem descent_to_all_is_instantiation {V : Type}
    (P : (X : Type) → (X → X → Option Bool) → Prop)
    (hframework : ∀ X c, P X c) (register : V → V → Option Bool) : P V register :=
  hframework V register

/-! ## LEG 3: the shared map is ONE proposition (definitional, shared-ness = carrier-generality)

The map is genuinely one shared object, not per-register copies, because a framework fact is a SINGLE
carrier-general proposition that every register instantiates. Two registers draw the same fact from the same
proof. -/

/-- **THE SHARED MAP IS ONE PROPOSITION.** A fact found once, universal over carriers, is available to two
distinct registers not by transfer between them but because both instantiate the SAME universal proof. So the
map is singular and shared, and this shared-ness is exactly carrier-generality, DEFINITIONAL, not a further
theorem and not merely the incidental fact that there is one library. -/
theorem the_shared_map_is_one_proposition {V W : Type}
    (P : (X : Type) → (X → X → Option Bool) → Prop)
    (hframework : ∀ X c, P X c)
    (rV : V → V → Option Bool) (rW : W → W → Option Bool) : P V rV ∧ P W rW :=
  ⟨hframework V rV, hframework W rW⟩

/-! ## THE ASSEMBLY: the loop cannot close (PROVEN, the hole is the obstruction)

The growth-loop cannot be captured as content IN the framework, a closed total self-description, because such
a description is a surjection the hole forbids. So the loop is a procedure run ON the framework, forever open. -/

/-- **THE LOOP CANNOT CLOSE.** Any attempt to make the growth-loop content inside the framework, a total
internal self-description of its own state space, is a surjection, and no total internal self-description is
surjective (`no_total_internal_self_description`). So the loop can never be a single closed theorem the
framework contains about its own growth; it stays an OPEN procedure run on the framework. This is the forbidden
closure, confirmed excluded. Carrier-general. -/
theorem the_loop_cannot_close {D : Type} (selfDescribe : D → D → Bool) :
    ¬ Function.Surjective selfDescribe :=
  no_total_internal_self_description selfDescribe

/-! ## The verdict, as prose

LEG 1, descent-to-all: DEFINITIONAL. That a carrier-general theorem holds in every register is instantiation
(`descent_to_all_is_instantiation`), the definitional payoff of abstractness, not new content. But the
near-triviality IS the point: all territories gain resolution automatically precisely because abstract
structure is universally instantiable. The descent leg is the mechanism's honest content, the automatic and
faithful half of the asymmetry, and it is exactly what carrier-generality MEANS.

LEG 2, must-descend-to-expand: HELD, not proven. The claim that the map cannot be expanded without descending
into a territory is a methodological reading, not a framework theorem. It RHYMES with two proven results but
is not either: COMPLETE-TRIVIAL (RelationalShape, no fixed finite list of invariants determines a register up
to iso, so the abstraction has no finitely-searchable interior) and the HOLE (no total internal
self-description, so the framework cannot enumerate its own structure from inside). These GROUND the leg by
analogy, the apophatic map having no searchable interior, so the concrete route is the available one, but
neither literally PROVES must-descend, which is a claim about the discovery process, not about classifications.
Reported HELD, with two rhyming proven anchors, not dressed as a theorem.

LEG 3, any-territory-can-expand: DEFINITIONAL. The map is genuinely one shared object because a framework fact
is a SINGLE carrier-general proposition every register instantiates (`the_shared_map_is_one_proposition`), so a
fact found via one register is available to another by shared instantiation, not transfer. This shared-ness is
carrier-generality itself, the definitional twin of Leg 1 from the ascent side, not a further theorem.

THE ASSEMBLY, the open loop. Descend cataphatically into a territory, find structure, ascend apophatically
stripping the register-specific and keeping the general, the map expands, and by Leg 1 all territories gain
resolution, enabling new descents. This session's graduation procedure IS this loop: surveys are the descent,
the five gates the ascent, gate zero the forced-absence test for genuinely-new structure. The loop CANNOT
close (`the_loop_cannot_close`): a closed total self-description of its own growth is a surjection the hole
forbids, so the loop is a procedure run ON the framework, never a theorem IN it. No drift to closure survives.

THE VERDICT: a READING WITH DEFINITIONAL ANCHORS, honestly (b), not (a). The formalization succeeds as an
explicit OPEN PROCEDURE with preconditions and a held whole, but its Lean content is NOT new theorems: Legs 1
and 3 are instantiation (DEFINITIONAL), Leg 2 is HELD with COMPLETE-TRIVIAL and the hole as rhyming anchors,
and the loop-openness is the hole restated at the growth level (`the_loop_cannot_close`, PROVEN but = the
canonical hole). So the map/territory growth-loop is a genuine and correctly-assembled procedure, its
preconditions real and proven, but it is a reading resting on instantiation and the hole, not a new structural
result. The near-triviality of the descent leg and the un-closability from the hole are the whole Lean
substance; the compounding asymmetry and the growth narrative are the held whole. Not inflated: the loop is a
true procedure, and it contains no new theorem, because by its own constraint it cannot.

Register readings, output only. A shared abstract account grows only by working through concrete cases, since
it has no inside to inspect directly; any one case can enrich it, and once enriched every case inherits the
enrichment for free, because they are all instances of the one account. What is rare is the lifting of a
finding from a single case into the shared account; what is automatic is that lift reaching all cases at once.
And the account can never contain a complete description of how it itself grows, since a system that could
totally describe itself would close a loop its own founding limit forbids: the growth is something done with
the account, not a fact stated within it.
-/

/-! ## The named targets -/

section Checks
#check @descent_to_all_is_instantiation
#check @the_shared_map_is_one_proposition
#check @the_loop_cannot_close
end Checks

#print axioms descent_to_all_is_instantiation
#print axioms the_shared_map_is_one_proposition
#print axioms the_loop_cannot_close

end GrowthLoop
end Chiralogy
