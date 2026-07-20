import Chiralogy

/-! # Experiment: how much can the operational regions hold?

The tower has five categories; three are dense and two, the unary and binary operations, hold almost nothing.
Determine whether they are unexplored or structurally thin. What is there now: nothing depends on a level's
unary structure, and the binary region has blocking (the absorbing law) and the operation-shape distinction of
`three_axiom_shapes`. Ask whether blocking is the only route by which operations reach the ethics, the closeable
family and the prohibition. Note which operations are natural to the framework's levels and which are
constructed for the test. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.OperationalContent

/-- A unary operation permuting two verdicts and fixing the absences. -/
def swapU : Fin 4 → Fin 4 := fun v => if v = 2 then 3 else if v = 3 then 2 else v

/-! ## Part 1: survey the routes -/

/-- **A unary operation can reach the ethics.** Two routes, both with constructed operations. Welding: a unary
operation relating two grounds (`sOp`, `s a = b`) makes closing one force the other (`equational_relations_weld`).
Blocking: a unary operation permuting verdicts with a fixed absence forces any respecting totalization to send
that absence to a fixed point of the permutation, an absence, so it cannot be closed to a verdict. -/
theorem can_a_unary_operation_reach_the_ethics :
    (∀ t : Fin 4 → Fin 4, (∀ x, t (sOp x) = sOp (t x)) → (isVerdict (t 2) → isVerdict (t 3)))
    ∧ (∀ t : Fin 4 → Fin 4, (∀ x, t (swapU x) = swapU (t x)) → swapU (t 0) = t 0) :=
  ⟨fun t hom => (equational_relations_weld t hom).1, fun _ h => (h 0).symm⟩

/-- **Binary routes beyond absorption.** Absorption blocks: no verdict absorbs under `mzAppend`, so closing the
absorbing reason is illegitimate. Welding is a distinct route: relating two grounds makes them both-or-neither, a
different effect on the family. So the binary region holds at least two phenomena. -/
theorem binary_routes_beyond_absorption :
    (∀ a : List Bool, mzAppend (some a) none ≠ some a)
    ∧ (∀ t : Fin 4 → Fin 4, (∀ x, t (sOp x) = sOp (t x)) → (t 2 = 2 → t 3 = 3)) :=
  ⟨blocking_removes_a_closure, fun t hom => (equational_relations_weld t hom).2⟩

/-! ## Part 2: is the operational contribution bounded? -/

/-- **What operations can do.** As far as the small instances show, an operation affects the family in three
ways: block a closure (no verdict absorbs), weld two grounds (both-or-neither), or nothing (an
operation-operation axiom, here `mzAppend` associativity, leaves the family untouched). This is provisional, not
proven exhaustive: a complete characterization needs a type of signatures the framework does not carry. -/
theorem what_operations_can_do :
    (∀ a : List Bool, mzAppend (some a) none ≠ some a)
    ∧ (∀ t : Fin 4 → Fin 4, (∀ x, t (sOp x) = sOp (t x)) → (isVerdict (t 2) → isVerdict (t 3)))
    ∧ (∀ a b c : Option (List Bool), mzAppend (mzAppend a b) c = mzAppend a (mzAppend b c)) := by
  refine ⟨blocking_removes_a_closure, fun t hom => (equational_relations_weld t hom).1, fun a b c => ?_⟩
  cases a <;> cases b <;> cases c <;> simp [mzAppend, List.append_assoc]

/-- **Blocking is not the only binary route.** Welding is distinct: under welding a closure is possible, both
grounds closing together (a respecting totalization sends both to a verdict), where under blocking the absorbing
reason closes not at all. Distinct closeability, so the binary region has at least two phenomena. -/
theorem is_blocking_the_only_binary_route :
    (∃ t : Fin 4 → Fin 4, (∀ x, t (sOp x) = sOp (t x)) ∧ isVerdict (t 2) ∧ isVerdict (t 3))
    ∧ (∀ a : List Bool, mzAppend (some a) none ≠ some a) :=
  ⟨⟨fun _ => 0, fun _ => rfl, Or.inl rfl, Or.inl rfl⟩, blocking_removes_a_closure⟩

/-- **The unary region is non-empty.** A unary operation relating two distinct grounds (`sOp`, `2 ≠ 3`) welds
them, changing the closeable family. So the region holds structure. It is a constructed operation, though; the
framework's natural unary operation, the group inverse, is a verdict operation and relates no absences, so the
region is populable in principle and thin in the built levels. -/
theorem unary_region_status :
    ∃ (s : Fin 4 → Fin 4) (a b : Fin 4),
      s a = b ∧ a ≠ b
      ∧ (∀ t : Fin 4 → Fin 4, (∀ x, t (s x) = s (t x)) → (isVerdict (t a) → isVerdict (t b))) :=
  ⟨sOp, 2, 3, rfl, by decide, fun t hom => (equational_relations_weld t hom).1⟩

/-! ## Part 3: the layout input -/

/-- **Region contents.** A representative of each side: the classification holds the hole (dense); the grounds
hold the reasons (dense); the binary region holds absorption-blocking (found); the unary region holds an
operation relating two grounds (possible). The full contents are in the verdict; dense regions warrant a place,
thin ones may not, but this reports contents, it does not decide. -/
theorem region_contents :
    (∀ {X : Type} (c : X → X → Option Bool), ¬ Function.Surjective c)
    ∧ (∀ v : Option Bool, v = none ↔ ∃ u : Unit, failMaybe u = v)
    ∧ (∀ a : List Bool, mzAppend (some a) none ≠ some a)
    ∧ (∃ (s : Fin 4 → Fin 4) (a b : Fin 4), s a = b ∧ a ≠ b) :=
  ⟨fun c => hole_uniform c, reasons_are_nullary_generators.2, blocking_removes_a_closure,
   ⟨sOp, 2, 3, rfl, by decide⟩⟩

/-! ## The verdicts

Part 1: unary operations can reach the ethics, and there are binary routes beyond absorption. A unary operation
welds two grounds or blocks a closure (`can_a_unary_operation_reach_the_ethics`); the binary region holds
absorption and welding, distinct effects (`binary_routes_beyond_absorption`). All are operations relating an
absence; the routes are blocking and welding.

Part 2: the operational contribution is bounded by three effects, block, weld, or nothing
(`what_operations_can_do`), but the list is provisional, not exhaustive, absent a type of signatures. Welding is
distinct from blocking: welding permits a closure of both grounds, blocking permits none
(`is_blocking_the_only_binary_route`). The unary region is non-empty (`unary_region_status`), a unary operation
welding two grounds, but only constructed operations reach it; the group inverse, the natural unary operation,
is a verdict operation relating no absences.

Part 3: the region contents (`region_contents` gives a representative of each). Classification: the hole, the
payload, the center, the collision, dense and found. Grounds: the reason count, the closeable family, the
permitted lattice, the prohibition, dense and found. Order: forcing and the Heyting order, refinement, the
free-ground axis, the departure space, dense and found. Unary: welding and permutation-blocking, thin, only
constructed operations reach it, none natural. Binary: absorption-blocking (with `mzAppend` at the
list-with-failure level a natural example), welding, and operation-operation inertness, found, and possibly more,
provisional. So three dense regions and two thin, the thin ones populable by constructed operations but sparse in
the built levels. This is the input to the layout, not a decision. Nothing here is resolved. -/

end Chiralogy.OperationalContent
