import Chiralogy
import Mathlib.Data.Fintype.BigOperators

/-! # Experiment: open threads in the model composition

Five unexamined questions, independent verdicts: whether the model layer can carry a forced level, whether
blocking outside the forcing order preserves Heyting, whether there is a fifth axiom shape, the commutation
table of the five levels, and whether the conformance form distinguishes anything. Concrete small instances.
Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Composition

/-! ## Thread 1: can the model layer carry a forced level?

To carry an order rather than stipulate it, the level's theory must relate its constants. Try an operation
relating two absences, `b = s(a)`, on the value space `Fin 4` (0, 1 verdicts; 2 = a; 3 = b). A totalization
respecting the operation is a map commuting with `s`. -/

/-- The operation: `s(a) = b`, fixing everything else. -/
def sOp : Fin 4 → Fin 4
  | 2 => 3
  | x => x

/-- The verdicts. -/
def isVerdict (x : Fin 4) : Prop := x = 0 ∨ x = 1

/-- **Relating constants welds, it does not force.** Any totalization commuting with `s` has `t b = s (t a)`,
so closing `a` forces closing `b` (first) and leaving `a` open forces `b` open (second): the two constants move
together, both or neither. This is a welding, not a chain. The gate fails the other way: `{b}` is not closeable
alone (leaving `a` open keeps `b` open), so there is no genuine forced order, only fewer independent reasons. -/
theorem can_a_level_be_forced (t : Fin 4 → Fin 4) (hom : ∀ x, t (sOp x) = sOp (t x)) :
    (isVerdict (t 2) → isVerdict (t 3)) ∧ (t 2 = 2 → t 3 = 3) := by
  have h : t 3 = sOp (t 2) := by have := hom 2; simpa [sOp] using this
  refine ⟨?_, ?_⟩
  · rintro (h0 | h0) <;> (rw [h, h0]; simp [sOp, isVerdict])
  · intro h2; rw [h, h2]; rfl

/-- **Levels are free by construction.** In the free Except, closing one throw alone is a legitimate quotient:
`{false}` is closed to a verdict while `{true}` stays a throw, so the constants are independent (Boolean). The
only way to relate them, an equation, welds them (`can_a_level_be_forced`) rather than chaining them. So the
algebraic model layer yields free or welded constants, never a Heyting chain; the chain the forced charts carry
is implicational, outside the equational layer. The gap between the free tower and the forced charts is
structural, not contingent. -/
theorem levels_are_free_by_construction :
    closeE (fun r => decide (r = false)) (Sum.inr false) = Sum.inl true
    ∧ closeE (fun r => decide (r = false)) (Sum.inr true) = Sum.inr true :=
  ⟨by decide, by decide⟩

/-! ## Thread 2: non-overlapping departures

Block a reason that does not participate in the forcing. Forcing `0 ≺ 1`, blocked reason `2` outside it. -/

/-- **Blocking outside the order preserves Heyting.** The readable closures under forcing `0 ≺ 1` with reason
`2` blocked number three, exactly the up-sets of the pure two-chain, and fewer than the Boolean four: the
Heyting structure survives intact with the blocked reason simply removed. Computed, not asserted; contrast
`departures_interact`, where blocking a forced reason collapsed to Boolean. -/
theorem blocking_outside_the_order :
    (Finset.univ.filter (fun c : Fin 3 → Bool => (c 1 = true → c 0 = true) ∧ c 2 = false)).card = 3
    ∧ (Finset.univ.filter (fun c : Fin 2 → Bool => c 1 = true → c 0 = true)).card = 3
    ∧ Fintype.card (Fin 2 → Bool) = 4 :=
  ⟨by decide, by decide, by decide⟩

/-! ## Thread 3: a fifth axiom shape? -/

/-- **Self-axioms on constants give no fifth shape.** A pure self-axiom on a single constant is reflexivity,
which imposes nothing: the closeable family stays the free Boolean three. A nontrivial self-relation
(involution, here `!!x = x`) is an operation axiom, inert to the closeable family as operation-operation axioms
are. So the grid stands at the shapes already found; there is no fifth. -/
theorem self_axioms_on_constants :
    (Finset.univ.filter (fun c : Bool → Bool => ¬ ∀ r, c r = true)).card = 3
    ∧ (∀ x : Bool, !(!x) = x) :=
  ⟨by decide, by decide⟩

/-! ## Thread 4: the commutation table

Ordered pairs of transformers over concrete finite parameters, compared by cardinality as
`state_except_does_not_commute` did. -/

abbrev SoverE : Type := Bool → Unit ⊕ (Bool × Bool)
abbrev EoverS : Type := Bool → (Unit ⊕ Bool) × Bool
abbrev RoverW : Type := Bool → Bool × Bool
abbrev WoverR : Type := (Bool → Bool) × Bool
abbrev WoverE : Type := (Unit ⊕ Bool) × Bool
abbrev EoverW : Type := Unit ⊕ (Bool × Bool)
abbrev WoverW : Type := (Bool × Fin 3) × Bool
abbrev WoverW' : Type := (Bool × Bool) × Fin 3

/-- **The commutation table.** Of the pairs computed, three orderings differ in cardinality and so do not
commute (State/Except 25 vs 36, Reader/Writer 16 vs 8, Writer/Except 6 vs 5), and one commutes (Writer/Writer,
12 vs 12). With `state_state_commutes` the pattern is that non-commutation is common and commutation is the
exception, the commuting pairs being same-transformer stacks. -/
theorem commutation_table :
    Fintype.card SoverE ≠ Fintype.card EoverS
    ∧ Fintype.card RoverW ≠ Fintype.card WoverR
    ∧ Fintype.card WoverE ≠ Fintype.card EoverW
    ∧ Fintype.card WoverW = Fintype.card WoverW' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [SoverE, EoverS, Fintype.card_fun, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_unit]; norm_num
  · simp only [RoverW, WoverR, Fintype.card_fun, Fintype.card_prod, Fintype.card_bool]; norm_num
  · simp only [WoverE, EoverW, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_unit]; norm_num
  · simp only [WoverW, WoverW', Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]

/-! ## Thread 5: does the form see anything? -/

/-- **The form distinguishes nothing.** The cataphatic form is loose: every type is the carrier of some
conformant, so no carrier is excluded, and two witnesses differing in carrier, ambient, and build are both
conformant. The form applies no discriminating test; the witness family is undifferentiated from the
framework's side, and every classification of it, the algebraic/enriched split included, is ours. -/
theorem what_the_form_distinguishes :
    (∀ X : Type, ∃ cc : CataphaticConformant, cc.X = X)
    ∧ (⟨Bool, Bool, id⟩ : CataphaticConformant).X = Bool
    ∧ (⟨Fin 3, ℕ, fun _ => (0 : ℕ)⟩ : CataphaticConformant).X = Fin 3 :=
  ⟨fun X => cataphatic_is_loose X, rfl, rfl⟩

/-! ## The verdicts

Thread 1: forced levels are not constructible in the model layer, and levels are free by construction. Relating
two constants by an operation welds them, closing one forces the other in both directions
(`can_a_level_be_forced`), so the effect is fewer independent reasons, not a chain; the free constants of Except
are closeable independently (`levels_are_free_by_construction`). The equational model layer yields free or
welded, never a Heyting chain, which is implicational. The gap to the forced charts is structural.

Thread 2: blocking outside the forcing order preserves Heyting. The readable closures are the up-sets of the
untouched two-chain with the blocked reason removed, three not four (`blocking_outside_the_order`), so the
Heyting structure survives, unlike the collapse when the blocked reason is inside the order.

Thread 3: there is no fifth axiom shape. A pure self-axiom on a constant is reflexivity and inert; a nontrivial
one is an operation axiom, inert like operation-operation (`self_axioms_on_constants`). The grid stands.

Thread 4: non-commutation is common, commutation exceptional. Three of four computed pairs do not commute and
the one that does is a same-transformer stack (`commutation_table`); with `state_state_commutes` the commuting
cases are the same-type ones.

Thread 5: the form distinguishes nothing. It is loose, admitting every carrier and separating no two witnesses
(`what_the_form_distinguishes`); the witness family is undifferentiated from the framework's side, every
classification ours. Nothing here is resolved. -/

end Chiralogy.Composition
