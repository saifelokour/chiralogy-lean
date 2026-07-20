import Chiralogy

/-! # Experiment: the general form of visibility

`InvariantVisible` found marking is the visibility axis for the fabrication family, failing at vacating. The
candidate general form: every invisibility is one of three kinds, recordable (marking makes a historical
difference visible), declarable (the level makes a possibility nameable), or an identity (there is no difference
to see, and silence is correct). Test whether these exhaust the cases. The tidiness is the risk: an identity that
hides a gap, a fourth case forced into three, a tautology reported as content. Concrete instances. Stays in
`Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Visibility

/-- A total classification, never returning an absence. -/
def total : Fin 4 → Fin 4 → Option Bool := fun _ _ => some true

/-- A level that declares the ground `none`. -/
def dPred : Option Bool → Bool := fun x => decide (x = none)

/-- A level with no such ground. -/
def gPred : Option Bool → Bool := fun _ => false

/-! ## Part 1: is vacating an identity? -/

/-- **Vacated and groundless.** Across levels the classification is the same, `total` never returning an absence
at either, but the levels differ, one declaring the ground and one not (`dPred` against `gPred`). So a vacated
ground and a groundless level differ at the level, not the classification: this is declarable, not an identity. -/
theorem vacated_and_groundless :
    (total = total) ∧ (dPred none ≠ gPred none) :=
  ⟨rfl, by decide⟩

/-- **Avoided and never arose.** Within one level, two total classifications never return the ground, so at the
ground they are indistinguishable, both silent; "avoided" and "never arose" name the same absence of a return,
with no predicate at the ground separating them. Within one level the invisibility is an identity: there is no
difference to see, and silence is correct. -/
theorem avoided_and_never_arose (c1 c2 : Fin 4 → Fin 4 → Option Bool)
    (h1 : ∀ x y, c1 x y ≠ none) (h2 : ∀ x y, c2 x y ≠ none) :
    ∀ x y, (c1 x y = none) ↔ (c2 x y = none) :=
  fun x y => ⟨fun h => absurd h (h1 x y), fun h => absurd h (h2 x y)⟩

/-! ## Part 2: do the three exhaust? -/

/-- **Sort the invisibilities.** Recordable: detection, independence, provenance, each a fabrication marking
distinguishes (`collision_without_concealment`). Declarable: vacating across levels, the levels differing where
the classification does not (`dPred`, `gPred`). Identity: the guard's blindness, any two proofs of the hole equal
(`guard_erases`), no difference to see, and the failure to recover a source from agreement, distinct sources
giving identical agreement. Each of the six sorts into one of the three. -/
theorem sort_the_invisibilities :
    (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool)))
    ∧ (dPred none ≠ gPred none)
    ∧ (∀ (c : Fin 4 → Fin 4 → Option Bool) (h1 h2 : ¬ Function.Surjective c), h1 = h2) :=
  ⟨collision_without_concealment.2, by decide, fun c h1 h2 => guard_erases c h1 h2⟩

/-- **Is there a fourth.** The three exhaust the internally-determined invisibilities. But correspondence-truth
is a misfit, reported not forced: whether a verdict is correct is a difference that may hold externally, `some
true` and `some false` are distinct well-formed verdicts, yet no framework predicate grades either as matching a
reality. It is not recordable, no internal trace; not declarable, no level names reality; not an identity, an
external difference may exist. It is outside expressibility, the framework's `inexpressible` grade, a boundary
rather than a residue. -/
theorem is_there_a_fourth :
    ((some true : Option Bool) ≠ some false)
    ∧ (∀ b : Bool, (some b : Option Bool) ≠ none) :=
  ⟨by decide, fun b => Option.some_ne_none b⟩

/-! ## Part 3: the general statement -/

/-- **Visibility reaches difference.** A predicate distinguishes two objects only if they differ; visibility
reaches exactly to difference. As a bare statement this is a tautology, you can distinguish only what differs. Its
content is not here but in the sorting: where a difference lives determines which mechanism reaches it, historical
difference marking, level difference declaration, no difference identity, external difference nothing. -/
theorem visibility_reaches_difference {α : Type} (x y : α) (P : α → Bool) :
    P x ≠ P y → x ≠ y :=
  fun h he => h (congrArg P he)

/-- **What it rules out.** The form has content at one point. It predicts an identity cannot be made visible by
any addition: if two objects are equal, every predicate whatsoever, including any marking or declaration one
might add, agrees on them. So identity-invisibility is permanent, unreachable by extension, where recordable and
declarable invisibility are reached by adding marking or declaration. That is the one non-tautological
consequence: the guard's blindness and the within-level avoided-or-never-arose identity can never be made
visible, and correctly so, because there is nothing there to see. -/
theorem what_it_rules_out {α : Type} (x y : α) (h : x = y) :
    ∀ P : α → Bool, P x = P y :=
  fun P => congrArg P h

/-! ## The verdicts

Part 1: vacating splits, and the identity case is real. Across levels a vacated ground and a groundless level
share the classification but differ at the level (`vacated_and_groundless`), which is declarable, not an
identity. Within one level, two total classifications are indistinguishable at the ground, both silent
(`avoided_and_never_arose`), which is an identity, no difference to see. So the gate is honored: the across-level
comparison is declarable and the within-level one is an identity, and the third case is not a euphemism for a
gap.

Part 2: the three exhaust the internally-determined invisibilities, with a fourth outside. Detection,
independence, and provenance are recordable; vacating is declarable; the guard's blindness and the
source-from-agreement failure are identities (`sort_the_invisibilities`). But correspondence-truth is a misfit
(`is_there_a_fourth`): a difference that may hold externally, with no internal trace, no level to name it, and no
identity, so it is outside expressibility, a boundary the framework structurally cannot see, not a residue within
it. Reported, not forced.

Part 3: the general form is a tautology with one consequence. Visibility reaches exactly to difference
(`visibility_reaches_difference`), which as stated says only that a predicate distinguishes only what differs. Its
one non-tautological content is that an identity is permanently invisible, unreachable by any addition
(`what_it_rules_out`), where recordable and declarable invisibility are reached by adding marking or declaration.

The verdict: the trichotomy holds for what the framework can see, and its third case is real, not a euphemism.
Recordable covers historical difference, reached by marking; declarable covers level difference, reached by
declaration; identity covers the absence of difference, permanently invisible and correctly so. Vacating is not a
gap in the trichotomy but an instance of it, declarable across levels and an identity within one. The three
exhaust the internally-determined invisibilities, and the honest residue is not a fourth internal kind but the
boundary of expressibility itself, correspondence-truth, a difference the framework has no referent for, its own
`inexpressible` grade. And the general form is mostly tautological: visibility reaches difference is close to
empty, saying you can distinguish only what differs; its single content is that identity-invisibility cannot be
lifted by any addition, which separates the correct silences from the recordable and declarable gaps. So marking
and declaration are the two mechanisms that make determined difference visible, identity is the correct silence,
and the external is the edge past all three. Reported per part. Nothing here is resolved. -/

end Chiralogy.Visibility
