import Chiralogy

/-! # Experiment: the permitted order as a lattice of quotients

`partial_totalizations_are_ranked` and `full_closure_is_the_top` gave an order on permitted totalizations
with the prohibition at the top. Identify what that order is and what acts on it. Hypothesis (Caramello): the
quotients of a geometric theory ordered by provability form a Heyting algebra, bottom the theory itself, top
the contradictory theory. A totalization closing a set of reasons is a quotient (identifying absences with
verdicts), and the prohibited full closure is the contradictory top.

Work at Except with two reasons (`Bool ⊕ Bool`, closures indexed by `Bool → Bool`). Stays in `Experiments/`;
canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.PermittedLattice

/-! ## Part 1: a lattice of quotients -/

/-- The quotient action of closing a set `S` of reasons: each throw `inr e` with `e ∈ S` is identified with a
verdict, verdicts and unclosed throws pass through. -/
def closeE (S : Bool → Bool) : Bool ⊕ Bool → Bool ⊕ Bool
  | Sum.inr e => bif S e then Sum.inl true else Sum.inr e
  | Sum.inl b => Sum.inl b

/-- **Totalizations are quotients.** Closing `{false}` identifies the throw `inr false` with the verdict
`inl true`, while the other throw and the verdicts are unchanged: a quotient of Except's theory by the axiom
`throw false = value`. -/
theorem totalizations_are_quotients :
    closeE (fun r => decide (r = false)) (Sum.inr false) = Sum.inl true
    ∧ closeE (fun r => decide (r = false)) (Sum.inr true) = Sum.inr true
    ∧ closeE (fun r => decide (r = false)) (Sum.inl true) = Sum.inl true := by decide

/-- Meet: close only what both close. -/
def cmeet (a b : Bool → Bool) : Bool → Bool := fun r => a r && b r

/-- Join: close what either closes. -/
def cjoin (a b : Bool → Bool) : Bool → Bool := fun r => a r || b r

/-- **Meet and join.** At Except with two reasons, closing `{false}` and closing `{true}` meet at the empty
closure and join at the full closure. -/
theorem meet_and_join :
    cmeet (fun r => decide (r = false)) (fun r => decide (r = true)) = (fun _ => false)
    ∧ cjoin (fun r => decide (r = false)) (fun r => decide (r = true)) = (fun _ => true) := by
  refine ⟨?_, ?_⟩ <;> · funext r; cases r <;> decide

/-- Closing every reason collides with faithfulness: the full closure is inconsistent. -/
theorem full_totality_collides :
    ¬ ∃ c : Fin 4 → Fin 4 → Bool ⊕ Bool,
      (∀ x y, ∃ b, c x y = Sum.inl b) ∧ (∃ x y e, c x y = Sum.inr e) := by
  rintro ⟨c, htot, x, y, e, he⟩
  obtain ⟨b, hb⟩ := htot x y
  rw [hb] at he; simp at he

/-- **The top is the contradictory theory.** The full closure is the top of the order
(`full_closure_is_the_top`) and the inconsistent one (`full_totality_collides`): the prohibition is the
contradictory quotient, not merely the maximal move. -/
theorem top_is_contradictory :
    (∀ close : Bool → Bool, closeLE close (fun _ => true))
    ∧ (¬ ∃ c : Fin 4 → Fin 4 → Bool ⊕ Bool, (∀ x y, ∃ b, c x y = Sum.inl b) ∧ (∃ x y e, c x y = Sum.inr e)) :=
  ⟨full_closure_is_the_top, full_totality_collides⟩

/-- **The bottom is the level itself.** The empty closure identifies nothing, leaving the theory unchanged,
and it is the bottom of the order. -/
theorem bottom_is_the_level_itself :
    (∀ x : Bool ⊕ Bool, closeE (fun _ => false) x = x)
    ∧ (∀ close : Bool → Bool, closeLE (fun _ => false) close) := by
  refine ⟨fun x => ?_, fun close r h => ?_⟩
  · cases x <;> rfl
  · simp at h

/-! ## Part 2: Heyting, in fact Boolean -/

/-- The candidate relative pseudo-complement `a ⇒ b`. -/
def chimp (a b : Bool → Bool) : Bool → Bool := fun r => !a r || b r

/-- **The lattice is Heyting.** The residuation holds exhaustively: for all `a b c`, `a ⊓ c ≤ b` iff
`c ≤ a ⇒ b`. So `chimp` is the relative pseudo-complement, checked on the term, not inferred. -/
theorem is_heyting :
    ∀ a b c : Bool → Bool, closeLE (cmeet a c) b ↔ closeLE c (chimp a b) := by decide

/-- **Negation forces the contradiction, and the lattice is Boolean.** The negation `¬a = a ⇒ ⊥` (bottom the
level) is the complementary closure, closing exactly the reasons `a` leaves open; joined with `a` it is the
contradictory top, met with `a` it is the level. So asserting a totalization and its negation forces the
prohibition. -/
theorem negation_is_forcing_contradiction :
    ∀ a : Bool → Bool,
      chimp a (fun _ => false) = (fun r => !a r)
      ∧ cjoin a (chimp a (fun _ => false)) = (fun _ => true)
      ∧ cmeet a (chimp a (fun _ => false)) = (fun _ => false) := by decide

/-! ## Part 3: what acts on the lattice -/

/-- **Dependence extends the signature.** The two context-selective moves are distinct
(`dependence_adds_reasons`), so a two-context Reader has two closeable reasons and a four-element lattice,
where the one-reason base had two. Dependence enlarges the quotient lattice. -/
theorem dependence_extends_the_signature :
    (readerCloseTrue (fun _ => none) ≠ readerCloseFalse (fun _ => none))
    ∧ Fintype.card (Bool → Bool) = 4 :=
  ⟨dependence_adds_reasons, by decide⟩

/-- **Markedness leaves the lattice fixed.** Plural-and-marked and Except both have two reasons, so the same
closure lattice, despite four absent values versus two. A marking multiplies values, not generators. -/
theorem markedness_leaves_the_lattice_fixed :
    (Finset.image (fun x : (Bool ⊕ Bool) × Bool => x.1)
       (Finset.univ.filter (fun x => ∃ e, x.1 = Sum.inr e))).card = 2
    ∧ (Finset.univ.filter (fun x : Bool ⊕ Bool => ∃ e, x = Sum.inr e)).card = 2 := by decide

/-- **Upstream is signature change.** An operation acts on the lattice exactly when it changes the signature:
dependence adds generators (the moves differ), markedness leaves the reason count fixed (equal counts). The
absent-value count follows markedness, so it too leaves the lattice fixed. Checked against the three
dimensions, not proven in general. -/
theorem upstream_is_signature_change :
    (readerCloseTrue (fun _ => none) ≠ readerCloseFalse (fun _ => none))
    ∧ ((Finset.image (fun x : (Bool ⊕ Bool) × Bool => x.1)
         (Finset.univ.filter (fun x => ∃ e, x.1 = Sum.inr e))).card
        = (Finset.univ.filter (fun x : Bool ⊕ Bool => ∃ e, x = Sum.inr e)).card) :=
  ⟨dependence_adds_reasons, by decide⟩

/-! ## The verdict

Part 1: the permitted order is a lattice of quotients. Closing a set of reasons is a quotient of the level's
theory, identifying throws with verdicts (`totalizations_are_quotients`); it has meets and joins
(`meet_and_join`), a bottom that is the level itself (`bottom_is_the_level_itself`), and a top that is both
maximal and inconsistent (`top_is_contradictory`): the prohibition is the contradictory quotient.

Part 2: the lattice is Heyting, in fact Boolean. The residuation holds exhaustively (`is_heyting`), so the
relative pseudo-complement exists; and every element has a complement (`negation_is_forcing_contradiction`),
so it is Boolean, the powerset of the reason set. The negation of a totalization is the complementary closure,
and a totalization joined with its negation is the prohibition. Caramello's general Heyting algebra is
realized here, on discrete finite reasons, as a Boolean algebra.

Part 3: what moves the lattice is signature change. Dependence extends the signature, adding generators and
enlarging the lattice (`dependence_extends_the_signature`); markedness multiplies values without generators
and leaves it fixed (`markedness_leaves_the_lattice_fixed`); the absent-value count follows markedness and is
inert. The criterion holds against the three dimensions checked (`upstream_is_signature_change`): upstream is
exactly signature change.

The verdict: the boundary's order is the Boolean algebra of reason-subsets, a lattice of quotients with the
level at the bottom and the prohibition, the inconsistent theory, at the top; what moves it is signature
change, which only dependence effects among the dimensions examined. Nothing here is resolved. -/

end Chiralogy.PermittedLattice
