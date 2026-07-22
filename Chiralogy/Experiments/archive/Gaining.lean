import Chiralogy

/-! ARCHIVED (SPENT): the graduatable universal results of this investigation already reached
canonical in prior sessions, so nothing graduated in the graduate-now wave. Mapping:
  when_does_it_create -> Model/Apophatic (as totalization_separates_equal_rows, identical statement generalized to {X}).
Remaining content is fixed-size witnesses and (where present) fragility/scale coordinates, kept as
the investigation record. Namespaced under Chiralogy.Gaining, it typechecks standalone against canonical. -/

/-! # Experiment: does fabrication create distinctions?

Flattening measured distinctions lost under totalization and never asked whether any are gained. The fill is
scale-dependent, `decide (s y ≤ s x)`, so two rows identical except both abstaining at a pair could receive
different fills and become distinct. Test whether totalization creates distinctions as well as destroys them, and
whether the axis is three-valued. Compute all cases before judging. Stays in `Experiments/`; canonical untouched;
nothing resolved. -/

open Chiralogy

namespace Chiralogy.Gaining

def satN {n : ℕ} : Fin n → Fin n → Option Bool := fun x y => if x = y then some true else none
def totSat3 : Fin 3 → Fin 3 → Option Bool := fun x y => some (decide (x = y))
def mid : Fin 3 → Fin 3 → Option Bool := fun x y =>
  if x = 0 then (if y = 0 then some true else none)
  else if x = 1 then (if y = 0 then some false else none) else (if y = 2 then some true else none)
def idScale {n : ℕ} : Fin n → Nat := fun i => (i : Nat)

/-- An object with two rows equal before and a third absence-distinct, and a scale that both separates the equal
pair and merges the distinct one. -/
def both4 : Fin 4 → Fin 4 → Option Bool := fun x y => if x = 2 ∧ y = 0 then some true else none
def bScale : Fin 4 → Nat := ![0, 1, 2, 2]

/-! ## Part 1: can distinctions be created? -/

/-- **Totalization can create distinctions.** The total opening's two rows are identical before totalization and
distinct after, under a distinguishing scale: the scale-dependent fill separates them where both abstained. The
axis is not two-valued. -/
theorem totalization_can_create :
    ((fun _ _ => none : Fin 2 → Fin 2 → Option Bool) 0 = (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) 1)
    ∧ (totalization idScale (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) 0
        ≠ totalization idScale (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) 1) := by
  refine ⟨rfl, by decide⟩

/-- **When it creates.** Two rows equal before totalization become distinct after exactly when they share an
absence at a pair where the fill separates them, `decide (s y ≤ s x) ≠ decide (s y ≤ s x')`. Sufficient: at such a
pair the totalization gives different filled values. -/
theorem when_does_it_create {n : ℕ} (c : Fin n → Fin n → Option Bool) (s : Fin n → Nat) (x x' : Fin n) :
    c x = c x' → (∃ y, c x y = none ∧ decide (s y ≤ s x) ≠ decide (s y ≤ s x')) →
    totalization s c x ≠ totalization s c x' := by
  intro heqc hy htot
  obtain ⟨y, hnone, hf⟩ := hy
  have hnone' : c x' y = none := (congrFun heqc y) ▸ hnone
  have he := congrFun htot y
  have e1 : totalization s c x y = some (decide (s y ≤ s x)) := by simp [totalization, hnone]
  have e2 : totalization s c x' y = some (decide (s y ≤ s x')) := by simp [totalization, hnone']
  rw [e1, e2] at he
  exact hf (Option.some_inj.mp he)

/-- **Creation is scale-dependent.** The same object gains a distinction under a distinguishing scale and none
under the flat scale, where every row receives the same fill. So creation is a property of the totalization with a
scale, not of the object. -/
theorem is_creation_scale_dependent :
    (totalization idScale (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) 0
        ≠ totalization idScale (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) 1)
    ∧ (totalization (fun _ => 0) (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) 0
        = totalization (fun _ => 0) (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) 1) := by
  refine ⟨by decide, by decide⟩

/-! ## Part 2: the net -/

/-- The pairs created: equal before totalization, distinct after. -/
def created {n : ℕ} (c : Fin n → Fin n → Option Bool) (s : Fin n → Nat) : Nat :=
  (Finset.univ.filter (fun p : Fin n × Fin n =>
    c p.1 = c p.2 ∧ totalization s c p.1 ≠ totalization s c p.2)).card

/-- The pairs destroyed: distinct before totalization, merged after. -/
def destroyed {n : ℕ} (c : Fin n → Fin n → Option Bool) (s : Fin n → Nat) : Nat :=
  (Finset.univ.filter (fun p : Fin n × Fin n =>
    c p.1 ≠ c p.2 ∧ totalization s c p.1 = totalization s c p.2)).card

/-- **The net change.** Under the flat scale nothing is created, so the net is nonpositive; destruction varies with
the object, the saturated map losing six, the intermediate two, the robust none. The flat destruction is not the
fragility, the flat fill sparing the pairs distinguished by a `some false`. -/
theorem net_change_in_distinction :
    (created (satN : Fin 3 → Fin 3 → Option Bool) (fun _ => 0) = 0
      ∧ destroyed (satN : Fin 3 → Fin 3 → Option Bool) (fun _ => 0) = 6)
    ∧ (created mid (fun _ => 0) = 0 ∧ destroyed mid (fun _ => 0) = 2)
    ∧ (created totSat3 (fun _ => 0) = 0 ∧ destroyed totSat3 (fun _ => 0) = 0) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **The net can be positive.** The total opening, degenerate, totalizes under a distinguishing scale to a
classification with distinct rows: created two, destroyed none, a net gain. An object ends more distinguishing than
it began. -/
theorem can_the_net_be_positive :
    (created (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) idScale = 2)
    ∧ (destroyed (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) idScale = 0) := by
  refine ⟨by decide, by decide⟩

/-- **The axis is three-valued.** Destroyed, preserved, and created are all inhabited: the saturated map loses
under the flat scale, the robust map keeps all its distinctions unchanged, the total opening gains under a
distinguishing scale. And one object shows two at once, created six and destroyed two under a single scale. -/
theorem is_the_axis_three_valued :
    (destroyed (satN : Fin 3 → Fin 3 → Option Bool) (fun _ => 0) = 6)
    ∧ (created totSat3 (fun _ => 0) = 0 ∧ destroyed totSat3 (fun _ => 0) = 0 ∧ NonDegenerate totSat3)
    ∧ (created (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) idScale = 2)
    ∧ (created both4 bScale = 6 ∧ destroyed both4 bScale = 2) := by
  refine ⟨by decide, ⟨by decide, by decide, by unfold NonDegenerate; decide⟩, by decide, by decide, by decide⟩

/-! ## Part 3: is it the same phenomenon as antifragility? -/

/-- **Creation is not antifragility.** Creation is scale-dependent, gained under one scale and not another, a
property of the totalization with a scale; the framework's antifragility is a fixed boundary fact, a fabricated
value unfaithful at the hole regardless of any scale. The mechanisms differ, sharing only the word gain, so the
name is not reused. -/
theorem compare_to_antifragility :
    (totalization idScale (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) 0
        ≠ totalization idScale (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) 1
      ∧ totalization (fun _ => 0) (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) 0
        = totalization (fun _ => 0) (fun _ _ => none : Fin 2 → Fin 2 → Option Bool) 1)
    ∧ (∀ c : Fin 4 → Fin 4 → Option Bool, c 0 2 = some true → c 0 2 ≠ imprecise 0 2) := by
  refine ⟨⟨by decide, by decide⟩, fun c => lie_fragility_is_boundary_derived c⟩

/-! ## The verdicts

Part 1: totalization can create distinctions, scale-dependently. The total opening's identical rows become
distinct under a distinguishing scale (`totalization_can_create`); this happens exactly when the two rows share an
absence at a pair where the fill separates them (`when_does_it_create`); and it is scale-dependent, gained under
one scale and not the flat one (`is_creation_scale_dependent`).

Part 2: the net can be positive and the axis is three-valued. Under the flat scale nothing is created and the net
is nonpositive (`net_change_in_distinction`); but the total opening totalizes under a distinguishing scale to a
more distinguishing object, a net gain (`can_the_net_be_positive`); destroyed, preserved, and created are all
inhabited, and one object shows creation and destruction at once (`is_the_axis_three_valued`).

Part 3: creation is not antifragility. Creation is scale-dependent, a property of the move with a scale; the
framework's antifragility is a fixed boundary fact independent of any scale (`compare_to_antifragility`). The name
is not reused.

The verdict: totalization creates distinctions as well as destroying them, so the effect of fabrication on
distinction is three-valued, destroyed, preserved, created, and the net can be positive. Two rows identical before
totalization become distinct after exactly when they share an absence at a pair where the fill separates them, the
scale sending `decide (s y ≤ s x)` one way for one row and the other way for the other. Creation is scale-dependent:
under the flat scale every row receives the same fill and nothing is created, while a distinguishing scale
separates rows that shared an absence, so creation is a property of the totalization with a scale, not of the
object, and must be reported as such. The total opening, the maximally degenerate object, totalizes under a
distinguishing scale to one with distinct rows, created without any prior distinction to destroy, so the net change
in distinction is genuinely positive there, an object ending more distinguishing than it began. All three values
are inhabited, and a single object can show creation and destruction at once under one scale, the fill separating
one equal pair while merging another distinct one. This is not the framework's antifragility, which is a fixed fact
derived from the boundary, a fabricated value unfaithful at the hole regardless of scale, whereas creation here
depends entirely on the arbitrary scale; the two share only the word gain, so the name is not borrowed. Per the
counter-bias, creation was exhibited before any claim about the axis, so it is not assumed; the scale-dependence
was checked and creation reported as a property of the move rather than the object; and the antifragility name was
gated on the mechanisms matching, which they do not. Reported per part. Nothing here is resolved. -/

end Chiralogy.Gaining
