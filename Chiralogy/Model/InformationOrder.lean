import Chiralogy.Model.Moves

/-! # The information order on classifications

A partial order on classifications `X → X → Option Bool`, pointwise from the cell order on `Option Bool`
(`none` below `some b`; `some b` comparable to `some b'` only when equal). It is the order the two moves already
travel: `partialization` descends it, `totalization` ascends it. Its maxima are exactly the total
classifications; it is a meet-semilattice with no joins of incomparable presences; and non-lattice-ness and the
non-monotonicity of `totalization` are the same obstruction.

Depends only on the moves (`totalization`, `partialization` in `Model/Apophatic`); no finiteness anywhere except
where a witness fixes a carrier, and `DecidableEq` only for `maximal_iff_total` and `fillCell`. -/

namespace Chiralogy

/-! ## The order -/

/-- The cell order on `Option Bool`: absence below presence, presences comparable only when equal. -/
def optLE (a b : Option Bool) : Prop := a = none ∨ a = b

/-- The pointwise information order on classifications: cellwise `optLE`. -/
def cLE {X : Type} (c d : X → X → Option Bool) : Prop := ∀ x y, optLE (c x y) (d x y)

theorem optLE_refl (a : Option Bool) : optLE a a := Or.inr rfl

theorem optLE_trans {a b c : Option Bool} (h1 : optLE a b) (h2 : optLE b c) : optLE a c := by
  unfold optLE at *
  rcases h1 with rfl | rfl
  · exact Or.inl rfl
  · rcases h2 with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem optLE_antisymm {a b : Option Bool} (h1 : optLE a b) (h2 : optLE b a) : a = b := by
  unfold optLE at *
  rcases h1 with rfl | rfl
  · rcases h2 with h | h
    · exact h.symm
    · exact h.symm
  · rfl

theorem cLE_refl {X : Type} (c : X → X → Option Bool) : cLE c c := fun _ _ => optLE_refl _

theorem cLE_trans {X : Type} {c d e : X → X → Option Bool} (h1 : cLE c d) (h2 : cLE d e) : cLE c e :=
  fun x y => optLE_trans (h1 x y) (h2 x y)

theorem cLE_antisymm {X : Type} {c d : X → X → Option Bool} (h1 : cLE c d) (h2 : cLE d c) : c = d := by
  funext x y; exact optLE_antisymm (h1 x y) (h2 x y)

/-- The all-absent classification, the order bottom. -/
def botC (X : Type) : X → X → Option Bool := fun _ _ => none

theorem botC_le {X : Type} (c : X → X → Option Bool) : cLE (botC X) c := fun _ _ => Or.inl rfl

/-- Totality: no absences. -/
def isTotal {X : Type} (c : X → X → Option Bool) : Prop := ∀ x y, c x y ≠ none

/-- **The order maxima are exactly the total classifications.** Predicate-ceiling and order-maximal coincide. -/
theorem maximal_iff_total {X : Type} [DecidableEq X] (c : X → X → Option Bool) :
    (∀ d, cLE c d → cLE d c) ↔ isTotal c := by
  constructor
  · intro hmax x0 y0 hnone
    set d : X → X → Option Bool := fun x y => if x = x0 ∧ y = y0 then some true else c x y with hd
    have hcd : cLE c d := by
      intro x y
      by_cases hxy : x = x0 ∧ y = y0
      · simp only [hd, if_pos hxy]; rw [hxy.1, hxy.2, hnone]; exact Or.inl rfl
      · simp only [hd, if_neg hxy]; exact Or.inr rfl
    have hback := hmax d hcd x0 y0
    simp only [hd, if_pos (⟨rfl, rfl⟩ : x0 = x0 ∧ y0 = y0), hnone, optLE] at hback
    rcases hback with h | h <;> simp at h
  · intro htot d hcd x y
    rcases hcd x y with h | h
    · exact absurd h (htot x y)
    · exact Or.inr h.symm

/-! ## Lattice structure: meet exists, join does not -/

/-- Cellwise meet: two presences agree or fall to absence. -/
def optMeet (a b : Option Bool) : Option Bool :=
  match a, b with
  | some x, some y => if x = y then some x else none
  | _, _ => none

def cMeet {X : Type} (c d : X → X → Option Bool) : X → X → Option Bool :=
  fun x y => optMeet (c x y) (d x y)

theorem optMeet_le_left (a b : Option Bool) : optLE (optMeet a b) a := by
  cases a with
  | none => exact Or.inl rfl
  | some x =>
    cases b with
    | none => exact Or.inl rfl
    | some y =>
      by_cases h : x = y
      · simp [optMeet, h, optLE]
      · simp [optMeet, h, optLE]

theorem optMeet_le_right (a b : Option Bool) : optLE (optMeet a b) b := by
  cases a with
  | none => exact Or.inl rfl
  | some x =>
    cases b with
    | none => exact Or.inl rfl
    | some y =>
      by_cases h : x = y
      · simp [optMeet, h, optLE]
      · simp [optMeet, h, optLE]

theorem optMeet_greatest {a b e : Option Bool} (h1 : optLE e a) (h2 : optLE e b) : optLE e (optMeet a b) := by
  unfold optLE at *
  rcases h1 with rfl | rfl
  · exact Or.inl rfl
  · rcases h2 with h | h
    · exact Or.inl h
    · subst h; cases e with
      | none => exact Or.inl rfl
      | some x => simp [optMeet]

theorem cMeet_le_left {X : Type} (c d : X → X → Option Bool) : cLE (cMeet c d) c :=
  fun _ _ => optMeet_le_left _ _
theorem cMeet_le_right {X : Type} (c d : X → X → Option Bool) : cLE (cMeet c d) d :=
  fun _ _ => optMeet_le_right _ _
theorem cMeet_greatest {X : Type} {c d e : X → X → Option Bool}
    (h1 : cLE e c) (h2 : cLE e d) : cLE e (cMeet c d) :=
  fun x y => optMeet_greatest (h1 x y) (h2 x y)

/-- Constant classifications, used as incomparable maxima. -/
def cTrue {X : Type} : X → X → Option Bool := fun _ _ => some true
def cFalse {X : Type} : X → X → Option Bool := fun _ _ => some false

/-- **Not a lattice.** Over any nonempty carrier the two constant total classifications have no common upper
bound: the join of incomparable presences does not exist. Needs only a point in the carrier, no finiteness. -/
theorem no_common_upper_bound {X : Type} [Nonempty X] :
    ¬ ∃ u : X → X → Option Bool, cLE cTrue u ∧ cLE cFalse u := by
  rintro ⟨u, h1, h2⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  have e1 := h1 x x; have e2 := h2 x x
  simp only [cTrue, cFalse, optLE] at e1 e2
  rcases e1 with e1 | e1
  · exact absurd e1 (by simp)
  rcases e2 with e2 | e2
  · exact absurd e2 (by simp)
  rw [← e1] at e2; simp at e2

/-! ## The moves against the order -/

/-- **Totalization is above its input.** -/
theorem c_le_totalization {X : Type} (s : X → Nat) (c : X → X → Option Bool) :
    cLE c (totalization s c) := by
  intro x y
  rcases hxy : c x y with _ | b
  · exact Or.inl rfl
  · right; simp [totalization, hxy]

/-- Totalization lands in the maxima. -/
theorem totalization_isTotal {X : Type} (s : X → Nat) (c : X → X → Option Bool) :
    isTotal (totalization s c) := by
  intro x y; simp [totalization]

/-- **Totalization is NOT monotone** (witness). Raising an absent input to a present one can send the two
totalizations to incomparable presences: the scale-dictated fill need not match the present value above it. -/
theorem totalization_not_monotone :
    ∃ (c d : Fin 1 → Fin 1 → Option Bool) (s : Fin 1 → Nat),
      cLE c d ∧ ¬ cLE (totalization s c) (totalization s d) := by
  refine ⟨botC (Fin 1), cFalse, (fun _ => 0), botC_le _, ?_⟩
  intro h
  have := h 0 0
  simp [totalization, botC, cFalse, optLE] at this

/-- **Partialization is below its input.** -/
theorem partialization_le_c {X : Type} (w : X → X → Bool) (c : X → X → Option Bool) :
    cLE (partialization w c) c := by
  intro x y
  simp only [partialization]
  by_cases hw : w x y = true
  · rw [if_pos hw]; exact Or.inl rfl
  · rw [if_neg hw]; exact optLE_refl _

/-- **A fill does nothing where nothing is absent.** Totalization keeps present values, so at a
classification that holds everywhere it returns that classification unchanged: the fill arm is the
identity exactly on the total classifications. -/
theorem totalization_fixes_the_total {X : Type} (s : X → Nat) {c : X → X → Option Bool}
    (h : isTotal c) : totalization s c = c := by
  funext x y
  rcases hv : c x y with - | b
  · exact absurd hv (h x y)
  · simp [totalization, hv]

/-- **Partialization IS monotone.** Unlike totalization, this arm is order-preserving. -/
theorem partialization_monotone {X : Type} (w : X → X → Bool) {c d : X → X → Option Bool}
    (h : cLE c d) : cLE (partialization w c) (partialization w d) := by
  intro x y
  simp only [partialization]
  by_cases hw : w x y = true
  · rw [if_pos hw, if_pos hw]; exact Or.inl rfl
  · rw [if_neg hw, if_neg hw]; exact h x y

/-! ## Endpoints: ceiling coincides, floor comes apart -/

/-- **Predicate-ceiling = order-maximal** (restatement of `maximal_iff_total` for the endpoint contrast). -/
theorem ceiling_coincides {X : Type} [DecidableEq X] (c : X → X → Option Bool) :
    isTotal c ↔ (∀ d, cLE c d → cLE d c) := (maximal_iff_total c).symm

/-- **Predicate-floor is not the order-bottom** (witness). The floor predicate (never `some true`) is satisfied
by the all-false classification, which sits strictly above the order-bottom: the two extremes diverge on the
absence axis, unlike the ceiling. -/
theorem floor_predicate_ne_order_bottom :
    (∀ x y, (cFalse : Fin 1 → Fin 1 → Option Bool) x y ≠ some true)
      ∧ cLE (botC (Fin 1)) cFalse ∧ botC (Fin 1) ≠ cFalse := by
  refine ⟨fun _ _ => by simp [cFalse], botC_le _, ?_⟩
  intro h; have := congrFun (congrFun h 0) 0; simp [botC, cFalse] at this

/-! ## Reachability and steps -/

/-- **The downward order IS the partialization image.** `c'` is below `c` exactly when `c'` is a partialization
of `c`: emptying cells generates precisely the information order downward. -/
theorem below_iff_partialization {X : Type} (c c' : X → X → Option Bool) :
    cLE c' c ↔ ∃ w, c' = partialization w c := by
  constructor
  · intro h
    refine ⟨fun x y => decide (c' x y = none), ?_⟩
    funext x y
    by_cases hn : c' x y = none
    · simp [partialization, hn]
    · simp only [partialization, decide_eq_true_eq, if_neg hn]
      rcases h x y with h1 | h1
      · exact absurd h1 hn
      · exact h1
  · rintro ⟨w, rfl⟩; exact partialization_le_c w c

/-- Downward reachability converges to the order-bottom: masking every cell reaches `botC`. -/
theorem full_partialization_is_bot {X : Type} (c : X → X → Option Bool) :
    partialization (fun _ _ => true) c = botC X := by
  funext x y; simp [partialization, botC]

/-- A single-cell fill using totalization's own rule at one position. -/
def fillCell {X : Type} [DecidableEq X] (s : X → Nat) (p : X × X) (c : X → X → Option Bool) :
    X → X → Option Bool :=
  fun x y => if (x, y) = p then some ((c x y).getD (decide (s y ≤ s x))) else c x y

/-- `fillCell` writes exactly totalization's value at its cell. -/
theorem fillCell_at {X : Type} [DecidableEq X] (s : X → Nat) (c : X → X → Option Bool) (p : X × X) :
    fillCell s p c p.1 p.2 = totalization s c p.1 p.2 := by
  simp [fillCell, totalization]

/-- `fillCell` leaves every other cell unchanged: the fill is genuinely single-cell. -/
theorem fillCell_other {X : Type} [DecidableEq X] (s : X → Nat) (c : X → X → Option Bool)
    (p : X × X) (x y : X) (h : (x, y) ≠ p) : fillCell s p c x y = c x y := by
  simp [fillCell, h]

/-- `fillCell` moves up the order (it only fills absences). -/
theorem c_le_fillCell {X : Type} [DecidableEq X] (s : X → Nat) (c : X → X → Option Bool) (p : X × X) :
    cLE c (fillCell s p c) := by
  intro x y
  by_cases h : (x, y) = p
  · rcases hxy : c x y with _ | b
    · exact Or.inl rfl
    · right; simp [fillCell, h, hxy]
  · rw [fillCell_other s c p x y h]; exact optLE_refl _

/-- **Upward reachability is scale-constrained.** From the order-bottom, totalization forces `some true` on the
diagonal, so it cannot reach maxima carrying `some false` there: the up-image is a proper sub-collection of the
maxima, whereas the down-image is the whole down-set. The order is symmetric; the moves are not. -/
theorem totalization_bot_diagonal {X : Type} (s : X → Nat) (x : X) :
    totalization s (botC X) x x = some true := by
  simp [totalization, botC]

/-! ## Fixed points and no-generation -/

/-- **Fixed points of totalization are exactly the total classifications** (the equilibria are the maxima). -/
theorem totalization_fixed_iff_total {X : Type} (s : X → Nat) (c : X → X → Option Bool) :
    totalization s c = c ↔ isTotal c := by
  constructor
  · intro h x y; rw [← h]; simp [totalization]
  · intro htot
    funext x y
    rcases hxy : c x y with _ | b
    · exact absurd hxy (htot x y)
    · simp [totalization, hxy]

/-- Fixed points of partialization are those masking only already-absent cells. -/
theorem partialization_fixed_iff {X : Type} (w : X → X → Bool) (c : X → X → Option Bool) :
    partialization w c = c ↔ ∀ x y, w x y = true → c x y = none := by
  constructor
  · intro h x y hw
    have hh := congrFun (congrFun h x) y
    simp only [partialization, if_pos hw] at hh
    exact hh.symm
  · intro h
    funext x y
    by_cases hw : w x y = true
    · simp only [partialization, if_pos hw]; exact (h x y hw).symm
    · simp only [partialization, if_neg hw]

/-- **No move produces a classification incomparable to its input.** Totalization stays in the up-cone,
partialization in the down-cone: nothing is generated off the order. -/
theorem moves_generate_no_incomparable {X : Type} (s : X → Nat) (w : X → X → Bool)
    (c : X → X → Option Bool) :
    cLE c (totalization s c) ∧ cLE (partialization w c) c :=
  ⟨c_le_totalization s c, partialization_le_c w c⟩

/-! ## The minimal mask

The mask arm's hom-sets are plural, but the plurality collapses in the order: between a classification and
anything below it there is a least mask, and every other mask fires wherever it does. -/

theorem optMeet_self (a : Option Bool) : optMeet a a = a := by
  cases a with
  | none => rfl
  | some x => simp [optMeet]

/-- The canonical mask between two comparable classifications: open exactly the cells that change. -/
def minMask {X : Type} (A B : X → X → Option Bool) : X → X → Bool :=
  fun x y => decide (A x y ≠ none ∧ B x y = none)

/-- **The minimal mask realizes the descent.** Whenever `B` sits below `A`, opening `A` by the minimal mask
gives exactly `B`, so every downward step in the order is a mask arrow. -/
theorem minMask_realizes {X : Type} (A B : X → X → Option Bool) (h : cLE B A) :
    partialization (minMask A B) A = B := by
  rw [mask_hom_iff]
  intro x y
  by_cases hb : B x y = none
  · by_cases ha : A x y = none
    · exact Or.inr ⟨by simp [minMask, ha], by rw [hb, ha]⟩
    · exact Or.inl ⟨by simp [minMask, ha, hb], hb⟩
  · refine Or.inr ⟨by simp [minMask, hb], ?_⟩
    rcases h x y with h1 | h1
    · exact absurd h1 hb
    · exact h1

/-- **And it is least**: every mask carrying `A` to `B` fires wherever the minimal one does. So the hom-set has
a canonical representative and the plurality of `mask_hom_freedom` is removable by choosing it. -/
theorem minMask_least {X : Type} (A B : X → X → Option Bool) (w : X → X → Bool)
    (h : partialization w A = B) (x y : X) (hmin : minMask A B x y = true) : w x y = true := by
  have hd : A x y ≠ none ∧ B x y = none := by simpa [minMask] using hmin
  rcases (mask_hom_iff A B w).1 h x y with ⟨hw, _⟩ | ⟨_, hb⟩
  · exact hw
  · exact absurd (hb.symm.trans hd.2) hd.1

/-! ## Relabelling and the order -/

/-- **Relabelling preserves the order.** A pointwise transport: the relabelled classifications compare cell by
cell exactly as the originals do at the relabelled cells. -/
theorem relabel_preserves_order {X : Type} (σ : X → X) (A B : X → X → Option Bool) (h : cLE A B) :
    cLE (relabel σ A) (relabel σ B) := fun a b => h (σ a) (σ b)

/-- **The kernel of the arrow action, exactly.** Two combined arrows act identically on every classification
iff their masks agree and their carrier maps agree wherever the mask does not fire. Where the mask fires the
carrier map is invisible, which is why `action_not_faithful` holds. -/
theorem act_eq_iff {X : Type} [DecidableEq X] (σ σ' : X → X) (w w' : X → X → Bool) :
    (∀ A : X → X → Option Bool, act (σ, w) A = act (σ', w') A)
      ↔ w = w' ∧ ∀ a b, w a b = false → σ a = σ' a ∧ σ b = σ' b := by
  constructor
  · intro h
    have hw : w = w' := by
      funext a b
      have hc : (if w a b then none else (some true : Option Bool))
          = (if w' a b then none else (some true : Option Bool)) :=
        congrFun (congrFun (h cTrue) a) b
      cases hu : w a b <;> cases hu' : w' a b
      · rfl
      · rw [hu, hu'] at hc; simp at hc
      · rw [hu, hu'] at hc; simp at hc
      · rfl
    subst hw
    refine ⟨rfl, fun a b hf => ⟨?_, ?_⟩⟩
    · have hc : (if w a b then none else some (decide (σ a = σ a)))
          = (if w a b then none else some (decide (σ' a = σ a))) :=
        congrFun (congrFun (h (fun x _ => some (decide (x = σ a)))) a) b
      rw [hf] at hc
      simp at hc
      exact hc.symm
    · have hc : (if w a b then none else some (decide (σ b = σ b)))
          = (if w a b then none else some (decide (σ' b = σ b))) :=
        congrFun (congrFun (h (fun _ y => some (decide (y = σ b)))) a) b
      rw [hf] at hc
      simp at hc
      exact hc.symm
  · rintro ⟨rfl, hσ⟩ A
    funext a b
    show (if w a b then none else A (σ a) (σ b)) = (if w a b then none else A (σ' a) (σ' b))
    by_cases hf : w a b = true
    · rw [hf]; rfl
    · have hf' : w a b = false := by simpa using hf
      have hd := hσ a b hf'
      rw [hf', hd.1, hd.2]

/-! ## The fill at the order bottom

A determiner is any map from a classification to a scale for filling it. Asking that it read the object and not
the labelling is equivariance under the relabelling groupoid. At the order bottom, which every relabelling
fixes, that requirement alone fixes the fill. Stated here as a fact about this construction; no claim is made
that the underlying up-to-automorphism argument is new. -/

/-- A determiner is equivariant when it reads the object rather than the labelling: relabelling the input
relabels the output scale. Quantified over the GROUPOID, so only bijections act. -/
def EquivariantDeterminer {X : Type} (D : (X → X → Option Bool) → (X → Nat)) : Prop :=
  ∀ (e : X ≃ X) (A : X → X → Option Bool), D (relabel e A) = D A ∘ e

/-- At a classification the relabelling fixes, an equivariant determiner outputs an invariant scale. -/
theorem equivariant_determiner_invariant {X : Type} (D : (X → X → Option Bool) → (X → Nat))
    (hD : EquivariantDeterminer D) (e : X ≃ X) (A : X → X → Option Bool) (hA : relabel e A = A) :
    D A ∘ e = D A := by
  rw [← hD e A, hA]

/-- **A transposition already collapses a scale.** Invariance under the two-element swaps alone forces a scale
to be constant, so no larger supply of carrier maps is needed. -/
theorem swap_invariant_scale_constant {X : Type} [DecidableEq X] (s : X → Nat)
    (h : ∀ e : X ≃ X, s ∘ e = s) (x y : X) : s x = s y := by
  have hc : s (Equiv.swap x y x) = s x := congrFun (h (Equiv.swap x y)) x
  rw [Equiv.swap_apply_left] at hc
  exact hc.symm

/-- **The fill at the order bottom is forced.** Every relabelling fixes the empty classification, so an
equivariant determiner must output a constant scale there, and a constant scale fills every cell with the same
verdict. The determiner has no freedom left at the bottom: the outcome is the all-true map whichever determiner
was supplied. Bijections suffice, so this does not depend on admitting arbitrary carrier maps. -/
theorem fill_at_order_bottom_forced {X : Type} [DecidableEq X]
    (D : (X → X → Option Bool) → (X → Nat)) (hD : EquivariantDeterminer D) :
    totalization (D (botC X)) (botC X) = fun _ _ => some true := by
  funext a b
  have hconst : ∀ x y : X, D (botC X) x = D (botC X) y :=
    swap_invariant_scale_constant _ (fun e => equivariant_determiner_invariant D hD e (botC X) rfl)
  simp only [totalization, botC, Option.getD_none]
  rw [hconst b a]
  simp

/-! ## Operator faithfulness of the two arms

`totalization_not_faithful` says the fill loses information about the OBJECT. These say what the two arms do to
their PARAMETER, which is a different question: the open arm's mask is recoverable from the operator, the fill
arm's scale is recoverable only up to the comparison it induces. -/

/-- The parameter is determined by the whole operator when distinct parameters act differently somewhere. -/
def OperatorFaithful {P S : Type} (f : P → S → S) : Prop :=
  ∀ p p' : P, (∀ s, f p s = f p' s) → p = p'

/-- **The open arm is operator-faithful**: the mask is recovered from the operator, tested on the all-present
classification alone. -/
theorem open_operator_faithful {X : Type} : OperatorFaithful
    (partialization : (X → X → Bool) → (X → X → Option Bool) → (X → X → Option Bool)) := by
  intro w w' h
  funext x y
  have hc : (if w x y then none else (some true : Option Bool))
      = (if w' x y then none else (some true : Option Bool)) :=
    congrFun (congrFun (h cTrue) x) y
  cases hw : w x y <;> cases hw' : w' x y
  · rfl
  · rw [hw, hw'] at hc; simp at hc
  · rw [hw, hw'] at hc; simp at hc
  · rfl

/-- **The fill arm is faithful exactly up to the comparison it induces.** Two scales give the same operator iff
they order every pair the same way, so the operator determines the ordering of the carrier and nothing more.
Which scale supplies it is partly a non-question: only the comparison is at stake. -/
theorem fill_operator_ext_iff {X : Type} (s s' : X → Nat) :
    (∀ c : X → X → Option Bool, totalization s c = totalization s' c)
      ↔ ∀ x y, decide (s y ≤ s x) = decide (s' y ≤ s' x) := by
  constructor
  · intro h x y
    have hc : totalization s (botC X) x y = totalization s' (botC X) x y :=
      congrFun (congrFun (h (botC X)) x) y
    simpa [totalization, botC] using hc
  · intro h c
    funext x y
    simp only [totalization, h x y]

/-! ## The single-cell fill algebra -/

/-- **Fills at different cells commute exactly.** Each cell receives its own scale's verdict, so the order in
which two single-cell fills are applied is irrelevant. -/
theorem fills_at_different_cells_commute {X : Type} [DecidableEq X] (s s' : X → Nat) (p q : X × X)
    (hpq : p ≠ q) (c : X → X → Option Bool) :
    fillCell s q (fillCell s' p c) = fillCell s' p (fillCell s q c) := by
  funext x y
  by_cases hq : (x, y) = q
  · have hp : ¬ ((x, y) = p) := by rw [hq]; exact fun h => hpq h.symm
    simp only [fillCell, if_pos hq, if_neg hp]
  · by_cases hp : (x, y) = p
    · simp only [fillCell, if_pos hp, if_neg hq]
    · simp only [fillCell, if_neg hp, if_neg hq]

/-- **Fills at the same cell absorb, and the first one wins.** The second fill finds the cell present and
leaves it alone, so the two single-cell fills fail to commute only at a shared cell. -/
theorem fills_at_same_cell_absorb {X : Type} [DecidableEq X] (s s' : X → Nat) (p : X × X)
    (c : X → X → Option Bool) :
    fillCell s p (fillCell s' p c) = fillCell s' p c := by
  funext x y
  by_cases hp : (x, y) = p
  · simp only [fillCell, if_pos hp, Option.getD_some]
  · simp only [fillCell, if_neg hp]

end Chiralogy
