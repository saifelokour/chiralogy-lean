import Chiralogy.Kernel.Apophatic

/-! # The two moves

The two operations on classifications `X → X → Option Bool`: `totalization` fills each absence with a scale
verdict (none to some), `partialization` withdraws marked verdicts (some to none). Extracted from `Model/Apophatic`
in the per-module-purity refactor: the moves cluster with the downstream dynamics community (the information order,
the n-ary assemblage, the assemblage dynamics and relations) that consumes them, a consumer base that did not exist
before those modules were graduated. This module holds the moves and the lemmas depending only on them; the
move-lemmas that also use the absence-carried shelf (`presentCarried`) or the model material (`imprecise`, `assertsFalse`)
stay in `Model/Apophatic`, which imports this module. -/

namespace Chiralogy

/-- Totalization: fill each absence with a scale verdict, keeping the present ones. -/
def totalization {X : Type} (s : X → Nat) (c : X → X → Option Bool) : X → X → Option Bool :=
  fun x y => some ((c x y).getD (decide (s y ≤ s x)))

theorem totalization_totalizes {X : Type} (s : X → Nat) (c : X → X → Option Bool) :
    ∀ x y, totalization s c x y ≠ none := by
  intro x y; simp [totalization]

/-- Totalization does not reach completeness: the totalized map still carries the hole. -/
theorem totalization_hole {X : Type} (s : X → Nat) (c : X → X → Option Bool) :
    ¬ Function.Surjective (totalization s c) :=
  hole_uniform (totalization s c)

/-- **Totalization is not faithful.** Two different partial maps totalize to the same map. -/
theorem totalization_not_faithful :
    ∃ c c' : Fin 2 → Fin 2 → Option Bool,
      c ≠ c' ∧ totalization (fun _ => 0) c = totalization (fun _ => 0) c' :=
  ⟨(fun _ _ => none), (fun x y => if x = 0 ∧ y = 1 then some true else none), by decide, by decide⟩

/-- **Totalization is irreversible.** No operation recovers the original from the totalized map. -/
theorem totalization_irreversible :
    ¬ ∃ recover : (Fin 2 → Fin 2 → Option Bool) → (Fin 2 → Fin 2 → Option Bool),
        ∀ c, recover (totalization (fun _ => 0) c) = c := by
  rintro ⟨recover, h⟩
  obtain ⟨c, c', hne, heq⟩ := totalization_not_faithful
  exact hne (by rw [← h c, heq, h c'])

/-- Partialization: withdraw the marked verdicts. -/
def partialization {X : Type} (w : X → X → Bool) (c : X → X → Option Bool) : X → X → Option Bool :=
  fun x y => if w x y then none else c x y

/-- **Totalization separates equal rows exactly through a split fill.** Two rows equal before totalization become
distinct after when they share an absence at a pair where the scale sends the fill different ways,
`decide (s y ≤ s x) ≠ decide (s y ≤ s x')`: at that pair the totalization gives different filled values. -/
theorem totalization_separates_equal_rows {X : Type} (c : X → X → Option Bool) (s : X → Nat) (x x' : X) :
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

/-- **Opening is monotone on distinction.** Opening by a column-uniform mask never separates equal rows: the fill is
the parameterless absence, so on a column it maps both rows the same way. Partialization increases distinction only
through a row-discriminating mask, never through its fill. -/
theorem opening_is_monotone_on_distinction {X : Type} (wc : X → Bool)
    (c : X → X → Option Bool) (x x' : X) :
    c x = c x' → partialization (fun _ y => wc y) c x = partialization (fun _ y => wc y) c x' := by
  intro h; funext y; simp only [partialization, congrFun h y]

/-! ## Relabelling

The third operation on classifications, alongside the two moves: pull a classification back along a carrier
map. Canonical `absenceCarried_relabel` and `absenceCarriedCount_relabel` are already stated about this
operation, where it appears inlined and unnamed; naming it is what lets the moves and the relabellings compose
into a single algebra. -/

/-- Relabelling: pull a classification back along a carrier map. -/
def relabel {X : Type} (σ : X → X) (A : X → X → Option Bool) : X → X → Option Bool :=
  fun a b => A (σ a) (σ b)

/-- Relabelling a mask along the same carrier map. -/
def relabelW {X : Type} (σ : X → X) (w : X → X → Bool) : X → X → Bool :=
  fun a b => w (σ a) (σ b)

theorem relabel_id {X : Type} (A : X → X → Option Bool) : relabel id A = A := rfl

theorem relabel_comp {X : Type} (σ τ : X → X) (A : X → X → Option Bool) :
    relabel σ (relabel τ A) = relabel (τ ∘ σ) A := rfl

theorem relabelW_comp {X : Type} (σ τ : X → X) (w : X → X → Bool) :
    relabelW σ (relabelW τ w) = relabelW (τ ∘ σ) w := rfl

theorem relabelW_or {X : Type} (σ : X → X) (w w' : X → X → Bool) :
    relabelW σ (fun a b => w a b || w' a b)
      = (fun a b => relabelW σ w a b || relabelW σ w' a b) := rfl

/-- **The relabelling is forced, not chosen.** Among operations that read each cell of the relabelled object
off a single cell of the original, selected coordinatewise, only precomposition by the same map in both
arguments reproduces the action. So there is no alternative to choose between. -/
theorem relabel_unique {X : Type} [DecidableEq X] (σ u v : X → X)
    (h : ∀ (A : X → X → Option Bool) (a b : X), A (u a) (v b) = A (σ a) (σ b)) (a b : X) :
    u a = σ a ∧ v b = σ b := by
  by_contra hu
  have hc := h (fun x y => if x = σ a ∧ y = σ b then some true else none) a b
  rw [if_neg hu, if_pos (show σ a = σ a ∧ σ b = σ b from ⟨rfl, rfl⟩)] at hc
  exact absurd hc.symm (Option.some_ne_none true)

/-! ## The open arm accumulates -/

/-- **Two maskings are one masking**, by the pointwise `or`. The open arm accumulates rather than iterating. -/
theorem partialization_union {X : Type} (w w' : X → X → Bool) (c : X → X → Option Bool) :
    partialization w (partialization w' c) = partialization (fun x y => w x y || w' x y) c := by
  funext x y
  cases hw : w x y <;> cases hw' : w' x y <;> simp [partialization, hw, hw']

/-- The all-false mask is the identity of the open arm. -/
theorem partialization_id {X : Type} (c : X → X → Option Bool) :
    partialization (fun _ _ => false) c = c := by
  funext x y; simp [partialization]

/-! ## The transport laws

Both moves are relabelling-equivariant, and both laws hold by computation: they are identities already present
at every carrier, not conditions imposed on the structure. -/

/-- **The open arm transports.** Relabelling then masking equals masking by the transported mask then
relabelling. -/
theorem transport_law {X : Type} (σ : X → X) (w : X → X → Bool) (A : X → X → Option Bool) :
    relabel σ (partialization w A) = partialization (relabelW σ w) (relabel σ A) := rfl

/-- **The fill arm transports too**, with the scale carried along the relabelling. -/
theorem transport_law_fill {X : Type} (σ : X → X) (s : X → Nat) (A : X → X → Option Bool) :
    relabel σ (totalization s A) = totalization (s ∘ σ) (relabel σ A) := rfl

/-! ## The combined arrows

A relabelling followed by a masking. The composition law is forced by the transport law: the outer mask unions
with the transported inner mask and the carrier maps compose. Nothing in it is chosen. -/

/-- A combined arrow: relabel, then mask. -/
abbrev Arrow (X : Type) := (X → X) × (X → X → Bool)

/-- The action of a combined arrow on a classification. -/
def act {X : Type} (p : Arrow X) (A : X → X → Option Bool) : X → X → Option Bool :=
  partialization p.2 (relabel p.1 A)

/-- Composition, dictated by `transport_law` clause by clause. -/
def arrowComp {X : Type} (p q : Arrow X) : Arrow X :=
  (q.1 ∘ p.1, fun a b => p.2 a b || relabelW p.1 q.2 a b)

def arrowId (X : Type) : Arrow X := (id, fun _ _ => false)

theorem act_id {X : Type} (A : X → X → Option Bool) : act (arrowId X) A = A := by
  funext a b; simp [act, arrowId, partialization, relabel]

/-- **The action law.** The composite arrow acts as the composite of the actions, derived from the transport
law together with mask-union and relabel-composition. -/
theorem act_comp {X : Type} (p q : Arrow X) (A : X → X → Option Bool) :
    act (arrowComp p q) A = act p (act q A) := by
  show partialization (fun a b => p.2 a b || relabelW p.1 q.2 a b) (relabel (q.1 ∘ p.1) A)
    = partialization p.2 (relabel p.1 (partialization q.2 (relabel q.1 A)))
  rw [transport_law, relabel_comp, partialization_union]

theorem arrowComp_id_left {X : Type} (p : Arrow X) : arrowComp (arrowId X) p = p := by
  refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
  funext a b
  simp [arrowComp, arrowId, relabelW]

theorem arrowComp_id_right {X : Type} (p : Arrow X) : arrowComp p (arrowId X) = p := by
  refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
  funext a b
  simp [arrowComp, arrowId, relabelW]

/-- **Composition is associative**, so the combined arrows form a monoid acting on classifications. The proof
uses only that carrier maps compose, that masks union associatively, and that relabelling distributes over the
union. -/
theorem arrowComp_assoc {X : Type} (p q r : Arrow X) :
    arrowComp (arrowComp p q) r = arrowComp p (arrowComp q r) := by
  refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
  funext a b
  exact Bool.or_assoc _ _ _

/-! ### The category on classifications -/

/-- An arrow of the combined category, packaged with its source and target. -/
structure Arr {X : Type} (A B : X → X → Option Bool) where
  par : Arrow X
  eq : act par A = B

theorem Arr.par_ext {X : Type} {A B : X → X → Option Bool} {f g : Arr A B}
    (h : f.par = g.par) : f = g := by
  cases f; cases g; simp only [Arr.mk.injEq]; exact h

def arrId {X : Type} (A : X → X → Option Bool) : Arr A A := ⟨arrowId X, act_id A⟩

def arrComp {X : Type} {A B C : X → X → Option Bool} (g : Arr B C) (f : Arr A B) : Arr A C :=
  ⟨arrowComp g.par f.par, by rw [act_comp, f.eq, g.eq]⟩

/-- **The category laws hold on the packaged arrows**, so the combined structure is a genuine category on
classifications and not a collection of scattered lemmas. -/
theorem arr_id_left {X : Type} {A B : X → X → Option Bool} (f : Arr A B) :
    arrComp (arrId B) f = f :=
  Arr.par_ext (arrowComp_id_left f.par)

theorem arr_id_right {X : Type} {A B : X → X → Option Bool} (f : Arr A B) :
    arrComp f (arrId A) = f :=
  Arr.par_ext (arrowComp_id_right f.par)

theorem arr_assoc {X : Type} {A B C D : X → X → Option Bool} (h : Arr C D) (g : Arr B C) (f : Arr A B) :
    arrComp (arrComp h g) f = arrComp h (arrComp g f) :=
  Arr.par_ext (arrowComp_assoc h.par g.par f.par)

/-- **The hom-set, characterized cellwise.** A pair is an arrow from `A` to `B` exactly when at every cell it
either fires and `B` abstains, or does not fire and `B` reads the relabelled `A`. -/
theorem act_hom_iff {X : Type} (A B : X → X → Option Bool) (σ : X → X) (w : X → X → Bool) :
    act (σ, w) A = B
      ↔ ∀ a b, (w a b = true ∧ B a b = none) ∨ (w a b = false ∧ B a b = A (σ a) (σ b)) := by
  constructor
  · intro h a b
    have hc : (if w a b then none else A (σ a) (σ b)) = B a b := congrFun (congrFun h a) b
    cases hw : w a b
    · rw [hw] at hc; exact Or.inr ⟨rfl, by simpa using hc.symm⟩
    · rw [hw] at hc; exact Or.inl ⟨rfl, by simpa using hc.symm⟩
  · intro h
    funext a b
    rcases h a b with ⟨hw, hb⟩ | ⟨hw, hb⟩ <;>
      simp [act, partialization, relabel, hw, hb]

/-- **The action is not faithful.** With the all-firing mask every carrier map acts alike, because the mask
hides the whole classification. -/
theorem action_not_faithful {X : Type} (σ σ' : X → X) (A : X → X → Option Bool) :
    act (σ, fun _ _ => true) A = act (σ', fun _ _ => true) A := by
  funext a b
  simp [act, partialization]

/-! ## The mask arm as a category, and the fill arm's failure to be one -/

/-- **The mask hom-set, characterized cellwise.** A mask carries `A` to `B` exactly when at each cell it either
fires and `B` abstains, or does not fire and `B` agrees with `A`. -/
theorem mask_hom_iff {X : Type} (A B : X → X → Option Bool) (w : X → X → Bool) :
    partialization w A = B
      ↔ ∀ x y, (w x y = true ∧ B x y = none) ∨ (w x y = false ∧ B x y = A x y) := by
  constructor
  · intro h x y
    have hc : partialization w A x y = B x y := congrFun (congrFun h x) y
    cases hw : w x y
    · refine Or.inr ⟨rfl, ?_⟩
      have hv : partialization w A x y = A x y := by simp [partialization, hw]
      exact hc.symm.trans hv
    · refine Or.inl ⟨rfl, ?_⟩
      have hv : partialization w A x y = none := by simp [partialization, hw]
      exact hc.symm.trans hv
  · intro h
    funext x y
    rcases h x y with ⟨hw, hb⟩ | ⟨hw, hb⟩ <;> simp [partialization, hw, hb]

/-- **Mask arrows are plural, but only where both ends already abstain.** Two masks carrying `A` to `B` differ
only at cells absent in both: the extra masks open cells that are open already. -/
theorem mask_hom_freedom {X : Type} (A B : X → X → Option Bool) (w w' : X → X → Bool)
    (h : partialization w A = B) (h' : partialization w' A = B) (x y : X)
    (hne : w x y ≠ w' x y) : A x y = none ∧ B x y = none := by
  rcases (mask_hom_iff A B w).1 h x y with ⟨hw, hb⟩ | ⟨hw, hb⟩ <;>
    rcases (mask_hom_iff A B w').1 h' x y with ⟨hw', hb'⟩ | ⟨hw', hb'⟩
  · exact absurd (hw.trans hw'.symm) hne
  · exact ⟨hb'.symm.trans hb, hb⟩
  · exact ⟨hb.symm.trans hb', hb'⟩
  · exact absurd (hw.trans hw'.symm) hne

/-- **The fill arm has no identity arrow at any object carrying an absence**, because a fill is total. So the
fills do not form a category on their own; only the mask arm does, and that asymmetry is the categorical form
of the two arms' asymmetry. -/
theorem fill_has_no_identity {X : Type} (A : X → X → Option Bool) (x y : X) (h : A x y = none)
    (s : X → Nat) : totalization s A ≠ A := by
  intro he
  have hc : totalization s A x y = A x y := congrFun (congrFun he x) y
  rw [h] at hc
  exact absurd hc (by simp [totalization])

/-! ## Nondegeneracy under fills -/

/-- Two rows, each present exactly where the other abstains, carrying `some false`. Every distinction it
carries is absence-carried. -/
def cResist : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some false else none

/-- **Absence of presence-protection does not imply destroyability.** `cResist` has every distinction
absence-carried, yet EVERY scale leaves it non-degenerate: to merge the two rows a scale would have to order
the two points both ways at once. So the scale's own consistency protects what presence does not, and the
converse of presence-protection is false. -/
theorem nondegeneracy_survives_every_fill (s : Fin 2 → Nat) :
    NonDegenerate (totalization s cResist) := by
  refine ⟨0, 1, fun h => ?_⟩
  by_cases hs : s 0 ≤ s 1
  · have h0 := congrFun h 0
    simp [totalization, cResist, hs] at h0
  · have h1 := congrFun h 1
    have hs' : s 1 ≤ s 0 := by omega
    simp [totalization, cResist, hs'] at h1

end Chiralogy
