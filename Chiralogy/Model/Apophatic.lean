import Chiralogy.Kernel.Apophatic
import Chiralogy.Kernel.Center

/-! # Model: the apophatic model (unique)

The canonical extension `Kl(Maybe)`: keep-the-none. `Option` is the monad; `payload_survives` and
`maybe_free_pointed` characterize the free adjunction of one absence; `imprecise_is_partial_mode` occupies
the partial pole. The two cost-inverted moves are `totalization` (fill the none, target-free cost) and
`partialization` (open one, target-dependent), with `totalization_irreversible` the non-invertible move. The
none-chiasm: the two arms invert at the none (`model_arms_invert`), whose center is distinct from the kernel
hole (`model_center_is_the_none`). -/

namespace Chiralogy

/-- The extension is the Kleisli category of `Maybe` on the distinction space. -/
example : Monad Option := inferInstance

/-- **The payload survives the extension.** A partial classification is still not surjective. -/
theorem payload_survives {X : Type} (c : X → X → Option Bool) : ¬ Function.Surjective c :=
  hole_uniform c

/-- A constitutively partial object: incomparable options, ranked by their own incommensurable lights. -/
def imprecise : Fin 4 → Fin 4 → Option Bool := fun i j =>
  if i = 0 ∧ j = 1 then some true
  else if i = 1 ∧ j = 0 then some false
  else if i = 2 ∧ j = 3 then some true
  else if i = 3 ∧ j = 2 then some false
  else none

/-- The partial mode: a non-degenerate classification with a constitutive absence. -/
theorem imprecise_is_partial_mode :
    NonDegenerate imprecise ∧ ∃ x y, imprecise x y = none := by
  refine ⟨⟨0, 2, fun h => ?_⟩, 0, 2, by decide⟩
  exact absurd (congrFun h 1) (by decide)

/-- A total classification embeds via `some` and never abstains: the total instances sit at the
no-absence pole; a `some ∘ f` value is present, not an absence. -/
theorem total_never_abstains {X : Type} (f : X → X → Bool) (x y : X) :
    (fun a b => some (f a b)) x y ≠ none := by simp

/-- **Maybe is the free pointed object.** For a point `pt : C` and a map `f : B → C`, there is a unique
pointed extension `Option B → C` sending `none` to `pt` and `some b` to `f b`. This universal property
characterizes `B + 1` as the free object with a distinguished point, the canonical codomain extension. -/
theorem maybe_free_pointed {B C : Type} (pt : C) (f : B → C) :
    ∃! g : Option B → C, g none = pt ∧ ∀ b, g (some b) = f b := by
  refine ⟨fun o => o.elim pt f, ⟨rfl, fun _ => rfl⟩, ?_⟩
  rintro g ⟨hnone, hsome⟩
  funext o
  cases o with
  | none => exact hnone
  | some b => exact hsome b


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

/-- Totalization fabricates: it fills a constitutive absence with a scale-dependent verdict: two scales
give opposite verdicts. -/
theorem totalization_fabricates :
    ∃ s s' : Fin 4 → Nat, totalization s imprecise 0 2 ≠ totalization s' imprecise 0 2 :=
  ⟨(fun _ => 0), (fun i => if i = 2 then 1 else 0), by decide⟩

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

/-- A false assertion against a target: a present verdict that contradicts it. -/
def assertsFalse {X : Type} (c : X → X → Option Bool) (t : X → X → Bool) (x y : X) : Prop :=
  ∃ b, c x y = some b ∧ b ≠ t x y

/-- **Partialization asserts no falsehood, against any target.** It only removes verdicts; an absence
makes no claim. -/
theorem partialization_asserts_no_falsehood {X : Type} (w : X → X → Bool)
    (c : X → X → Option Bool) (t : X → X → Bool) (x y : X) :
    assertsFalse (partialization w c) t x y → assertsFalse c t x y := by
  rintro ⟨b, hb, hne⟩
  simp only [partialization] at hb
  by_cases hw : w x y
  · rw [if_pos hw] at hb; simp at hb
  · rw [if_neg hw] at hb; exact ⟨b, hb, hne⟩

/-- **Totalization falsifies against every target.** At the constitutive absence of `imprecise`, whatever
the target says, one of the two scale-verdicts contradicts it: a target-free cost. -/
theorem totalization_falsifies_against_every_target (t : Fin 4 → Fin 4 → Bool) :
    assertsFalse (totalization (fun _ => 0) imprecise) t 0 2 ∨
      assertsFalse (totalization (fun i => if i = 2 then 1 else 0) imprecise) t 0 2 := by
  cases h : t 0 2
  · exact Or.inl ⟨true, by decide, by rw [h]; decide⟩
  · exact Or.inr ⟨false, by decide, by rw [h]; decide⟩

/-- **The model's two arms invert at the none.** Totalization fills a none (none ↦ some) and partialization
opens one (some ↦ none): opposite directions on the none-axis, exhibited on one object. Their costs invert:
totalization falsifies against every target (target-free), partialization asserts no falsehood against any
target (target-dependent). Two distinct arms, not one move twice. -/
theorem model_arms_invert :
    (∃ (s : Fin 4 → Nat) (w : Fin 4 → Fin 4 → Bool),
        (imprecise 0 2 = none ∧ totalization s imprecise 0 2 ≠ none) ∧
        (imprecise 0 1 ≠ none ∧ partialization w imprecise 0 1 = none)) ∧
    (∀ t : Fin 4 → Fin 4 → Bool,
        assertsFalse (totalization (fun _ => 0) imprecise) t 0 2 ∨
          assertsFalse (totalization (fun i => if i = 2 then 1 else 0) imprecise) t 0 2) ∧
    (∀ (w : Fin 4 → Fin 4 → Bool) (c : Fin 4 → Fin 4 → Option Bool)
        (t : Fin 4 → Fin 4 → Bool) (x y : Fin 4),
        assertsFalse (partialization w c) t x y → assertsFalse c t x y) :=
  ⟨⟨fun _ => 0, fun x y => decide (x = 0 ∧ y = 1),
      ⟨⟨by decide, totalization_totalizes _ _ 0 2⟩, ⟨by decide, by decide⟩⟩⟩,
   totalization_falsifies_against_every_target,
   fun w c t x y => partialization_asserts_no_falsehood w c t x y⟩

/-- **The model center is the none.** Both arms pivot on the constitutive absence: totalization changes
only the none entries (present verdicts pass through), and partialization's product is a none. This center
is distinct from the kernel hole: a total object carries the hole with no none (`ethical_center_is_distinct`). -/
theorem model_center_is_the_none :
    (∀ (X : Type) (s : X → Nat) (c : X → X → Option Bool) (x y : X) (b : Bool),
        c x y = some b → totalization s c x y = some b) ∧
    (∀ (X : Type) (w : X → X → Bool) (c : X → X → Option Bool) (x y : X),
        w x y = true → partialization w c x y = none) ∧
    (∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ ¬ Function.Surjective c) := by
  refine ⟨fun X s c x y b h => ?_, fun X w c x y h => ?_, ethical_center_is_distinct⟩
  · simp [totalization, h]
  · simp [partialization, h]

/-- Copy is available on every distinction space in a cartesian base: the diagonal is unconditional. This
is the root of both collapses, and the diagonal the obstructions use. -/
def copy {B : Type} (b : B) : B × B := (b, b)

theorem copy_is_free (B : Type) (b : B) : copy b = (b, b) := rfl

/-- A stochastic distinction space collapses to a codomain enrichment: a classification into any space `D`
is a plain map subject to the same hole. Determinism is not a separate axis: the map into `D` is the
extension. -/
theorem stochastic_collapses {X D : Type} {g : D → D} (hg : ∀ d, g d ≠ d)
    (c : X → X → D) : ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-- A substructural (tensor) distinction space has copy in a cartesian base, so the tensor is the product:
the additive/multiplicative distinction is invisible. -/
theorem tensor_has_copy {B C : Type} (p : B × C) : copy p = (p, p) := rfl

/-- **The diagonal that makes the hole closes the codomain axis.** The diagonal argument duplicates its
argument: it factors through copy. In a base without copy the argument cannot be built. -/
theorem diagonal_factors_through_copy {X Y : Type} (f : X → X → Y) :
    (fun x => f x x) =
      (fun p : (X → Y) × X => p.1 p.2) ∘ (Prod.map f id) ∘ (@copy X) := by
  funext x; rfl

theorem the_diagonal_is_copy {X : Type} : (fun x : X => (x, x)) = (@copy X) := rfl


/-- Comparability: an edge iff the pair is classified (not absent). The free arrangement lives here. -/
def Comparable {X : Type} (c : X → X → Option Bool) (x y : X) : Prop := c x y ≠ none

/-- **Federation.** The comparability graph of `imprecise` splits into two components: blocks `{0,1}` and
`{2,3}` are internally comparable, with no comparability between them. -/
theorem comparability_federates :
    Comparable imprecise 0 1 ∧ Comparable imprecise 2 3 ∧
      (∀ i j : Fin 4, (i = 0 ∨ i = 1) → (j = 2 ∨ j = 3) →
        imprecise i j = none ∧ imprecise j i = none) := by
  refine ⟨?_, ?_, ?_⟩
  · show imprecise 0 1 ≠ none; decide
  · show imprecise 2 3 ≠ none; decide
  · decide

/-- A partial object whose comparability graph has a cut-vertex. -/
def vshape : Fin 3 → Fin 3 → Option Bool := fun i j =>
  if i = 0 ∧ j = 1 then some true
  else if i = 1 ∧ j = 0 then some false
  else if i = 0 ∧ j = 2 then some true
  else if i = 2 ∧ j = 0 then some false
  else none

/-- **Cut-vertex.** In `vshape`, `1` and `2` are each comparable to `0` but incomparable to each other:
removing `0` disconnects them. A free structural hub. -/
theorem comparability_has_cut_vertex :
    vshape 0 1 ≠ none ∧ vshape 0 2 ≠ none ∧ vshape 1 2 = none ∧ vshape 2 1 = none :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **Trivial on total objects.** A total classification is comparable everywhere: the comparability graph
is complete (the terminal product), carrying no free arrangement. -/
theorem total_comparability_complete {X : Type} (f : X → X → Bool) (x y : X) :
    Comparable (fun a b => some (f a b)) x y := by
  simp [Comparable]


/-- A cyclic classification: `0` over `1` over `2` over `0`: each pair ranked, the order inconsistent. -/
def cyclic : Fin 3 → Fin 3 → Option Bool := fun x y =>
  if x = y then none
  else if y = x + 1 then some true
  else some false

/-- The cycle: each pair is ranked, the order inconsistent. -/
theorem cyclic_witness :
    cyclic 0 1 = some true ∧ cyclic 1 2 = some true ∧ cyclic 2 0 = some true :=
  ⟨by decide, by decide, by decide⟩

/-- The cycle needs no absence: it is comparable everywhere off the diagonal. -/
theorem cyclic_is_total : ∀ x y : Fin 3, x ≠ y → cyclic x y ≠ none := by decide

/-- The coherence content: no maximum: every element is beaten by another, no global order though every
pairwise verdict is present. -/
theorem cyclic_no_maximum : ∀ x : Fin 3, ∃ y, cyclic y x = some true := by decide

/-- A transitive order, for the separation. -/
def linear : Fin 3 → Fin 3 → Option Bool := fun x y =>
  if x = y then none else if x < y then some true else some false

/-- **The cycle is not the hole.** The transitive order carries the hole yet has no 3-cycle: the hole does
not entail the cycle. So the cycle is arity-3 among distinct elements: it routes through neither
obstruction. -/
theorem cycle_is_not_the_hole :
    (¬ Function.Surjective linear) ∧
      (¬ ∃ a b c : Fin 3, linear a b = some true ∧ linear b c = some true ∧ linear c a = some true) :=
  ⟨hole_uniform linear, by decide⟩

/-- Both maps carry the hole; only one cycles: coherence-failure and incompleteness are independent. -/
theorem cyclic_also_has_hole : ¬ Function.Surjective cyclic :=
  hole_uniform cyclic

/-- Comparability transitivity is measure-free: a decidable first-order relational condition, no count. -/
def intransitivity_is_measure_free (c : Fin 3 → Fin 3 → Option Bool) :
    Decidable (∀ x y z : Fin 3, Comparable c x y → Comparable c y z → Comparable c x z) := by
  unfold Comparable; infer_instance

end Chiralogy
