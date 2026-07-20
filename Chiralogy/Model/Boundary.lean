import Chiralogy.Model.Apophatic
import Chiralogy.Model.Cataphatic
import Chiralogy.Model.Cataphatic.Instances
import Chiralogy.Kernel.Center
import Chiralogy.Kernel.Apophatic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators

/-! # Model: the boundary between the arms (limit, seam, channel)

First of the interface pair. The in-between where the two arms meet at a limit and communicate, connected not
fused; everything here quantifies a bare classification. The ethics on the declared grounds, the permitted
lattice and the departure space, is the second half, `Permitted`.

The one prohibition: `complete_and_faithful_is_impossible` (the limit where none and surplus are co-located),
`completeness_is_unreachable`, `totalization_is_self_defeating`, and the reachable/handed-back results. The
braid: `boundary_braids_both_absences` and `the_open_seam` bring the kernel hole and the model none into
contact; `double_chiasm_does_not_compose` shows the two chiasms share no generator. The channel: a proposed
account (`proposedAccount`) flows cataphatic to apophatic, the guard bounding it (`proposer_guard`,
`guard_is_universal`), one-way (`fold_then_build_ignores_guard`); it certifies rather than informs
(`guard_erases`, `channel_capacity_is_zero`, `channel_is_certification`), judgement constant
(`judgement_is_constant`). The two obstructions are distinct (`none_and_surplus_are_distinct`) and the ethical
move is apophatic-shaped (`ethical_is_apophatic_shaped`); the arms are related by the absorbing axiom, not a map
(`axiom_relates_the_arms`, `not_a_morphism`). -/

namespace Chiralogy

/-- **Completeness is unreachable.** The success condition of the totalizing attempt, a surjective
self-classification, is provably unsatisfiable. -/
theorem completeness_is_unreachable {X : Type} (c : X → X → Option Bool) :
    ¬ Function.Surjective c :=
  hole_uniform c

/-- **The internal contradiction.** A total map that is also faithful to a constitutive absence is impossible:
totality needs a verdict where faithfulness needs the absence, by the move's own goal. This is the base instance
of `boundary_collision` (`base_collision_is_generic`), binary at the base and a spectrum above (see `Permitted`,
where only full totality collides). -/
theorem complete_and_faithful_is_impossible :
    ¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2 := by
  rintro ⟨c, htotal, hfaithful⟩
  rw [show imprecise (0 : Fin 4) 2 = none from by decide] at hfaithful
  exact htotal 0 2 hfaithful

/-- **Totalization is self-defeating.** It fills the absences yet the totalized map still carries the hole: its
own success condition fails. -/
theorem totalization_is_self_defeating {X : Type} (s : X → Nat) (c : X → X → Option Bool) :
    (∀ x y, totalization s c x y ≠ none) ∧ ¬ Function.Surjective (totalization s c) :=
  ⟨totalization_totalizes s c, totalization_hole s c⟩

/-! ## The arms are related by axioms, not maps

`same_signature_different_arity` places the apophatic constant and a cataphatic operation in one signature. An
axiom is not a morphism; the absorbing law relates what the arms read without crossing them. -/

/-- A second operation, reversed on the present part, also absorbing `none`. -/
def mzAppend' : Option (List Bool) → Option (List Bool) → Option (List Bool)
  | none, _ => none
  | _, none => none
  | some a, some b => some (b ++ a)

/-- **The axiom relates the arms, one-directionally.** `none` is the unique left-absorbing element under
`mzAppend`, so the operation pins the constant; but two distinct operations share the absorbing constant, so the
constant does not pin the operation. -/
theorem axiom_relates_the_arms :
    (∀ z : Option (List Bool), (∀ x, mzAppend z x = z) → z = none)
    ∧ (∀ x, mzAppend' none x = none) ∧ mzAppend ≠ mzAppend' := by
  refine ⟨?_, fun _ => rfl, fun h => ?_⟩
  · intro z h; cases z with
    | none => rfl
    | some a => have := h none; simp [mzAppend] at this
  · have := congrFun (congrFun h (some [true])) (some [false]); simp [mzAppend, mzAppend'] at this

/-- **Not a morphism.** The absorbing law is an equation on one carrier between `none` (arity 0) and `mzAppend`
(arity 2), not a map: sharing it does not fuse the arms (`loop_does_not_close`). -/
theorem not_a_morphism :
    (∀ x : Option (List Bool), mzAppend none x = none)
    ∧ (Nonempty (Monad Option) ∧ ¬ Function.Surjective (embed (ZMod 3))) :=
  ⟨fun _ => rfl, loop_does_not_close⟩

/-! ## The channel: proposer, guard, certification

A proposed account flows cataphatic to apophatic; the guard bounds it, one-way, certifying rather than
informing. -/

/-- The proposer. A cataphatic construction whose ambient is the account space `X → B`: it proposes a candidate
self-classification in transpose form. Free. -/
def proposedAccount {X B : Type} (build : X → (X → B)) : CataphaticConformant := ⟨X, X → B, build⟩

/-- **The guard bounds the proposal, on the term.** Idolatry-detection fires on the proposer's own output: if
the proposed account were totalized it is refuted, the built account itself the argument, so this is data-flow,
not a function between the arms. -/
theorem proposer_guard {X B : Type} (build : X → (X → B)) {g : B → B} (hg : ∀ b, g b ≠ b) :
    ¬ Function.Surjective (proposedAccount build).build :=
  no_reflexive_object hg build

/-- **The guard is universal.** It bounds any account, not only proposed ones: a division of labor, a free
proposer met by a guard ready for any proposal. -/
theorem guard_is_universal {X B : Type} (c : X → X → B) {g : B → B} (hg : ∀ b, g b ≠ b) :
    ¬ Function.Surjective c :=
  no_reflexive_object hg c

/-- **Fold-then-build does not exist.** The guard's output is a `Prop`, proof-irrelevant, so any map from it is
constant: the refutation carries nothing to build from. The asymmetry is the type signature, `Type` into `Prop`
but not back. -/
theorem fold_then_build_ignores_guard {X B : Type} (c : X → X → B)
    (F : ¬ Function.Surjective c → CataphaticConformant) (h₁ h₂ : ¬ Function.Surjective c) :
    F h₁ = F h₂ := rfl

/-- **The two arms are adjacent, not crossed.** The apophatic hole and the cataphatic transpose hold together
from one `c`, joined by `∧`, not by a between-arms function: bicameral, not chiastic. -/
theorem two_adjacent_arms {X B : Type} (c : X → X → B) :
    (∀ g : B → B, (∀ b, g b ≠ b) → ¬ Function.Surjective c) ∧ (∃ build : X → (X → B), ∀ x, build x = c x) :=
  one_map_two_ends c

/-- **Erasure.** The guard's verdict is a `Prop`, hence proof-irrelevant: any two proofs are equal. -/
theorem guard_erases {X B : Type} (c : X → X → B) (h₁ h₂ : ¬ Function.Surjective c) : h₁ = h₂ := rfl

/-- **Non-dependence.** Because the verdict is erased, every map out of it is constant, so no verdict formed from
the guard's output varies with the account. -/
theorem erasure_forces_nondependence {X B T : Type} (c : X → X → B)
    (F : ¬ Function.Surjective c → T) (h₁ h₂ : ¬ Function.Surjective c) : F h₁ = F h₂ :=
  congrArg F (guard_erases c h₁ h₂)

/-- **Uniformity.** The guard on any account is the uniform hole applied to it: `proposer_guard` factors through
`no_reflexive_object`. -/
theorem guard_is_the_uniform_hole {X B : Type} (build : X → (X → B)) {g : B → B} (hg : ∀ b, g b ≠ b) :
    proposer_guard build hg = no_reflexive_object hg build := rfl

/-- **Non-discrimination.** Two different accounts receive identical treatment, both bounded by the same lemma. -/
theorem uniformity_forbids_discrimination {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b)
    (build₁ build₂ : X → (X → B)) :
    (¬ Function.Surjective build₁) ∧ (¬ Function.Surjective build₂) :=
  ⟨guard_is_universal build₁ hg, guard_is_universal build₂ hg⟩

/-- **Zero capacity.** The verdict never varies: any two accounts receive equivalent verdicts, so the channel
transmits nothing. -/
theorem channel_capacity_is_zero {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b)
    (build₁ build₂ : X → (X → B)) :
    (¬ Function.Surjective build₁) ↔ (¬ Function.Surjective build₂) :=
  ⟨fun _ => guard_is_universal build₂ hg, fun _ => guard_is_universal build₁ hg⟩

/-- **The channel certifies.** The account must be present and the verdict is invariant: the channel guarantees,
it does not inform. -/
theorem channel_is_certification {X B : Type} (build : X → (X → B)) :
    ((proposedAccount build).build = build)
    ∧ (∀ h₁ h₂ : ¬ Function.Surjective build, h₁ = h₂) :=
  ⟨rfl, fun _ _ => rfl⟩

/-- **The channel's invariance is the hole's uniformity.** `hole_uniform` and `guard_is_universal` are the same
term, `no_reflexive_object` at the fixed-point-free endomap. -/
theorem apophatic_uniformity_is_channel_uniformity {X : Type} (c : X → X → Option Bool) :
    hole_uniform c = guard_is_universal c optCycle_fixedpointfree := rfl

/-- **Judgement is constant.** The verdict holds of every account with a fixed-point-free codomain: the verdict
map is constant, so no judgement varies with the account. -/
theorem judgement_is_constant {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) :
    ∀ build : X → (X → B), ¬ Function.Surjective build :=
  fun build => guard_is_universal build hg

/-- **The verdict ignores the case.** Two different accounts receive identical verdicts, both bounded: the
account's identity does not reach the verdict. -/
theorem verdict_ignores_the_case :
    ((fun (_ _ : Fin 2) => true) ≠ (fun (_ _ : Fin 2) => false))
    ∧ (¬ Function.Surjective (fun (_ _ : Fin 2) => true))
    ∧ (¬ Function.Surjective (fun (_ _ : Fin 2) => false)) :=
  ⟨by decide,
   no_reflexive_object (g := fun b => !b) (by decide) _,
   no_reflexive_object (g := fun b => !b) (by decide) _⟩

/-! ## The boundary limit: two distinct obstructions -/

/-- **The none and the surplus are distinct.** The apophatic none is a missing value in the codomain; the
cataphatic surplus is an excess, an unreached ambient point: different ambients, opposite kinds, neither derived
from the other. -/
theorem none_and_surplus_are_distinct :
    (imprecise 0 2 = none) ∧ (∃ a : ZMod 3, a ≠ 0 ∧ a ≠ 1) :=
  ⟨by decide, ⟨2, by decide, by decide⟩⟩

/-- **The ethical move is apophatic-shaped, and range-quantified.** The ethical center is distinct (a total
object still carries the hole) yet its move ends in a refusal, the same shape as the fold. The collision
quantifies the returned value (`c 0 2`), not the signature: total classifications exist, so the signature reading
is refuted, and vacating (a total map that never returns an absence) is the sole case distinguishing the two. -/
theorem ethical_is_apophatic_shaped :
    (∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ ¬ Function.Surjective c)
    ∧ ¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2 :=
  ⟨ethical_center_is_distinct, complete_and_faithful_is_impossible⟩

/-! ## Why the target is imported: no standard certifies itself -/

/-- **Every target is defeasible.** A target is itself a self-classification subject to the same hole, so no
standard is complete over itself and the target is handed back (○). -/
theorem every_target_is_defeasible {X : Type} (target : X → X → Bool) :
    ¬ Function.Surjective target :=
  no_reflexive_object (g := fun b => !b) (by decide) target

/-! ## The three limits: the prohibition does not swell -/

/-- **Local partialization is not prohibited.** A single local move is a valid, reachable operation: it does not
aim at the empty destination. -/
theorem local_partialization_not_prohibited :
    ∃ (w : Fin 4 → Fin 4 → Bool) (c : Fin 4 → Fin 4 → Option Bool),
      partialization w c 0 2 = none :=
  ⟨fun _ _ => true, fun _ _ => some true, by simp [partialization]⟩

/-- **No reachable target is prohibited.** Moving toward any target is always a valid step; every target stays
○. -/
theorem reachable_targets_not_prohibited {X : Type} (c : X → X → Option Bool) (t : Option Bool) (x : X) :
    x ∈ targetCoalgebra c x t :=
  agreementLE_refl c t x

/-- **Abstention is not prescribed.** Partialization's cost is target-dependent, a withdrawal a loss only
relative to a target: the prohibition is one-sided, silent on everything reachable. -/
theorem prohibition_does_not_prescribe_abstention :
    ∃ (c : Fin 2 → Fin 2 → Option Bool) (w : Fin 2 → Fin 2 → Bool) (t1 t2 : Fin 2 → Fin 2 → Bool),
      c 0 1 = some (t1 0 1) ∧ assertsFalse c t2 0 1 ∧ partialization w c 0 1 = none :=
  ⟨(fun x y => if x = 0 ∧ y = 1 then some true else none),
   (fun x y => decide (x = 0 ∧ y = 1)),
   (fun _ _ => true), (fun _ _ => false),
   by decide, ⟨true, by decide, by decide⟩, by decide⟩

/-- **Chiralogy falls under its own prohibition.** Represented within itself as `𝒜`, its self-classification
carries the hole (`self_account_has_hole`), so it too cannot claim completeness; the representation is not
identity, and that gap is handed back (○). -/
theorem chiralogy_under_its_own_boundary {X : Type} (c : X → X → Option Bool) :
    ¬ Function.Surjective c :=
  completeness_is_unreachable c

/-- **The Boundary braids both absences.** The one prohibition invokes each layer-center: the empty destination
routes through the kernel hole, complete-and-faithful through the model none. -/
theorem boundary_braids_both_absences :
    (∀ (X : Type) (c : X → X → Option Bool), ¬ Function.Surjective c) ∧
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2) :=
  ⟨fun _ c => no_reflexive_object optCycle_fixedpointfree c, complete_and_faithful_is_impossible⟩

/-- **The open seam.** The Boundary is the seam where the kernel chiasm's center and the model chiasm's center
are brought into contact by a single utterance, re-presented not reproven. -/
theorem the_open_seam :
    (∀ (X : Type) (c : X → X → Option Bool), ¬ Function.Surjective c) ∧
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2) :=
  boundary_braids_both_absences

/-- The kernel chiasm: two inversions around the hole. -/
abbrev KernelChiasmStmt : Prop :=
  (¬ Function.Surjective 𝒜.classify) ∧ (∀ {X : Type} (c : X → X → Option Bool), ¬ Function.Surjective c)

/-- The model chiasm: two arms around the none, with inverted costs. -/
abbrev ModelChiasmStmt : Prop :=
  (∃ (s : Fin 4 → Nat) (w : Fin 4 → Fin 4 → Bool),
      (imprecise 0 2 = none ∧ totalization s imprecise 0 2 ≠ none) ∧
      (imprecise 0 1 ≠ none ∧ partialization w imprecise 0 1 = none)) ∧
  (∀ t : Fin 4 → Fin 4 → Bool,
      assertsFalse (totalization (fun _ => 0) imprecise) t 0 2 ∨
        assertsFalse (totalization (fun i => if i = 2 then 1 else 0) imprecise) t 0 2) ∧
  (∀ (w : Fin 4 → Fin 4 → Bool) (c : Fin 4 → Fin 4 → Option Bool)
      (t : Fin 4 → Fin 4 → Bool) (x y : Fin 4),
      assertsFalse (partialization w c) t x y → assertsFalse c t x y)

/-- The braid: the one prohibition brings the two centers into contact. -/
abbrev BraidStmt : Prop :=
  (∀ (X : Type) (c : X → X → Option Bool), ¬ Function.Surjective c) ∧
  (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2)

/-- **The conjunction (the floor).** The kernel chiasm, the model chiasm, and the braid bundled: three proven
facts side by side, a conjunction, not one generated object. -/
theorem double_chiasm_conjunction : KernelChiasmStmt ∧ ModelChiasmStmt ∧ BraidStmt :=
  ⟨⟨no_reflexive_object (g := fun b => !b) (by decide) 𝒜.classify, fun c => hole_uniform c⟩,
   model_arms_invert, boundary_braids_both_absences⟩

/-- The two absences, as the candidate parameter of a uniform generator. -/
inductive Absence where
  | hole
  | none

/-- The chiasm-type of each absence: a case-split, since the two chiasms have different types. -/
def ChiasmType : Absence → Prop
  | .hole => KernelChiasmStmt
  | .none => ModelChiasmStmt

/-- The attempted generator: a match dispatching to the pre-proven chiasm, adding nothing beyond
`double_chiasm_conjunction`. -/
def chiasm_of : (a : Absence) → ChiasmType a
  | .hole => ⟨no_reflexive_object (g := fun b => !b) (by decide) 𝒜.classify, fun c => hole_uniform c⟩
  | .none => model_arms_invert

/-- **The double chiasm does not compose.** The two centers are different kinds of absence, so no single datum
feeds a uniform generator: the hole holds on `Bool` (no `none`), the none is a distinguished codomain point in
`Option`, so `chiasm_of` can only dispatch. -/
theorem double_chiasm_does_not_compose :
    (∃ c : Fin 2 → Fin 2 → Bool, ¬ Function.Surjective c) ∧
    (∃ i j : Fin 4, imprecise i j = none) :=
  ⟨⟨fun _ _ => true, stochastic_collapses (g := fun b => !b) (by decide) _⟩, 0, 2, by decide⟩

/-! ## The prohibition is over an act; the lie is fragile

The collision is over the returned value, and its result is indistinguishable from innocence, so nothing detects
the act from the result. But under extension a fabricated value is fragile: absorbing at the hole is the total
side of the collision, which bites pointwise where absorbing acts. -/

/-- **The guard's uniformity is observational coarseness.** The guard distinguishes nothing: every observation of
its verdict is constant (`erasure_forces_nondependence`), which coalgebraically is the coarsest bisimilarity, all
states identified. -/
theorem guard_uniformity_is_observational_coarseness {X B T : Type} (c : X → X → B)
    (obs : ¬ Function.Surjective c → T) (h₁ h₂ : ¬ Function.Surjective c) : obs h₁ = obs h₂ :=
  erasure_forces_nondependence c obs h₁ h₂

/-- **Nothing detects totalization from the result.** A totalization of an absence produces the same value as the
genuine verdict, so the prohibition is over an act whose result is indistinguishable from innocence. -/
theorem nothing_detects_totalization :
    (fun v : Option Bool => some (v.getD true)) none = (fun v : Option Bool => some (v.getD true)) (some true) :=
  rfl

/-- **The lie's fragility is derived from the boundary.** Maintaining a fabricated value under a new view requires
reporting it at the hole (`c 0 2 = some true`), the total side of the collision, which bites pointwise where
absorbing acts (`imprecise 0 2 = none`): an absorbing view is unfaithful there, inherited per view. Visible only
given marking; unmarked, honest and coordinated present identically. -/
theorem lie_fragility_is_boundary_derived (c : Fin 4 → Fin 4 → Option Bool) :
    c 0 2 = some true → c 0 2 ≠ imprecise 0 2 :=
  fun h => by rw [h]; decide

end Chiralogy
