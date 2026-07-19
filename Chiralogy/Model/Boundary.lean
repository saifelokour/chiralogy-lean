import Chiralogy.Model.Apophatic
import Chiralogy.Model.Cataphatic
import Chiralogy.Kernel.Center
import Chiralogy.Kernel.Apophatic
import Mathlib.Data.ZMod.Basic

/-! # Model: the boundary between the arms (limit, seam, channel)

The in-between where the two arms meet at a limit and communicate, connected not fused. The one prohibition:
`complete_and_faithful_is_impossible` (the limit where the none and surplus are co-located),
`completeness_is_unreachable`, `totalization_is_self_defeating`, and the reachable/handed-back results.
The braid: `boundary_braids_both_absences` and `the_open_seam` bring the kernel hole and the model none into
contact; `double_chiasm_does_not_compose` shows the two chiasms share no generator (a reading, not one
object). The channel: a proposed account (`proposedAccount`) flows cataphatic to apophatic, the guard
bounding it (`proposer_guard`, `guard_is_universal`); the flow is one-way (`fold_then_build_ignores_guard`,
`Type → Prop`). The two boundary obstructions are distinct (`none_and_surplus_are_distinct`), and the
ethical move is apophatic-shaped (`ethical_is_apophatic_shaped`). The channel certifies rather than informs
(`guard_erases`, `erasure_forces_nondependence`, `guard_is_the_uniform_hole`,
`uniformity_forbids_discrimination`, `channel_capacity_is_zero`, `channel_is_certification`,
`apophatic_uniformity_is_channel_uniformity`); judgement is constant (`judgement_is_constant`,
`verdict_ignores_the_case`). These channel and arm results are absence-agnostic (over any distinction space,
they mention no absence-structure), so they are unchanged under the generalization. Under structured absence
the prohibition narrows rather than fragments (`one_prohibition_permitted_grew`), the permitted moves carry a
partial order with the prohibition at its top (`full_closure_is_the_top`, `partial_totalizations_are_ranked`,
`ranking_is_partial_not_total`), and collision separates from concealment (`collision_without_concealment`). -/

namespace Chiralogy

/-- **Completeness is unreachable.** The success condition of the totalizing attempt, a surjective
self-classification, is provably unsatisfiable. -/
theorem completeness_is_unreachable {X : Type} (c : X → X → Option Bool) :
    ¬ Function.Surjective c :=
  hole_uniform c

/-- **The internal contradiction.** A total map that is also faithful to a constitutive absence is
impossible: totality needs a verdict where faithfulness needs the absence. The self-defeat is by the
move's own goal: no external standard, no imported value, only the map's own absence against totality. This is
the base instance of the generic `boundary_collision` (`base_collision_is_generic`); binary at the base, it
becomes a spectrum above, where only full totality collides (see the prohibition order below). -/
theorem complete_and_faithful_is_impossible :
    ¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2 := by
  rintro ⟨c, htotal, hfaithful⟩
  rw [show imprecise (0 : Fin 4) 2 = none from by decide] at hfaithful
  exact htotal 0 2 hfaithful

/-- **Totalization is self-defeating.** It fills the absences yet the totalized map still carries the hole
- it cannot reach the completeness it aims at. Its own success condition fails. -/
theorem totalization_is_self_defeating {X : Type} (s : X → Nat) (c : X → X → Option Bool) :
    (∀ x y, totalization s c x y ≠ none) ∧ ¬ Function.Surjective (totalization s c) :=
  ⟨totalization_totalizes s c, totalization_hole s c⟩

/-! ## The prohibition under structured absence

Above the base the prohibition changes shape without splitting. A totalization is given by which reasons it
closes, `close : Bool → Bool`; the collision is structural, concealment contingent. -/

/-- A totalization is full when it closes every reason. -/
abbrev isFull (close : Bool → Bool) : Prop := close false = true ∧ close true = true

/-- A totalization keeps some reason (does not collide) when it leaves one open. -/
abbrev keepsSome (close : Bool → Bool) : Prop := close false = false ∨ close true = false

/-- **Permitted iff not full.** A move avoids the collision exactly when it is not the full closure. -/
theorem permitted_iff_not_full (close : Bool → Bool) : keepsSome close ↔ ¬ isFull close := by
  cases h0 : close false <;> cases h1 : close true <;> simp [isFull, keepsSome, h0, h1]

/-- **Exactly one prohibited move.** Only the full closure collides: the prohibited totalization is unique. -/
theorem exactly_one_prohibited (close : Bool → Bool) : isFull close ↔ close = fun _ => true := by
  constructor
  · rintro ⟨h0, h1⟩; funext r; cases r <;> assumption
  · rintro rfl; exact ⟨rfl, rfl⟩

/-- **The prohibition narrows, it does not fragment.** Of the four totalization moves, exactly one, the full
closure, is prohibited and three are permitted: structured absence forbids the same one move and permits more
than the binary base. -/
theorem one_prohibition_permitted_grew :
    (Finset.univ.filter (fun close : Bool → Bool => isFull close)).card = 1
    ∧ (Finset.univ.filter (fun close : Bool → Bool => ¬ isFull close)).card = 3 := by decide

/-- The inclusion order on closures: closing a subset of the reasons. -/
abbrev closeLE (close close' : Bool → Bool) : Prop := ∀ r, close r = true → close' r = true

/-- **The prohibited move is the top.** Every totalization is below the full closure in the inclusion order:
the prohibition sits at the top, with the base as the degenerate one-element case. -/
theorem full_closure_is_the_top (close : Bool → Bool) : closeLE close (fun _ => true) :=
  fun _ _ => rfl

/-- **The permitted moves are ranked by inclusion.** A strict chain of closures exists, so 6.a.4's "nothing
reachable ranked" holds only at the base; above it the reachable partial totalizations carry an order. -/
theorem partial_totalizations_are_ranked :
    closeLE (fun _ => false) (fun r => decide (r = false))
    ∧ closeLE (fun r => decide (r = false)) (fun _ => true)
    ∧ ¬ closeLE (fun _ => true) (fun r => decide (r = false)) := by decide

/-- **The order is partial, not total.** Closing only `false` and closing only `true` are incomparable: a
lattice of closures, not a total ranking. -/
theorem ranking_is_partial_not_total :
    ¬ closeLE (fun r => decide (r = false)) (fun r => decide (r = true))
    ∧ ¬ closeLE (fun r => decide (r = true)) (fun r => decide (r = false)) := by decide

/-- A recording totalization at the Writer value space: fabricate, and log the fabrication. -/
def recordingTotalize (e : Bool) : Option Bool × List Bool → Option Bool × List Bool
  | (none, l) => (some true, e :: l)
  | (some b, l) => (some b, l)

/-- **Collision without concealment.** The collision is structural: total and faithful are incompatible at
the memoryful value space regardless of the log. Concealment is contingent: the recording variant marks the
fabrication, so it does not conceal. The base bundles collision and concealment; a level separates them. -/
theorem collision_without_concealment :
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool × List Bool, (∀ x y, (c x y).1 ≠ none) ∧ (c 0 2).1 = none)
    ∧ (∀ e : Bool, recordingTotalize e (none, []) ≠ recordingTotalize e (some true, ([] : List Bool))) := by
  refine ⟨?_, fun e => ?_⟩
  · rintro ⟨c, htot, hf⟩; exact htot 0 2 hf
  · exact fun h => List.cons_ne_nil e [] (congrArg Prod.snd h)

/-! ## Why the target is imported: no standard certifies itself -/

/-- **Every target is defeasible.** A target is itself a self-classification, subject to the same hole:
no standard is complete over itself. So no target certifies itself, and the target is handed back (○). -/
theorem every_target_is_defeasible {X : Type} (target : X → X → Bool) :
    ¬ Function.Surjective target :=
  no_reflexive_object (g := fun b => !b) (by decide) target

/-! ## The three limits: the prohibition does not swell -/

/-- Local partialization is not prohibited: a single local move is a valid, reachable operation: it does
not aim at the empty destination. -/
theorem local_partialization_not_prohibited :
    ∃ (w : Fin 4 → Fin 4 → Bool) (c : Fin 4 → Fin 4 → Option Bool),
      partialization w c 0 2 = none :=
  ⟨fun _ _ => true, fun _ _ => some true, by simp [partialization]⟩

/-- No reachable target is prohibited: moving toward any target is always a valid step. Every target
stays ○. -/
theorem reachable_targets_not_prohibited {X : Type} (c : X → X → Option Bool) (t : Option Bool) (x : X) :
    x ∈ targetCoalgebra c x t :=
  agreementLE_refl c t x

/-- Abstention is not prescribed: partialization's cost is target-dependent: a withdrawal is a loss only
relative to a target. The prohibition is one-sided, silent on everything reachable. -/
theorem prohibition_does_not_prescribe_abstention :
    ∃ (c : Fin 2 → Fin 2 → Option Bool) (w : Fin 2 → Fin 2 → Bool) (t1 t2 : Fin 2 → Fin 2 → Bool),
      c 0 1 = some (t1 0 1) ∧ assertsFalse c t2 0 1 ∧ partialization w c 0 1 = none :=
  ⟨(fun x y => if x = 0 ∧ y = 1 then some true else none),
   (fun x y => decide (x = 0 ∧ y = 1)),
   (fun _ _ => true), (fun _ _ => false),
   by decide, ⟨true, by decide, by decide⟩, by decide⟩

/-- **Chiralogy falls under its own prohibition and its own payload.** Represented within itself as the
object `𝒜` (`Kernel/SelfApplication.lean`), its self-classification carries the hole: `self_account_has_hole`.
So it too cannot claim completeness, nor install its register (category theory, type theory, Lean, English)
as the complete language: that would be the attempt performed on its own medium, one level up. The
representation is not identity: `𝒜 = Chiralogy` is not proven, and that completeness gap is handed back (○)
as the framework's own hole. -/
theorem chiralogy_under_its_own_boundary {X : Type} (c : X → X → Option Bool) :
    ¬ Function.Surjective c :=
  completeness_is_unreachable c

/-- **The Boundary braids both absences.** The one prohibition invokes each layer-center: the destination is empty routes through the kernel hole `no_reflexive_object`; complete-and-faithful is impossible routes through the model none (`imprecise 0 2 = none`). The two centers meet at the Boundary. -/
theorem boundary_braids_both_absences :
    (∀ (X : Type) (c : X → X → Option Bool), ¬ Function.Surjective c) ∧
    (¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2) :=
  ⟨fun _ c => no_reflexive_object optCycle_fixedpointfree c, complete_and_faithful_is_impossible⟩

/-- **The open seam.** The one prohibition braids the two layer-centers: no complete self-account pivots on the kernel hole `no_reflexive_object`, no complete-and-faithful map on the model none.
The Boundary is the seam where the kernel chiasm's center and the model chiasm's center are brought into
contact by a single utterance. Re-presented, not reproven. -/
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

/-- **The conjunction (the floor).** The kernel chiasm, the model chiasm, and the braid bundled into one statement. This always succeeds: it is
three proven facts placed side by side, a conjunction, not one generated object. -/
theorem double_chiasm_conjunction : KernelChiasmStmt ∧ ModelChiasmStmt ∧ BraidStmt :=
  ⟨⟨no_reflexive_object (g := fun b => !b) (by decide) 𝒜.classify, fun c => hole_uniform c⟩,
   model_arms_invert, boundary_braids_both_absences⟩

/-- The two absences, as the candidate parameter of a uniform generator. -/
inductive Absence where
  | hole
  | none

/-- The chiasm-type of each absence. It is a case-split: the two chiasms have different types, so any
generator over `Absence` is dependently typed on which absence it received. -/
def ChiasmType : Absence → Prop
  | .hole => KernelChiasmStmt
  | .none => ModelChiasmStmt

/-- The attempted generator. Its proof term is a match: it inspects which absence it got and returns the
corresponding pre-proven chiasm. That is a dispatch, not a construction from the absence's structure, so it adds nothing beyond `double_chiasm_conjunction`. -/
def chiasm_of : (a : Absence) → ChiasmType a
  | .hole => ⟨no_reflexive_object (g := fun b => !b) (by decide) 𝒜.classify, fun c => hole_uniform c⟩
  | .none => model_arms_invert

/-- **The double chiasm does not compose.** The two centers are different kinds of absence, so no single
datum feeds a uniform generator. The kernel center (the hole) is non-surjectivity for any codomain carrying
a fixed-point-free endomap (`stochastic_collapses`): it holds on `Bool`, which has no `none`. The model
center is a distinguished point of the codomain, realized only in `Option` (here as `imprecise`'s `none`).
The hole is present where the none cannot be, so `chiasm_of` can only dispatch (the hole's arity versus the none's codomain point). -/
theorem double_chiasm_does_not_compose :
    (∃ c : Fin 2 → Fin 2 → Bool, ¬ Function.Surjective c) ∧
    (∃ i j : Fin 4, imprecise i j = none) :=
  ⟨⟨fun _ _ => true, stochastic_collapses (g := fun b => !b) (by decide) _⟩, 0, 2, by decide⟩

/-- The proposer. A cataphatic construction whose ambient is the account space `X → B`: its build proposes
an account of `X`, a candidate self-classification in transpose form. Free (build-outward proposes
anything). -/
def proposedAccount {X B : Type} (build : X → (X → B)) : CataphaticConformant := ⟨X, X → B, build⟩

/-- The guard bounds the proposal, on the term. Idolatry-detection (`no_reflexive_object`) fires on the
proposer's own output `(proposedAccount build).build`: if the proposed account were totalized (claimed
surjective, the complete self-classification), it is refuted. The argument to the refutation is the built
account itself, so this is data-flow (the account flows into the guard), not a function between the arms.
The same `build` is the proposer's output and the guard's target, in one term. -/
theorem proposer_guard {X B : Type} (build : X → (X → B)) {g : B → B} (hg : ∀ b, g b ≠ b) :
    ¬ Function.Surjective (proposedAccount build).build :=
  no_reflexive_object hg build

/-- The guard is universal: it bounds any account, not only proposed ones. So the relationship is a division
of labor, a free proposer met by a guard ready for any proposal, not a guard that targets one construction.
This is the same data-flow read at the top level: whatever the proposer builds, the guard is already able to
bound. -/
theorem guard_is_universal {X B : Type} (c : X → X → B) {g : B → B} (hg : ∀ b, g b ≠ b) :
    ¬ Function.Surjective c :=
  no_reflexive_object hg c
/-- Composite 2, fold-then-build, does not genuinely exist. The guard's actual output is `¬ Surjective c`, a
Prop, hence proof-irrelevant: any map `F` from that output to an account is constant in it (`rfl`, by proof
irrelevance). So the refutation carries nothing to build from; whatever account `F` returns is smuggled from
the ambient data, not derived from the guard's output. The asymmetry is by absence, the type signature: Type
flows into Prop (build-then-fold), Prop cannot flow back into Type (fold-then-build). -/
theorem fold_then_build_ignores_guard {X B : Type} (c : X → X → B)
    (F : ¬ Function.Surjective c → CataphaticConformant) (h₁ h₂ : ¬ Function.Surjective c) :
    F h₁ = F h₂ := rfl

/-- **The two arms are adjacent, not crossed.** The apophatic arm (the hole at the codomain) and the
cataphatic arm (the free transpose at the domain) hold together from one `c`, joined by `∧`, not by a
between-arms function: bicameral, not chiastic. The conjunction is `one_map_two_ends`; that it is not a
crossing map is `loop_does_not_close` and the one-way channel (`fold_then_build_ignores_guard`). -/
theorem two_adjacent_arms {X B : Type} (c : X → X → B) :
    (∀ g : B → B, (∀ b, g b ≠ b) → ¬ Function.Surjective c) ∧ (∃ build : X → (X → B), ∀ x, build x = c x) :=
  one_map_two_ends c

/-! ## The boundary limit: two distinct obstructions -/

/-- **The none and the surplus are distinct.** The apophatic none is an absence, a missing value in the
codomain (`imprecise 0 2 = none`); the cataphatic surplus is an excess, an unreached point in the ambient
(`∃ a : ZMod 3, a ≠ 0 ∧ a ≠ 1`). Different ambients, opposite kinds, neither derived from the other: two
obstructions co-located at the limit, not one. -/
theorem none_and_surplus_are_distinct :
    (imprecise 0 2 = none) ∧ (∃ a : ZMod 3, a ≠ 0 ∧ a ≠ 1) :=
  ⟨by decide, ⟨2, by decide, by decide⟩⟩

/-- **The ethical move is apophatic-shaped.** The ethical center is distinct (a total object still carries
the hole, `ethical_center_is_distinct`), yet its move ends in a refusal (`¬ ∃`,
`complete_and_faithful_is_impossible`), the same shape as the fold: a distinct center reached by the
apophatic move. -/
theorem ethical_is_apophatic_shaped :
    (∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ ¬ Function.Surjective c)
    ∧ ¬ ∃ c : Fin 4 → Fin 4 → Option Bool, (∀ x y, c x y ≠ none) ∧ c 0 2 = imprecise 0 2 :=
  ⟨ethical_center_is_distinct, complete_and_faithful_is_impossible⟩

/-! ## The certification chain: erasure to zero capacity -/

/-- **Erasure.** The guard's verdict is a `Prop`, hence proof-irrelevant: any two proofs are equal. -/
theorem guard_erases {X B : Type} (c : X → X → B) (h₁ h₂ : ¬ Function.Surjective c) : h₁ = h₂ := rfl

/-- **Non-dependence.** Because the verdict is erased, every map out of it is constant. So no verdict formed
from the guard's output varies with the account, over the flows the framework has (not a quantification over
all conceivable operations). -/
theorem erasure_forces_nondependence {X B T : Type} (c : X → X → B)
    (F : ¬ Function.Surjective c → T) (h₁ h₂ : ¬ Function.Surjective c) : F h₁ = F h₂ :=
  congrArg F (guard_erases c h₁ h₂)

/-- **Uniformity.** The guard on any account is the uniform hole applied to it: `proposer_guard` factors
through `no_reflexive_object`, one lemma for every account. -/
theorem guard_is_the_uniform_hole {X B : Type} (build : X → (X → B)) {g : B → B} (hg : ∀ b, g b ≠ b) :
    proposer_guard build hg = no_reflexive_object hg build := rfl

/-- **Non-discrimination.** Two different accounts receive identical treatment: both bounded by the same
lemma. -/
theorem uniformity_forbids_discrimination {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b)
    (build₁ build₂ : X → (X → B)) :
    (¬ Function.Surjective build₁) ∧ (¬ Function.Surjective build₂) :=
  ⟨guard_is_universal build₁ hg, guard_is_universal build₂ hg⟩

/-- **Zero capacity.** The verdict never varies: any two accounts receive equivalent verdicts, so the
channel transmits nothing. -/
theorem channel_capacity_is_zero {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b)
    (build₁ build₂ : X → (X → B)) :
    (¬ Function.Surjective build₁) ↔ (¬ Function.Surjective build₂) :=
  ⟨fun _ => guard_is_universal build₂ hg, fun _ => guard_is_universal build₁ hg⟩

/-! ## The channel certifies -/

/-- **The channel certifies.** The account must be present (it is the guard's argument,
`(proposedAccount build).build = build`) and the verdict is invariant (all proofs equal). The channel
guarantees; it does not inform. -/
theorem channel_is_certification {X B : Type} (build : X → (X → B)) :
    ((proposedAccount build).build = build)
    ∧ (∀ h₁ h₂ : ¬ Function.Surjective build, h₁ = h₂) :=
  ⟨rfl, fun _ _ => rfl⟩

/-- **The channel's invariance is the hole's uniformity.** `hole_uniform` and `guard_is_universal` are the
same term, `no_reflexive_object` at the fixed-point-free endomap: one uniformity, at the codomain and at the
channel. -/
theorem apophatic_uniformity_is_channel_uniformity {X : Type} (c : X → X → Option Bool) :
    hole_uniform c = guard_is_universal c optCycle_fixedpointfree := rfl

/-! ## Judgement is constant -/

/-- **Judgement is constant.** The verdict holds of every account with a fixed-point-free codomain: the
verdict map is constant, so no judgement varies with the account. -/
theorem judgement_is_constant {X B : Type} {g : B → B} (hg : ∀ b, g b ≠ b) :
    ∀ build : X → (X → B), ¬ Function.Surjective build :=
  fun build => guard_is_universal build hg

/-- **The verdict ignores the case.** Two different accounts (constant `true` and constant `false` on
`Fin 2`) receive identical verdicts: both bounded. The account's identity does not reach the verdict. -/
theorem verdict_ignores_the_case :
    ((fun (_ _ : Fin 2) => true) ≠ (fun (_ _ : Fin 2) => false))
    ∧ (¬ Function.Surjective (fun (_ _ : Fin 2) => true))
    ∧ (¬ Function.Surjective (fun (_ _ : Fin 2) => false)) :=
  ⟨by decide,
   no_reflexive_object (g := fun b => !b) (by decide) _,
   no_reflexive_object (g := fun b => !b) (by decide) _⟩

end Chiralogy
