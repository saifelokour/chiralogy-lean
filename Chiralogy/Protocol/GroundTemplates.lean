import Chiralogy.Protocol.Membership

/-! # Protocol: ground-templates

An occupancy specification: what a domain must exhibit to present a ground-structure. A template is a
prerequisite order on a finite ground-set; a domain presents it by exhibiting that many distinguishable
grounds. This is statable without the closure notion, so it sits beside `Membership` and imports no model: the
template is a condition on a domain, and the model computes the permitted moves from it separately. -/

namespace Chiralogy

/-- A template: `grounds` many grounds with a prerequisite order among them. IMPORTED per register; the template
names the order, it does not compute with it. -/
structure GroundTemplate where
  grounds : ℕ
  prereq : Fin grounds → Fin grounds → Bool

/-- A member presents a template when its distinction space exhibits the template's grounds distinguishably.
Stated with no closure notion: only membership and injectivity, the prerequisites carried by the template. -/
def Presents (M : Member) (T : GroundTemplate) : Prop :=
  ∃ g : Fin T.grounds → M.B, Function.Injective g

/-- The point template: one ground, no prerequisite (physics). -/
def pointTemplate : GroundTemplate := ⟨1, fun _ _ => false⟩

/-- The chain template: three grounds in a prerequisite chain (a type system, and the missing-data mechanisms). -/
def chainTemplate : GroundTemplate :=
  ⟨3, fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 1) && decide (b = 2))⟩

/-- **The occupancy templates.** The point template asks one ground, the chain three with the linear
prerequisite (closing the third presupposes the second, the second the first). Each is a bare order, no closure
notion, so the split holds: the template is a condition on a domain, its consequences the model's separately. -/
theorem occupancy_templates :
    pointTemplate.grounds = 1
    ∧ chainTemplate.grounds = 3
    ∧ chainTemplate.prereq (1 : Fin 3) (2 : Fin 3) = true
    ∧ chainTemplate.prereq (2 : Fin 3) (1 : Fin 3) = false :=
  ⟨rfl, rfl, by decide, by decide⟩

/-- **Presenting is model-free.** A domain presents the chain template exactly by exhibiting three
distinguishable grounds; the witness is any injection from the three grounds into the distinction space, with no
closure machinery invoked. -/
theorem presents_needs_no_closure (M : Member) (g : Fin 3 → M.B) (hg : Function.Injective g) :
    Presents M chainTemplate :=
  ⟨g, hg⟩

end Chiralogy
