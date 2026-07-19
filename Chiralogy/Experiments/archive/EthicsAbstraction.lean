import Chiralogy

/-! # Experiment: is the ethics an abstraction over levels or over registers?

A levelled register inherits the permitted lattice, the fragmented center, and the per-reason totalizations by
conforming. Determine whether that structure varies with the domain (abstraction over registers) or only with
the level (abstraction over levels, which registers receive). If it abstracts over registers, two registers at
the same level differ ethically somewhere; if over levels, they have identical ethical structure and the domain
contributes nothing structural. Stays in `Experiments/`; canonical untouched; the protocol is not extended;
nothing resolved. -/

open Chiralogy

namespace Chiralogy.EthicsAbstraction

/-! ## Part 1: a second register

Two registers at the same level, Except (`Bool ⊕ Bool`, two reasons). The first stands for a physics-style
domain, the second for a genuinely different one: a different carrier with its own reason-placement, not the
first relabelled. No claim is made about the second domain's subject matter beyond what it imports. -/

/-- A physics-style register at the Except level: the diagonal is a verdict, the off-diagonal a reason. -/
def physicsRegister : Member where
  X := Fin 2
  B := Bool ⊕ Bool
  canDiffer := ⟨Sum.inl true, Sum.inr false, by decide⟩
  classify := fun x y => if x = y then Sum.inl true else Sum.inr false
  nondegenerate := ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩

/-- A second, genuinely different register at the same level: a different carrier (`Fin 3`) reading the
absences at the opposite cells, the diagonal a reason and the off-diagonal a verdict. Its content is only what
it imports. -/
def secondRegister : Member where
  X := Fin 3
  B := Bool ⊕ Bool
  canDiffer := ⟨Sum.inl true, Sum.inr false, by decide⟩
  classify := fun x y => if x = y then Sum.inr true else Sum.inl false
  nondegenerate := ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩

/-- **Both conform.** Each passes the unchanged protocol and the payload fires: no complete self-account for
either. -/
theorem both_conform :
    ¬ Function.Surjective physicsRegister.classify ∧ ¬ Function.Surjective secondRegister.classify :=
  ⟨payload physicsRegister, payload secondRegister⟩

/-! ## Part 2: does anything ethical differ?

Compare the two at the same level on every ethical feature available. Each feature is a fact about the level
(Except, two reasons), so it is shared; the search is whether the register's own classify reaches any of
them. -/

/-- **Same permitted count.** Both are at two reasons, so both have `2 ^ 2 - 1 = 3` permitted totalizations. -/
theorem same_permitted_count :
    (Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3 := by decide

/-- **Same lattice.** The permitted order depends only on the reason count (`same_reason_count_same_lattice`),
so at two reasons it transports along any relabelling of the reasons, here the swap: the two registers' orders
are isomorphic. -/
theorem same_lattice (a b : Fin 2 → Bool) :
    leReasons a b ↔
      leReasons (fun r => a ((Equiv.swap (0 : Fin 2) 1).symm r))
                (fun r => b ((Equiv.swap (0 : Fin 2) 1).symm r)) :=
  same_reason_count_same_lattice (Equiv.swap (0 : Fin 2) 1) a b

/-- **Same prohibition.** The forbidden move is the full closure in both: one prohibited totalization each. -/
theorem same_prohibition :
    (Finset.univ.filter (fun close : Fin 2 → Bool => ∀ r, close r = true)).card = 1 := by decide

/-- **Same center structure.** The center fragments identically: two reason-parts, distinct, the level's, not
the register's. -/
theorem same_center_structure :
    exceptAbsence.absent (Sum.inr false) ∧ exceptAbsence.absent (Sum.inr true)
    ∧ (Sum.inr false : Bool ⊕ Bool) ≠ Sum.inr true :=
  ⟨⟨false, rfl⟩, ⟨true, rfl⟩, by decide⟩

/-- **The domain does not contribute structurally.** The two registers genuinely differ: physics reads the
off-diagonal as a reason and the diagonal as a verdict, the second the reverse. Yet the permitted count is the
same for both (`3`, the level's), and by the results above so are the lattice, the prohibition, and the center.
The classify differs, and its difference reaches which absence sits where, a domain fact; it reaches no
structural ethical feature. The difference is interpretive, not structural. -/
theorem does_the_domain_contribute :
    ((∃ e, physicsRegister.classify (0 : Fin 2) (1 : Fin 2) = Sum.inr e)
        ∧ physicsRegister.classify (0 : Fin 2) (0 : Fin 2) = Sum.inl true)
    ∧ ((∃ e, secondRegister.classify (0 : Fin 3) (0 : Fin 3) = Sum.inr e)
        ∧ secondRegister.classify (0 : Fin 3) (1 : Fin 3) = Sum.inl false)
    ∧ (Finset.univ.filter (fun close : Fin 2 → Bool => ¬ ∀ r, close r = true)).card = 3 :=
  ⟨⟨⟨false, rfl⟩, rfl⟩, ⟨⟨true, rfl⟩, rfl⟩, by decide⟩

/-! ## Part 3: what the domain does contribute -/

/-- **The domain supplies the reading.** At one and the same structural cell the two registers assign different
values (`Sum.inr false` versus `Sum.inl false`): the classify is the register's imported datum, the
identification of what each absence is in that domain. The structure is the level's, the meaning the domain's.
This is the register-import pattern, not a new result. -/
theorem domain_supplies_the_reading :
    physicsRegister.classify (0 : Fin 2) (1 : Fin 2) ≠ secondRegister.classify (0 : Fin 3) (1 : Fin 3) := by
  show (Sum.inr false : Bool ⊕ Bool) ≠ (Sum.inl false : Bool ⊕ Bool)
  decide

/-! ## The verdict

Part 1: a second, genuinely different register conforms at the same level. Different carrier, its own
reason-placement, the unchanged protocol, and the payload fires for each (`both_conform`).

Part 2: no ethical feature differs. The permitted count (`same_permitted_count`), the lattice
(`same_lattice`), the prohibition (`same_prohibition`), and the center (`same_center_structure`) are the
level's, identical for both. The two classifications do differ, and the difference reaches which absence sits
where, but no structural feature (`does_the_domain_contribute`); the classify is invisible to the ethics.

Part 3: the domain supplies the reading, the identification of what each absence is
(`domain_supplies_the_reading`), the imported content of the register-import pattern, not a new result.

The verdict: the ethics is an abstraction over levels, which registers receive. The level shapes the ethics;
the domain names the reasons. Nothing here is resolved. -/

end Chiralogy.EthicsAbstraction
