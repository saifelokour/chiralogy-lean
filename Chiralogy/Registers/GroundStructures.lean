import Chiralogy.Protocol.Membership
import Chiralogy.Model.Grounds

/-! # Registers: four members and their ground-structures

Four domains entering through the protocol, each a genuine two-place self-classifying family (distinct elements
distinct verdicts, the payload firing) carrying a ground-structure. All domain content is IMPORTED and every
mapping is a READING; the protocol is not extended, and nothing is claimed of any subject matter beyond the
ground-structure each register carries. The domain family is imported; `genuineFam` witnesses the two-place
non-degeneracy each register requires. Cognition is a three-chain, immunology a two-chain plus a free ground,
chemistry a three-chain plus a free ground, trust a fork plus a free ground, the first non-chain bound
component. -/

namespace Chiralogy

/-- A representative genuine two-place family, the non-degeneracy witness for each register. -/
def genuineFam : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none

/-- Chemistry's order: Currie's nested lower limits `0 ≺ 1 ≺ 2` (critical, detection, quantitation) and the
upper quantitation limit `3` a separate axis, free. IMPORTED (IUPAC, Currie), READING. -/
def prereqChemistry : Fin 4 → Fin 4 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 1) && decide (b = 2))

/-- Trust's order: identity-resolution `0` below two independent interaction grounds `1`, `2` (a fork) and a free
withheld ground `3`. IMPORTED (multi-agent trust), READING. -/
def prereqTrust : Fin 4 → Fin 4 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 0) && decide (b = 2))

/-- **Cognition: a three-chain.** The generative model over representations, a family; its grounds (novel input,
mis-specified prior, no vocabulary) chain, three permitted moves. -/
theorem cognition_register :
    (NonDegenerate genuineFam ∧ ¬ Function.Surjective genuineFam)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqChain3 S ∧ ¬ ∀ r, S r = true)).card = 3) :=
  ⟨⟨⟨0, 1, by decide⟩, hole_uniform genuineFam⟩, by decide⟩

/-- **Immunology: a two-chain plus a free ground.** Clones over the repertoire, a family; its grounds
(no-match `0 ≺ 1` below-threshold, anergy `2` free) a mixed order, five permitted. -/
theorem immunology_register :
    (NonDegenerate genuineFam ∧ ¬ Function.Surjective genuineFam)
    ∧ (isFree prereqMixed3 2 ∧ ¬ isFree prereqMixed3 0)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqMixed3 S ∧ ¬ ∀ r, S r = true)).card = 5) :=
  ⟨⟨⟨0, 1, by decide⟩, hole_uniform genuineFam⟩, ⟨by decide, by decide⟩, by decide⟩

/-- **Chemistry: a three-chain plus a free ground.** Method-analyte detection, a family; Currie's nested lower
limits chain with the upper limit free, seven permitted. -/
theorem chemistry_register :
    (NonDegenerate genuineFam ∧ ¬ Function.Surjective genuineFam)
    ∧ (isFree prereqChemistry 3 ∧ ¬ isFree prereqChemistry 0)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable prereqChemistry S ∧ ¬ ∀ r, S r = true)).card = 7) :=
  ⟨⟨⟨0, 1, by decide⟩, hole_uniform genuineFam⟩, ⟨by decide, by decide⟩, by decide⟩

/-- **Trust: a fork plus a free ground.** Agents over agents, a family; identity-resolution below two independent
interaction grounds (a fork, the first non-chain bound component) with a free withheld ground, nine permitted,
the fork worth five closeable up-sets where a chain of three is four. -/
theorem trust_register :
    (NonDegenerate genuineFam ∧ ¬ Function.Surjective genuineFam)
    ∧ (isFree prereqTrust 3 ∧ ¬ isFree prereqTrust 0)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable prereqTrust S ∧ ¬ ∀ r, S r = true)).card = 9)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable prereqV3 S)).card = 5) :=
  ⟨⟨⟨0, 1, by decide⟩, hole_uniform genuineFam⟩, ⟨by decide, by decide⟩, by decide, by decide⟩

end Chiralogy
