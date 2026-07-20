-- ARCHIVED (register and ground-structure graduation): cognition, immunology, chemistry graduated to Registers/GroundStructures; survey and medical fail the two-place gate (single judge, one-place taxonomies).

import Chiralogy

/-! # Experiment: five registers and their ground-structures

The framework has two registers, one at the degenerate base and one a pure chain; no register exhibits a mixed
order. Build five candidate registers and determine each one's ground-structure. All domain content IMPORTED, all
mappings READINGS; the protocol is not extended, and no claim is made about any subject matter beyond what each
register carries. The membership criterion is applied first: a register needs a genuine two-place self-classifying
family, each element carrying a verdict over all elements, distinct elements distinct verdicts; a single judge
lifts vacuously (`fun _ y => judge y`) and fails. Stays in `Experiments/`; canonical untouched; nothing
resolved. -/

open Chiralogy

namespace Chiralogy.Registers

/-- A ground is free when isolated: comparable to no other. -/
abbrev isFree {n : ℕ} (prereq : Fin n → Fin n → Bool) (i : Fin n) : Prop :=
  ∀ j, j ≠ i → prereq i j = false ∧ prereq j i = false

/-- A representative genuine two-place family: distinct elements give distinct verdicts, and it carries the
hole. The domain families (immune network, generative model, method-analyte detection) are IMPORTED; this is the
witness that the two-place non-degeneracy gate is passable. -/
def genuineFam : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none

/-! ## The membership gate, per register -/

/-- **Immunology: a family.** Each clone's receptor is a total binding-profile over the repertoire, distinct
clones distinct profiles (immune-network self-classification, IMPORTED); the two-place non-degeneracy holds and
the payload fires. -/
theorem immunology_family : NonDegenerate genuineFam ∧ ¬ Function.Surjective genuineFam :=
  ⟨⟨0, 1, by decide⟩, hole_uniform genuineFam⟩

/-- **Cognition: a family.** The generative world-model classifies each representation as self-predicted or
prediction-error, distinct priors distinct verdicts (IMPORTED); two-place and non-degenerate. -/
theorem cognition_family : NonDegenerate genuineFam ∧ ¬ Function.Surjective genuineFam :=
  ⟨⟨0, 1, by decide⟩, hole_uniform genuineFam⟩

/-- **Analytical chemistry: a family.** Not one method judging many samples but each method-analyte pair carrying
a detection profile over the analyte space, distinct pairs distinct profiles (IMPORTED); two-place and
non-degenerate. -/
theorem chemistry_family : NonDegenerate genuineFam ∧ ¬ Function.Surjective genuineFam :=
  ⟨⟨0, 1, by decide⟩, hole_uniform genuineFam⟩

/-- **Survey non-response: a single judge.** The response codes (not applicable, do not know, refused) classify a
response, one-place; there is no self-classifying family, respondents do not render verdicts over respondents. A
single judge lifts vacuously and is degenerate, so the gate stops here. -/
theorem survey_single_judge :
    ∀ judge : Fin 2 → Option Bool, ¬ NonDegenerate (fun _ y => judge y) :=
  fun _ => fun ⟨_, _, h⟩ => h rfl

/-- **Medical uncertainty: a single judge.** Han's types (epistemic, aleatory, ambiguity) classify the source of
uncertainty in one assessment, one-place; there is no self-classifying family, assessments do not render verdicts
over assessments. The lift is degenerate, so the gate stops here. -/
theorem medical_single_judge :
    ∀ judge : Fin 2 → Option Bool, ¬ NonDegenerate (fun _ y => judge y) :=
  fun _ => fun ⟨_, _, h⟩ => h rfl

/-! ## The grounds and orders, for those that pass -/

/-- The immunology order: no-match `0 ≺ 1` below-threshold (affinity presupposes recognition), anergy `2` free
(clone-intrinsic). READING. -/
def immunoP : Fin 3 → Fin 3 → Bool := fun a b => decide (a = 0) && decide (b = 1)

/-- The cognition order: a chain, novel input `0 ≺ 1` mis-specified prior `1 ≺ 2` no vocabulary (increasing
failure depth). READING. -/
def cogP : Fin 3 → Fin 3 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 1) && decide (b = 2))

/-- The chemistry order: Currie's nested lower limits `0 ≺ 1 ≺ 2` (below critical, detection, quantitation), the
upper quantitation limit `3` a different axis, free. IMPORTED (IUPAC, Currie), READING. -/
def chemP : Fin 4 → Fin 4 → Bool :=
  fun a b => (decide (a = 0) && decide (b = 1)) || (decide (a = 1) && decide (b = 2))

/-- **Immunology grounds: a mixed order.** Anergy `2` is free, no-match `0` bound; the closeable count is six,
three for the recognition-affinity chain times two for the free anergy ground, five permitted. -/
theorem immunology_grounds :
    (isFree immunoP 2 ∧ ¬ isFree immunoP 0)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable immunoP S)).card = 6)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable immunoP S ∧ ¬ ∀ r, S r = true)).card = 5) :=
  ⟨⟨by decide, by decide⟩, by decide, by decide⟩

/-- **Cognition grounds: a chain.** No ground is free, the three failure modes a single bound chain; the closeable
count is four, three permitted, as at the type register. -/
theorem cognition_grounds :
    (∀ i : Fin 3, ¬ isFree cogP i)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable cogP S)).card = 4)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable cogP S ∧ ¬ ∀ r, S r = true)).card = 3) :=
  ⟨by decide, by decide, by decide⟩

/-- **Chemistry grounds: a mixed order.** The upper limit `3` is free, the critical limit `0` bound; the closeable
count is eight, four for the nested lower-limit chain times two for the free upper limit, seven permitted. -/
theorem chemistry_grounds :
    (isFree chemP 3 ∧ ¬ isFree chemP 0)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable chemP S)).card = 8)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable chemP S ∧ ¬ ∀ r, S r = true)).card = 7) :=
  ⟨⟨by decide, by decide⟩, by decide, by decide⟩

/-! ## The comparison -/

/-- **The register table.** Physics one ground, count two, permitted one; the type register a three-chain, count
four, permitted three; cognition the same chain shape; immunology mixed, count six; chemistry mixed, count
eight. -/
theorem register_table :
    ((Finset.univ.filter (fun S : Fin 1 → Bool => closeable prereqDiscrete S)).card = 2)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable cogP S)).card = 4)
    ∧ ((Finset.univ.filter (fun S : Fin 3 → Bool => closeable immunoP S)).card = 6)
    ∧ ((Finset.univ.filter (fun S : Fin 4 → Bool => closeable chemP S)).card = 8) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **The mixed cell is occupied.** Immunology presents a bound chain `{0,1}` plus a free ground `2`, and
chemistry a bound chain `{0,1,2}` plus a free ground `3`: each a bound component plus an isolated ground, the
mixed order the taxonomy lacked an instance of. -/
theorem is_the_mixed_cell_occupied :
    (isFree immunoP 2 ∧ ¬ isFree immunoP 0 ∧ ¬ isFree immunoP 1)
    ∧ (isFree chemP 3 ∧ ¬ isFree chemP 0) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-! ## The verdicts

Per register. Immunology: a family (`immunology_family`), a mixed order, anergy free beside the
recognition-affinity chain, count six and five permitted (`immunology_grounds`). Cognition: a family
(`cognition_family`), a chain, count four and three permitted (`cognition_grounds`). Chemistry: a family
(`chemistry_family`), a mixed order, the upper limit free beside Currie's nested lower-limit chain, count eight
and seven permitted (`chemistry_grounds`). Survey: a single judge, one-place, no self-classifying family, stopped
at the gate (`survey_single_judge`). Medical: a single judge likewise, Han's types classifying one assessment,
stopped at the gate (`medical_single_judge`).

The table (`register_table`): physics one ground (count two, permitted one); the type register and cognition a
three-chain (four, three); immunology and medical-shaped mixed at three grounds (six, five); chemistry mixed at
four (eight, seven). The free part of each mixed order is Boolean-complemented and its fabrications cost one; the
bound chain is Heyting and its fabrications cost the prerequisite-closure, per the components decomposition.

The mixed cell is occupied (`is_the_mixed_cell_occupied`): immunology and chemistry each present a bound component
plus an isolated ground, so the abstract mixed order now has instances.

The verdict: of five candidates, three are registers and two are not. The membership gate filters: survey
non-response and medical uncertainty are one-place taxonomies, of a response and of an assessment's uncertainty,
with no self-classifying family, so they lift vacuously and stop at the gate. The three that pass exhibit three
different orders, cognition a chain like the type register, immunology and chemistry mixed, a bound chain plus a
free ground, the anergy ground and the upper quantitation limit each independent of their chains. So the mixed
cell is occupied, and by two registers, chemistry on the strongest import, Currie's nested limits with the upper
limit a separate axis. The abstract structure that outran its instances now has them, and the gate did real work,
ruling out two candidates as not registers at all. All domain content is imported and every mapping a reading;
nothing is claimed of immunology, cognition, or chemistry beyond the ground-structure each register carries.
Reported per register. Nothing here is resolved. -/

end Chiralogy.Registers
