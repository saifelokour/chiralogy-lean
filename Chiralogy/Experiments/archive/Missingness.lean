import Chiralogy

/-! # Experiment: does missing-data theory occupy a cell?

Archived: its findings are readings about domains the framework does not chart. Rubin's mechanisms remain a
candidate third register (the three-chain, alongside physics and type systems), unbuilt by decision rather than
by failure; compositional missingness turned out chained, not free.

The taxonomy has two occupied cells (physics at n = 1, type systems at the three-chain) and five empty,
including the whole free column. Missing-data theory offers two independently-developed classifications of
absence-kinds. Test whether either occupies a cell.

All domain content is IMPORTED; all mappings are READINGS with defeasible fidelity. The register construction
and the order structure are THEOREMS; that a candidate's closure respects a given order is a reading. No claim
is made about statistics. Stays in `Experiments/`; canonical untouched; nothing resolved. -/

open Chiralogy

namespace Chiralogy.Missingness

/-- The chain coherence: closing ground 2 presupposes 1, closing 1 presupposes 0. -/
abbrev cohChain (c : Fin 3 → Bool) : Prop := (c 2 = true → c 1 = true) ∧ (c 1 = true → c 0 = true)

/-! ## Part 1: Rubin's mechanisms (IMPORTED)

Three grounds: missing completely at random, missing at random, missing not at random. Stances: listwise
deletion, multiple imputation, selection models. -/

/-- Rubin's three grounds, IMPORTED. -/
inductive RubinGround | mcar | mar | mnar
  deriving DecidableEq

/-- The classification: a verdict and one term per ground. -/
def rubinClassify : Fin 4 → Fin 4 → Bool ⊕ RubinGround := fun x _ =>
  if x = 0 then Sum.inl true
  else if x = 1 then Sum.inr .mcar
  else if x = 2 then Sum.inr .mar
  else Sum.inr .mnar

/-- The Rubin register: carrier of cases, classification into a three-ground level. -/
def rubinRegister : Member where
  X := Fin 4
  B := Bool ⊕ RubinGround
  canDiffer := ⟨Sum.inl true, Sum.inr .mcar, by decide⟩
  classify := rubinClassify
  nondegenerate := ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩

/-- **Rubin's three grounds are distinct and reachable.** Each mechanism is reached by a case, there is a
verdict, and the three are pairwise distinct. -/
theorem rubin_three_grounds :
    rubinClassify 1 0 = Sum.inr RubinGround.mcar
    ∧ rubinClassify 2 0 = Sum.inr RubinGround.mar
    ∧ rubinClassify 3 0 = Sum.inr RubinGround.mnar
    ∧ rubinClassify 0 0 = Sum.inl true
    ∧ RubinGround.mcar ≠ RubinGround.mar
    ∧ RubinGround.mar ≠ RubinGround.mnar
    ∧ RubinGround.mcar ≠ RubinGround.mnar :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide, by decide⟩

/-- **What order do they carry.** The closure operation, having a valid method for a kind, respects a chain,
not the bare assumption-strength nesting: a method valid under the general MNAR is valid under MAR and MCAR, so
closing a later ground presupposes closing the earlier. Closing MAR alone, or MNAR alone, is incoherent; the
chain gives three permitted moves, not the seven of the discrete order nor the four of a branching. READING:
the identification of Rubin's closure with this chain. -/
theorem what_order_do_they_carry :
    (¬ cohChain (fun g => decide (g = (1 : Fin 3))))
    ∧ (¬ cohChain (fun g => decide (g = (2 : Fin 3))))
    ∧ (Finset.univ.filter (fun c : Fin 3 → Bool => cohChain c ∧ ¬ ∀ r, c r = true)).card = 3 :=
  ⟨by decide, by decide, by decide⟩

/-- **The stances land on distinct moves** (READING, defeasible). Listwise deletion closes `{MCAR}`, multiple
imputation `{MCAR, MAR}`, selection models the full closure (the attempt, resolving the nonignorable by
unverifiable assumptions). Three distinct closures, two permitted, one the prohibition. Stated, not asserted. -/
def stances_land_where : Prop :=
  ((fun g : Fin 3 => decide (g = 0)) ≠ (fun g : Fin 3 => decide (g ≠ 2)))
    ∧ ((fun g : Fin 3 => decide (g ≠ 2)) ≠ (fun _ : Fin 3 => true))
    ∧ cohChain (fun g => decide (g = (0 : Fin 3)))
    ∧ cohChain (fun g => decide (g ≠ (2 : Fin 3)))
    ∧ (∀ r : Fin 3, (fun _ => true) r = true)

/-! ## Part 2: compositional missingness (IMPORTED)

Three grounds: a missing entity (absent record), a missing attribute (unrecorded field), a missing value (empty
cell). This is the free-cell candidate; the free cell has been empty. Test independence rather than assume it. -/

/-- The compositional grounds, IMPORTED. -/
inductive CompGround | entity | attribute | value
  deriving DecidableEq

/-- The classification: a verdict and one term per ground. -/
def compClassify : Fin 4 → Fin 4 → Bool ⊕ CompGround := fun x _ =>
  if x = 0 then Sum.inl true
  else if x = 1 then Sum.inr .entity
  else if x = 2 then Sum.inr .attribute
  else Sum.inr .value

/-- The compositional register. -/
def compRegister : Member where
  X := Fin 4
  B := Bool ⊕ CompGround
  canDiffer := ⟨Sum.inl true, Sum.inr .entity, by decide⟩
  classify := compClassify
  nondegenerate := ⟨0, 1, fun h => absurd (congrFun h 0) (by decide)⟩

/-- **Compositional three grounds are distinct and reachable.** -/
theorem compositional_three_grounds :
    compClassify 1 0 = Sum.inr CompGround.entity
    ∧ compClassify 2 0 = Sum.inr CompGround.attribute
    ∧ compClassify 3 0 = Sum.inr CompGround.value
    ∧ compClassify 0 0 = Sum.inl true
    ∧ CompGround.entity ≠ CompGround.attribute
    ∧ CompGround.attribute ≠ CompGround.value
    ∧ CompGround.entity ≠ CompGround.value :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide, by decide⟩

/-- **Compositional missingness is chained, not free.** A prerequisite lurks: a missing value presupposes a
present attribute, a missing attribute presupposes a present entity, so closing value alone or attribute alone
is incoherent. The order is the chain (entity ≺ attribute ≺ value), three permitted moves, not the discrete
order's seven. The free-looking candidate springs the same trap as type systems and database nulls. -/
theorem compositional_is_chained :
    (¬ cohChain (fun g => decide (g = (2 : Fin 3))))
    ∧ (¬ cohChain (fun g => decide (g = (1 : Fin 3))))
    ∧ (Finset.univ.filter (fun c : Fin 3 → Bool => cohChain c ∧ ¬ ∀ r, c r = true)).card = 3 :=
  ⟨by decide, by decide, by decide⟩

/-! ## Part 3: occupancy (READINGS) -/

/-- **Which cells are filled** (READING, defeasible). Both candidates carry the chain, so both occupy the
three-chain, already held by type systems: second and third instances of one cell, not new cells. The
branchings (V, Λ, four permitted) and the discrete cell stay empty. Stated, not asserted. -/
def which_cells_filled : Prop :=
  (Finset.univ.filter (fun c : Fin 3 → Bool => cohChain c ∧ ¬ ∀ r, c r = true)).card = 3

/-- **The free column status** (READING, defeasible). The free column stays empty: the discrete n = 3 cell
(seven permitted, Boolean) has no domain instance. Four independent candidates, type systems, database nulls,
Rubin's mechanisms, compositional missingness, have now been tested and all were forced. The free structures
are realized by the tower's constructed levels, not by any domain examined. Stated, not asserted. -/
def free_column_status : Prop :=
  (Finset.univ.filter (fun c : Fin 3 → Bool => ¬ ∀ r, c r = true)).card = 7

/-! ## The verdict

Part 1: Rubin's mechanisms carry a chain. The closure operation respects a prerequisite, a method valid under
the general condition being valid under the special, not the bare assumption-strength nesting
(`what_order_do_they_carry`): closing MAR presupposes MCAR, closing MNAR presupposes both, three permitted moves.
The three stances land on distinct closures, listwise at `{MCAR}`, imputation at `{MCAR, MAR}`, selection at the
full closure, the attempt (`stances_land_where`). So Rubin occupies the three-chain, a second instance beside
type systems, not a new cell.

Part 2: compositional missingness is chained, not free. A missing value presupposes a present attribute and a
present entity, so the order is entity ≺ attribute ≺ value, three permitted, not the discrete seven
(`compositional_is_chained`). The free-cell candidate sprang the trap: it looked independent and carried a
mereological prerequisite.

Part 3: no new cell, and the free column stays empty. Both candidates fill the three-chain
(`which_cells_filled`); the branchings and the discrete cell are still unoccupied (`free_column_status`). Four
independent domains have now been tested and every one was forced; the free Boolean structures appear to be
realized only by the framework's constructed levels, not by any domain. The wanted result, filling the free
cell, did not survive the independence test. All mappings are READINGS, defeasible. Nothing here is resolved. -/

end Chiralogy.Missingness
