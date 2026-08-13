import Chiralogy.Model.InformationOrder
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Powerset

/-! # The n-ary assemblage

The general n-ary assemblage on a heterogeneous product `∀ i : Fin n, X i`: classify a pair by the unique
coordinate it differs in, if exactly one, else by a cross import. Uniform in `n`, independent of the ordered
binary `assembleClassify`. Its intrinsic positive characterization (`nary_form_iff`): a classification is an
n-ary assemblage iff every differ-in-one cell depends only on its coordinate. The two moves commute with
assembly under a single quantified coherence condition (with tight absence/presence refinements), realized
uniformly by a sum scale; and the form-preserving region-step paths descend to the bottom and ascend to a
scale-forced ceiling.

Depends on `Model/InformationOrder` (the order `cLE`, bottom `botC`, `isTotal`, `maximal_iff_total`, the moves)
and thereby `Model/Apophatic`; no dependence on `Model/Assemblage`. -/

namespace Chiralogy

/-- **Distinct maxima are incomparable.** Any two distinct total classifications have no order relation: the only
relation two totalizations can bear is equality. (Hooks the order alone; placed here for `ascent_ceilings_incomparable`.) -/
theorem distinct_maxima_incomparable {X : Type} [DecidableEq X] (c d : X → X → Option Bool)
    (hc : isTotal c) (hd : isTotal d) (hne : c ≠ d) : ¬ cLE c d ∧ ¬ cLE d c := by
  refine ⟨fun h => hne (cLE_antisymm h ((maximal_iff_total c).2 hc d h)), ?_⟩
  intro h; exact hne (cLE_antisymm ((maximal_iff_total d).2 hd c h) h)

variable {n : ℕ} {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-! ## The construction -/

/-- Two points differ in exactly coordinate `i`. -/
abbrev differsInOne (a b : ∀ i, X i) (i : Fin n) : Prop := a i ≠ b i ∧ ∀ j, j ≠ i → a j = b j

omit [∀ i, DecidableEq (X i)] in
/-- **The differing coordinate is unique.** -/
theorem differsInOne_unique {a b : ∀ i, X i} {p q : Fin n}
    (hp : differsInOne a b p) (hq : differsInOne a b q) : p = q := by
  by_contra hpq; exact hp.1 (hq.2 p hpq)

/-- The general n-ary assemblage: the unique differing coordinate picks its factor, else the import. -/
noncomputable def nary (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    (∀ i, X i) → (∀ i, X i) → Option Bool :=
  fun a b => if h : ∃ i, differsInOne a b i then c h.choose (a h.choose) (b h.choose) else imp a b

/-- On a pair differing in exactly `i`, the n-ary reads factor `i` at that coordinate. -/
theorem nary_apply_differ (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) {a b : ∀ i, X i} {i : Fin n}
    (hi : differsInOne a b i) : nary c imp a b = c i (a i) (b i) := by
  have hex : ∃ i, differsInOne a b i := ⟨i, hi⟩
  have hch : hex.choose = i := differsInOne_unique hex.choose_spec hi
  unfold nary; rw [dif_pos hex, hch]

/-- On a pair differing in more than one coordinate (or none), the n-ary reads the import. -/
theorem nary_apply_imp (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) {a b : ∀ i, X i}
    (hne : ¬ ∃ i, differsInOne a b i) : nary c imp a b = imp a b := by
  unfold nary; rw [dif_neg hne]

/-- **The n-ary is monotone in every factor and the import**, the partition depending only on the pair. -/
theorem nary_mono {c c' : ∀ i, X i → X i → Option Bool}
    {imp imp' : (∀ i, X i) → (∀ i, X i) → Option Bool}
    (h : ∀ i, cLE (c i) (c' i)) (hi : cLE imp imp') : cLE (nary c imp) (nary c' imp') := by
  intro a b
  by_cases hex : ∃ i, differsInOne a b i
  · rw [nary_apply_differ c imp hex.choose_spec, nary_apply_differ c' imp' hex.choose_spec]
    exact h hex.choose (a hex.choose) (b hex.choose)
  · rw [nary_apply_imp c imp hex, nary_apply_imp c' imp' hex]; exact hi a b

/-! ## Form: the intrinsic positive characterization -/

/-- **The n-ary form signature: a differ-in-`i` cell depends only on coordinate `i`.** Axiom-free, uniform in `n`. -/
theorem nary_region_independent (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) {a b a' b' : ∀ i, X i} {i : Fin n}
    (hi : differsInOne a b i) (hi' : differsInOne a' b' i) (ha : a i = a' i) (hb : b i = b' i) :
    nary c imp a b = nary c imp a' b' := by
  rw [nary_apply_differ c imp hi, nary_apply_differ c imp hi', ha, hb]

/-- The intrinsic n-ary predicate: every differ-in-one cell depends only on its own coordinate. No factorization. -/
def isAssemblageN {V : Type} (A : (∀ i, X i) → (∀ i, X i) → V) : Prop :=
  ∀ (a b a' b' : ∀ i, X i) (i : Fin n), differsInOne a b i → differsInOne a' b' i →
    a i = a' i → b i = b' i → A a b = A a' b'

/-- **The positive characterization, general `n`.** A classification is an n-ary assemblage IFF every
differ-in-one cell depends only on its coordinate. Sufficiency reconstructs each factor from a basepoint via
`Function.update`, so "is an n-ary assemblage" is checkable with no reference to any factorization. -/
theorem nary_form_iff [∀ i, Inhabited (X i)] (A : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    (∃ c imp, A = nary c imp) ↔ isAssemblageN A := by
  constructor
  · rintro ⟨c, imp, rfl⟩ a b a' b' i hi hi' ha hb
    exact nary_region_independent c imp hi hi' ha hb
  · intro hInd
    refine ⟨fun i x y => A (Function.update (fun _ => default) i x) (Function.update (fun _ => default) i y),
      A, ?_⟩
    funext a b
    by_cases hex : ∃ i, differsInOne a b i
    · rw [nary_apply_differ _ _ hex.choose_spec]
      refine hInd a b _ _ hex.choose hex.choose_spec
        ⟨?_, fun j hj => ?_⟩ ?_ ?_
      · simp only [Function.update_self]; exact hex.choose_spec.1
      · simp only [Function.update_of_ne hj]
      · simp only [Function.update_self]
      · simp only [Function.update_self]
    · rw [nary_apply_imp _ _ hex]

/-! ## Commutation with the moves -/

/-- **The coherence condition unifies.** The `n` per-region conditions collapse to ONE condition quantified over
the differing coordinate; the import is handled by totalizing with `s`. -/
theorem nary_totalization_commutes (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (hs : ∀ a b : ∀ i, X i, ∀ hex : ∃ i, differsInOne a b i,
      decide (s b ≤ s a) = decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose))) :
    totalization s (nary c imp)
      = nary (fun i => totalization (si i) (c i)) (totalization s imp) := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · have hL : totalization s (nary c imp) a b
        = some ((c hex.choose (a hex.choose) (b hex.choose)).getD (decide (s b ≤ s a))) := by
      simp only [totalization, nary_apply_differ c imp hex.choose_spec]
    have hR : nary (fun i => totalization (si i) (c i)) (totalization s imp) a b
        = some ((c hex.choose (a hex.choose) (b hex.choose)).getD
            (decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose)))) := by
      rw [nary_apply_differ (fun i => totalization (si i) (c i)) (totalization s imp) hex.choose_spec]
      simp only [totalization]
    rw [hL, hR, hs a b hex]
  · have hL : totalization s (nary c imp) a b = some ((imp a b).getD (decide (s b ≤ s a))) := by
      simp only [totalization, nary_apply_imp c imp hex]
    have hR : nary (fun i => totalization (si i) (c i)) (totalization s imp) a b
        = some ((imp a b).getD (decide (s b ≤ s a))) := by
      rw [nary_apply_imp (fun i => totalization (si i) (c i)) (totalization s imp) hex]
      simp only [totalization]
    rw [hL, hR]

/-- **General-n absence refinement.** The coherence condition need hold only at absent differ-in-one cells. -/
theorem nary_totalization_commutes_on_absences (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (hs : ∀ a b : ∀ i, X i, ∀ hex : ∃ i, differsInOne a b i,
      c hex.choose (a hex.choose) (b hex.choose) = none →
      decide (s b ≤ s a) = decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose))) :
    totalization s (nary c imp)
      = nary (fun i => totalization (si i) (c i)) (totalization s imp) := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · have hL : totalization s (nary c imp) a b
        = some ((c hex.choose (a hex.choose) (b hex.choose)).getD (decide (s b ≤ s a))) := by
      simp only [totalization, nary_apply_differ c imp hex.choose_spec]
    have hR : nary (fun i => totalization (si i) (c i)) (totalization s imp) a b
        = some ((c hex.choose (a hex.choose) (b hex.choose)).getD
            (decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose)))) := by
      rw [nary_apply_differ (fun i => totalization (si i) (c i)) (totalization s imp) hex.choose_spec]
      simp only [totalization]
    rw [hL, hR]
    rcases hc : c hex.choose (a hex.choose) (b hex.choose) with _ | v
    · rw [Option.getD_none, Option.getD_none, hs a b hex hc]
    · rw [Option.getD_some, Option.getD_some]
  · have hL : totalization s (nary c imp) a b = some ((imp a b).getD (decide (s b ≤ s a))) := by
      simp only [totalization, nary_apply_imp c imp hex]
    have hR : nary (fun i => totalization (si i) (c i)) (totalization s imp) a b
        = some ((imp a b).getD (decide (s b ≤ s a))) := by
      rw [nary_apply_imp (fun i => totalization (si i) (c i)) (totalization s imp) hex]
      simp only [totalization]
    rw [hL, hR]

/-- **General-n necessity (totalization).** Commutation forces absence-coherence at each absent differ-in-one
cell; with the sufficiency above this is the tight iff, in the quantified-coordinate form. -/
theorem nary_totalization_commutation_forces_absence_coherence (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (h : totalization s (nary c imp) = nary (fun i => totalization (si i) (c i)) (totalization s imp))
    (a b : ∀ i, X i) (hex : ∃ i, differsInOne a b i)
    (hc : c hex.choose (a hex.choose) (b hex.choose) = none) :
    decide (s b ≤ s a) = decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose)) := by
  have hcong := congrFun (congrFun h a) b
  have hL : totalization s (nary c imp) a b = some (decide (s b ≤ s a)) := by
    simp only [totalization, nary_apply_differ c imp hex.choose_spec, hc, Option.getD_none]
  have hR : nary (fun i => totalization (si i) (c i)) (totalization s imp) a b
      = some (decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose))) := by
    rw [nary_apply_differ (fun i => totalization (si i) (c i)) (totalization s imp) hex.choose_spec]
    simp only [totalization, hc, Option.getD_none]
  rw [hL, hR] at hcong
  exact Option.some_inj.mp hcong

/-- **General-n presence refinement (partialization sufficiency).** The mask need agree only at present
differ-in-one cells. -/
theorem nary_partialization_commutes_on_presences (w : (∀ i, X i) → (∀ i, X i) → Bool)
    (wi : ∀ i, X i → X i → Bool) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (hw : ∀ a b : ∀ i, X i, ∀ hex : ∃ i, differsInOne a b i,
      c hex.choose (a hex.choose) (b hex.choose) ≠ none →
      w a b = wi hex.choose (a hex.choose) (b hex.choose)) :
    partialization w (nary c imp)
      = nary (fun i => partialization (wi i) (c i)) (partialization w imp) := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · have hL : partialization w (nary c imp) a b
        = (if w a b then none else c hex.choose (a hex.choose) (b hex.choose)) := by
      simp only [partialization, nary_apply_differ c imp hex.choose_spec]
    have hR : nary (fun i => partialization (wi i) (c i)) (partialization w imp) a b
        = (if wi hex.choose (a hex.choose) (b hex.choose) then none
            else c hex.choose (a hex.choose) (b hex.choose)) := by
      rw [nary_apply_differ (fun i => partialization (wi i) (c i)) (partialization w imp) hex.choose_spec]
      simp only [partialization]
    rw [hL, hR]
    rcases hc : c hex.choose (a hex.choose) (b hex.choose) with _ | v
    · simp
    · rw [hw a b hex (by rw [hc]; exact Option.some_ne_none v)]
  · have hL : partialization w (nary c imp) a b = (if w a b then none else imp a b) := by
      simp only [partialization, nary_apply_imp c imp hex]
    have hR : nary (fun i => partialization (wi i) (c i)) (partialization w imp) a b
        = (if w a b then none else imp a b) := by
      rw [nary_apply_imp (fun i => partialization (wi i) (c i)) (partialization w imp) hex]
      simp only [partialization]
    rw [hL, hR]

/-- **General-n necessity (partialization).** Commutation forces presence-coherence at each present differ-in-one
cell; with the sufficiency above this is the general-n presence-coherence iff. -/
theorem nary_partialization_commutation_forces_presence_coherence (w : (∀ i, X i) → (∀ i, X i) → Bool)
    (wi : ∀ i, X i → X i → Bool) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (h : partialization w (nary c imp) = nary (fun i => partialization (wi i) (c i)) (partialization w imp))
    (a b : ∀ i, X i) (hex : ∃ i, differsInOne a b i) (v : Bool)
    (hc : c hex.choose (a hex.choose) (b hex.choose) = some v) :
    w a b = wi hex.choose (a hex.choose) (b hex.choose) := by
  have hcong := congrFun (congrFun h a) b
  have hL : partialization w (nary c imp) a b = (if w a b then none else some v) := by
    simp only [partialization, nary_apply_differ c imp hex.choose_spec, hc]
  have hR : nary (fun i => partialization (wi i) (c i)) (partialization w imp) a b
      = (if wi hex.choose (a hex.choose) (b hex.choose) then none else some v) := by
    rw [nary_apply_differ (fun i => partialization (wi i) (c i)) (partialization w imp) hex.choose_spec]
    simp only [partialization, hc]
  rw [hL, hR] at hcong
  by_cases hw : w a b = true
  · by_cases hw1 : wi hex.choose (a hex.choose) (b hex.choose) = true
    · rw [hw, hw1]
    · rw [if_pos hw, if_neg hw1] at hcong; exact absurd hcong (by simp)
  · by_cases hw1 : wi hex.choose (a hex.choose) (b hex.choose) = true
    · rw [if_neg hw, if_pos hw1] at hcong; exact absurd hcong (by simp)
    · rw [Bool.not_eq_true] at hw hw1; rw [hw, hw1]

/-- **Assembling partialized factors is below the n-ary composite**, hence a partialization of it (structural). -/
theorem nary_assembled_partialization_is_below (w : ∀ i, X i → X i → Bool)
    (w' : (∀ i, X i) → (∀ i, X i) → Bool) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    cLE (nary (fun i => partialization (w i) (c i)) (partialization w' imp)) (nary c imp) :=
  nary_mono (fun i => partialization_le_c (w i) (c i)) (partialization_le_c w' imp)

theorem nary_assembled_partialization_is_a_partialization (w : ∀ i, X i → X i → Bool)
    (w' : (∀ i, X i) → (∀ i, X i) → Bool) (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    ∃ W, nary (fun i => partialization (w i) (c i)) (partialization w' imp)
        = partialization W (nary c imp) :=
  (below_iff_partialization _ _).1 (nary_assembled_partialization_is_below w w' c imp)

/-! ## The uniform sum scale -/

open Finset in
omit [∀ i, DecidableEq (X i)] in
/-- **The sum scale realizes coherence.** For per-coordinate scales `si`, the scale `a ↦ ∑ j, si j (a j)`
satisfies the single quantified coherence condition, because on a differ-in-one pair every other summand cancels. -/
theorem nary_sum_scale_coherent (si : ∀ i, X i → Nat) (a b : ∀ i, X i)
    (hex : ∃ i, differsInOne a b i) :
    decide ((∑ j, si j (b j)) ≤ ∑ j, si j (a j))
      = decide (si hex.choose (b hex.choose) ≤ si hex.choose (a hex.choose)) := by
  have hi : differsInOne a b hex.choose := hex.choose_spec
  have htail : (∑ j ∈ univ.erase hex.choose, si j (a j)) = ∑ j ∈ univ.erase hex.choose, si j (b j) :=
    Finset.sum_congr rfl (fun j hj => by rw [hi.2 j (Finset.ne_of_mem_erase hj)])
  have ha : (∑ j, si j (a j)) = si hex.choose (a hex.choose) + ∑ j ∈ univ.erase hex.choose, si j (a j) :=
    (Finset.add_sum_erase univ (fun j => si j (a j)) (mem_univ hex.choose)).symm
  have hb : (∑ j, si j (b j)) = si hex.choose (b hex.choose) + ∑ j ∈ univ.erase hex.choose, si j (b j) :=
    (Finset.add_sum_erase univ (fun j => si j (b j)) (mem_univ hex.choose)).symm
  rw [ha, hb, htail]
  exact decide_eq_decide.mpr (by omega)

open Finset in
/-- **A canonical scale for commutation at every `n`.** Totalizing by the sum scale commutes with assembling the
per-coordinate totalizations, uniformly, with no side condition beyond the per-coordinate scales. -/
theorem nary_totalization_commutes_sum (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    totalization (fun a => ∑ j, si j (a j)) (nary c imp)
      = nary (fun i => totalization (si i) (c i)) (totalization (fun a => ∑ j, si j (a j)) imp) :=
  nary_totalization_commutes _ si c imp (fun a b hex => nary_sum_scale_coherent si a b hex)

/-! ## Form-preserving paths -/

/-- `nary` of all-absent factors and absent import is the bottom. -/
theorem nary_bot : nary (fun i => botC (X i)) (botC (∀ i, X i)) = botC (∀ i, X i) := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · rw [nary_apply_differ (fun i => botC (X i)) (botC (∀ i, X i)) hex.choose_spec]; rfl
  · rw [nary_apply_imp (fun i => botC (X i)) (botC (∀ i, X i)) hex]

/-- `nary` of total factors and total import is total (a maximal element). -/
theorem nary_isTotal {c : ∀ i, X i → X i → Option Bool} {imp : (∀ i, X i) → (∀ i, X i) → Option Bool}
    (hc : ∀ i, isTotal (c i)) (hi : isTotal imp) : isTotal (nary c imp) := by
  intro a b
  by_cases hex : ∃ i, differsInOne a b i
  · rw [nary_apply_differ c imp hex.choose_spec]; exact hc hex.choose (a hex.choose) (b hex.choose)
  · rw [nary_apply_imp c imp hex]; exact hi a b

/-- Factors of the descent at step `k`: the first `k` emptied. -/
noncomputable def descentFactors (c : ∀ i, X i → X i → Option Bool) (k : Nat) :
    ∀ i, X i → X i → Option Bool := fun i => if i.val < k then botC (X i) else c i

/-- Import of the descent: emptied only after all factors. -/
noncomputable def descentImp (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) :
    (∀ i, X i) → (∀ i, X i) → Option Bool := if n < k then botC (∀ i, X i) else imp

/-- The descent chain: at step `k` the first `k` factors are emptied, then the import. -/
noncomputable def descentPath (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) : (∀ i, X i) → (∀ i, X i) → Option Bool :=
  nary (descentFactors c k) (descentImp imp k)

/-- The chain starts at the given assemblage. -/
theorem descentPath_zero (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) : descentPath c imp 0 = nary c imp := by
  have hf : descentFactors c 0 = c := by
    funext i; simp only [descentFactors]; rw [if_neg (by omega : ¬ i.val < 0)]
  have himp : descentImp imp 0 = imp := by
    simp only [descentImp]; rw [if_neg (by omega : ¬ n < 0)]
  unfold descentPath; rw [hf, himp]

/-- **Every intermediate is in form.** Each `descentPath` step is a `nary`, hence an n-ary assemblage. -/
theorem descentPath_isAssemblageN [∀ i, Inhabited (X i)] (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) : isAssemblageN (descentPath c imp k) :=
  (nary_form_iff _).mp ⟨descentFactors c k, descentImp imp k, rfl⟩

/-- **The chain descends in the information order.** Each step empties one region. -/
theorem descentPath_descends (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) :
    cLE (descentPath c imp (k + 1)) (descentPath c imp k) := by
  unfold descentPath
  apply nary_mono
  · intro i; simp only [descentFactors]
    by_cases h2 : i.val < k + 1
    · by_cases h1 : i.val < k
      · rw [if_pos h2, if_pos h1]; exact cLE_refl _
      · rw [if_pos h2, if_neg h1]; exact botC_le _
    · rw [if_neg h2, if_neg (show ¬ i.val < k by omega)]; exact cLE_refl _
  · simp only [descentImp]
    by_cases h2 : n < k + 1
    · by_cases h1 : n < k
      · rw [if_pos h2, if_pos h1]; exact cLE_refl _
      · rw [if_pos h2, if_neg h1]; exact botC_le _
    · rw [if_neg h2, if_neg (show ¬ n < k by omega)]; exact cLE_refl _

/-- **The chain terminates at the order-bottom.** After `n+1` steps everything is emptied. -/
theorem descentPath_reaches_bot (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) : descentPath c imp (n + 1) = botC (∀ i, X i) := by
  have hf : descentFactors c (n + 1) = fun i => botC (X i) := by
    funext i; simp only [descentFactors]; rw [if_pos (Nat.lt_succ_of_lt i.isLt)]
  have himp : descentImp imp (n + 1) = botC (∀ i, X i) := by
    simp only [descentImp]; rw [if_pos (Nat.lt_succ_self n)]
  unfold descentPath; rw [hf, himp, nary_bot]

/-- Factors of the ascent at step `k`: the first `k` totalized. -/
noncomputable def ascentFactors (si : ∀ i, X i → Nat) (c : ∀ i, X i → X i → Option Bool) (k : Nat) :
    ∀ i, X i → X i → Option Bool := fun i => if i.val < k then totalization (si i) (c i) else c i

noncomputable def ascentImp (s : (∀ i, X i) → Nat) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) :
    (∀ i, X i) → (∀ i, X i) → Option Bool := if n < k then totalization s imp else imp

/-- The ascent chain: at step `k` the first `k` factors are totalized, then the import. -/
noncomputable def ascentPath (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) :
    (∀ i, X i) → (∀ i, X i) → Option Bool := nary (ascentFactors si c k) (ascentImp s imp k)

theorem ascentPath_zero (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    ascentPath s si c imp 0 = nary c imp := by
  have hf : ascentFactors si c 0 = c := by
    funext i; simp only [ascentFactors]; rw [if_neg (by omega : ¬ i.val < 0)]
  have himp : ascentImp s imp 0 = imp := by
    simp only [ascentImp]; rw [if_neg (by omega : ¬ n < 0)]
  unfold ascentPath; rw [hf, himp]

theorem ascentPath_isAssemblageN [∀ i, Inhabited (X i)] (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) :
    isAssemblageN (ascentPath s si c imp k) :=
  (nary_form_iff _).mp ⟨ascentFactors si c k, ascentImp s imp k, rfl⟩

/-- **The ascent ascends.** Each step totalizes one region. -/
theorem ascentPath_ascends (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) :
    cLE (ascentPath s si c imp k) (ascentPath s si c imp (k + 1)) := by
  unfold ascentPath
  apply nary_mono
  · intro i; simp only [ascentFactors]
    by_cases h1 : i.val < k
    · rw [if_pos h1, if_pos (show i.val < k + 1 by omega)]; exact cLE_refl _
    · by_cases h2 : i.val < k + 1
      · rw [if_neg h1, if_pos h2]; exact c_le_totalization _ _
      · rw [if_neg h1, if_neg h2]; exact cLE_refl _
  · simp only [ascentImp]
    by_cases h1 : n < k
    · rw [if_pos h1, if_pos (show n < k + 1 by omega)]; exact cLE_refl _
    · by_cases h2 : n < k + 1
      · rw [if_neg h1, if_pos h2]; exact c_le_totalization _ _
      · rw [if_neg h1, if_neg h2]; exact cLE_refl _

/-- **The ascent reaches one scale-forced ceiling**, not an arbitrary maximum: the endpoint is
`nary (totalizations) (totalized import)`, fully determined by the scales. -/
theorem ascentPath_reaches_ceiling (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    ascentPath s si c imp (n + 1)
      = nary (fun i => totalization (si i) (c i)) (totalization s imp) := by
  have hf : ascentFactors si c (n + 1) = fun i => totalization (si i) (c i) := by
    funext i; simp only [ascentFactors]; rw [if_pos (Nat.lt_succ_of_lt i.isLt)]
  have himp : ascentImp s imp (n + 1) = totalization s imp := by
    simp only [ascentImp]; rw [if_pos (Nat.lt_succ_self n)]
  unfold ascentPath; rw [hf, himp]

/-- The ascent endpoint is a maximal element (total). -/
theorem ascentPath_ceiling_isTotal (s : (∀ i, X i) → Nat) (si : ∀ i, X i → Nat)
    (c : ∀ i, X i → X i → Option Bool) (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    isTotal (ascentPath s si c imp (n + 1)) := by
  rw [ascentPath_reaches_ceiling]
  exact nary_isTotal (fun i => totalization_isTotal (si i) (c i)) (totalization_isTotal s imp)

/-! ## The path quotient and its witnesses -/

/-- Emptying one factor: replace it by the absent classification. -/
def emptyFactor (i : Fin n) (c : ∀ i, X i → X i → Option Bool) : ∀ i, X i → X i → Option Bool :=
  Function.update c i (botC (X i))

omit [∀ i, DecidableEq (X i)] in
/-- **Emptying distinct factors commutes.** The generator of order-independence. -/
theorem emptyFactor_comm {i j : Fin n} (hij : i ≠ j) (c : ∀ i, X i → X i → Option Bool) :
    emptyFactor i (emptyFactor j c) = emptyFactor j (emptyFactor i c) := by
  simp only [emptyFactor]; rw [Function.update_comm hij.symm]

omit [∀ i, DecidableEq (X i)] in
/-- Emptying the same factor twice is emptying it once. -/
theorem emptyFactor_idem (i : Fin n) (c : ∀ i, X i → X i → Option Bool) :
    emptyFactor i (emptyFactor i c) = emptyFactor i c := by
  simp only [emptyFactor, Function.update_idem]

/-- The set-indexed intermediate: emptied factors given by a `Finset`, import by a `Bool`. -/
noncomputable def descentBySet (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (F : Finset (Fin n)) (e : Bool) :
    (∀ i, X i) → (∀ i, X i) → Option Bool :=
  nary (fun i => if i ∈ F then botC (X i) else c i) (if e then botC (∀ i, X i) else imp)

/-- **The ordered descent factors through the set-indexed intermediate.** The family of descent paths is the set
of maximal chains in the Boolean lattice `Finset (Fin n) × Bool`; the quotient (identify intermediates by
emptied-set) is that lattice: two orderings share an intermediate exactly when they have emptied the same set. -/
theorem descentPath_eq_bySet (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (k : Nat) :
    descentPath c imp k
      = descentBySet c imp (Finset.univ.filter (fun i => i.val < k)) (decide (n < k)) := by
  unfold descentPath descentBySet
  congr 1
  · funext i; simp only [descentFactors, Finset.mem_filter, Finset.mem_univ, true_and]
  · simp only [descentImp]; by_cases h : n < k <;> simp [h]

/-- **Order dependence at the n-ary** (witness). Emptying factor 0 first differs from emptying factor 1 first:
the two single-region steps give different intermediates. So the path is a family, not a canonical trajectory. -/
theorem descent_path_is_a_family_nary :
    ∃ (c : ∀ _ : Fin 2, Fin 2 → Fin 2 → Option Bool)
      (imp : (∀ _ : Fin 2, Fin 2) → (∀ _ : Fin 2, Fin 2) → Option Bool)
      (a b : ∀ _ : Fin 2, Fin 2),
      nary (emptyFactor 0 c) imp a b ≠ nary (emptyFactor 1 c) imp a b := by
  refine ⟨fun _ => fun _ _ => some true, fun _ _ => none, ![0, 0], ![1, 0], ?_⟩
  have hd : differsInOne (![0, 0] : ∀ _ : Fin 2, Fin 2) ![1, 0] 0 := by decide
  rw [nary_apply_differ _ _ hd, nary_apply_differ _ _ hd]
  decide

/-- **Distinct ascent ceilings are incomparable.** The only hypothesis is that the endpoints differ: both are
total (hence maximal), so distinctness forces incomparability. -/
theorem ascent_ceilings_incomparable
    (s s' : (∀ i, X i) → Nat) (si si' : ∀ i, X i → Nat)
    (c c' : ∀ i, X i → X i → Option Bool) (imp imp' : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (hne : ascentPath s si c imp (n + 1) ≠ ascentPath s' si' c' imp' (n + 1)) :
    ¬ cLE (ascentPath s si c imp (n + 1)) (ascentPath s' si' c' imp' (n + 1))
      ∧ ¬ cLE (ascentPath s' si' c' imp' (n + 1)) (ascentPath s si c imp (n + 1)) :=
  distinct_maxima_incomparable _ _ (ascentPath_ceiling_isTotal s si c imp)
    (ascentPath_ceiling_isTotal s' si' c' imp') hne

/-! ## The regions and the cross, and the assembly's symmetries

The cells of a product carrier fall into the `n` regions, where a pair differs in exactly one coordinate, and
the cross, where it differs in more or in none. The factors read the regions and the import reads the cross.
What follows is the structure of that split: the order the import carries, the symmetries an assembly can have,
and the sense in which an assembly is a limit of its pieces. -/

abbrev Pt (X : Fin n → Type) := ∀ k, X k

/-- A cross cell: a pair no factor reads. Stated as an `abbrev` so instance search unfolds it. -/
abbrev IsCross (a b : ∀ i, X i) : Prop := ¬ ∃ i, differsInOne a b i

omit [∀ i, DecidableEq (X i)] in
theorem diagAt (a : ∀ i, X i) : IsCross a a := by
  rintro ⟨i, hne, _⟩; exact hne rfl


/-! ### What presence forces at a coordinate -/
/-- **Presence forces agreement at the absent coordinate.** Over the empty import, if the factor at `i`
abstains off its diagonal, then wherever the composite holds a verdict the two points agree at `i`: the only
cells it holds are its own region-`i` cells at equal coordinate values, and there are none, plus the other
regions where agreement at `i` is forced by differ-in-one. -/
theorem present_forces_coord_eq (c : ∀ i, X i → X i → Option Bool) (i : Fin n)
    (habs : ∀ x y, x ≠ y → c i x y = none) (a b : ∀ k, X k)
    (h : nary c (botC (∀ k, X k)) a b ≠ none) : a i = b i := by
  by_contra hne
  by_cases hex : ∃ j, differsInOne a b j
  · obtain ⟨j, hj⟩ := hex
    have hji : j = i := by
      by_contra hji
      exact hne (hj.2 i (fun hc => hji hc.symm))
    subst hji
    rw [nary_apply_differ c _ hj] at h
    exact h (habs _ _ hne)
  · rw [nary_apply_imp c _ hex] at h
    exact h rfl

/-! ## The import carries the order

With the factors held fixed, the map from imports to assemblies transmits the classification order exactly and
commutes with the meet. The free region is therefore an ordered space in its own right, with a bottom that is
unique and maxima that are plural. -/
/-- **The order lifts, and lifts exactly.** With the factors held fixed, the composite of one import sits below
the composite of another EXACTLY when the imports are ordered on the cross region. The region cells contribute
nothing either way, since both composites read the same factors there. So `imp ↦ nary c imp` is an order
embedding of the cross-assignment order into the classification order. -/
theorem import_order_embeds (c : ∀ i, X i → X i → Option Bool)
    (imp imp' : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    cLE (nary c imp) (nary c imp') ↔ ∀ a b, IsCross a b → optLE (imp a b) (imp' a b) := by
  constructor
  · intro h a b hc
    have hcell := h a b
    rwa [nary_apply_imp c imp hc, nary_apply_imp c imp' hc] at hcell
  · intro h a b
    by_cases hex : ∃ i, differsInOne a b i
    · rw [nary_apply_differ c imp hex.choose_spec, nary_apply_differ c imp' hex.choose_spec]
      exact optLE_refl _
    · rw [nary_apply_imp c imp hex, nary_apply_imp c imp' hex]
      exact h a b hex

/-- **The composite construction commutes with meet.** The import space's meet is computed cellwise on the
cross region and transported unchanged; the region cells meet with themselves and survive. So the free region's
semilattice structure is exactly the composites' semilattice structure. -/
theorem nary_meet (c : ∀ i, X i → X i → Option Bool)
    (imp imp' : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    nary c (cMeet imp imp') = cMeet (nary c imp) (nary c imp') := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · rw [nary_apply_differ c (cMeet imp imp') hex.choose_spec]
    show _ = optMeet (nary c imp a b) (nary c imp' a b)
    rw [nary_apply_differ c imp hex.choose_spec, nary_apply_differ c imp' hex.choose_spec,
      optMeet_self]
  · rw [nary_apply_imp c (cMeet imp imp') hex]
    show cMeet imp imp' a b = optMeet (nary c imp a b) (nary c imp' a b)
    rw [nary_apply_imp c imp hex, nary_apply_imp c imp' hex]
    rfl

/-- The import order has a bottom: the empty import sits below every other. -/
theorem import_bottom (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    cLE (nary c (botC (∀ i, X i))) (nary c imp) :=
  (import_order_embeds c _ imp).2 (fun _ _ _ => Or.inl rfl)

/-- **FLAGGED: the one distinguished point.** The bottom is unique, so the framework DOES single out an import.
It singles out the one that supplies nothing: anything at or below the empty import is empty on the whole cross
region. This is the framework declining to choose, written order-theoretically, not a selection of content. It
is the only point any result in this file distinguishes, and it is reported here rather than buried. -/
theorem bottom_is_unique (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (h : cLE (nary c imp) (nary c (botC (∀ i, X i)))) :
    ∀ a b, IsCross a b → imp a b = none := by
  intro a b hc
  rcases (import_order_embeds c imp _).1 h a b hc with h1 | h1
  · exact h1
  · exact h1

/-- **And no distinguished maximum.** Two total imports give incomparable composites, so at the informative end
of the order there is no canonical point at all. The order singles out emptiness and refuses to single out
content. -/
theorem maxima_are_plural [∀ i, Inhabited (X i)] (c : ∀ i, X i → X i → Option Bool) :
    ¬ cLE (nary c cTrue) (nary c cFalse) ∧ ¬ cLE (nary c cFalse) (nary c cTrue) := by
  have hd : IsCross (fun i => (default : X i)) (fun i => (default : X i)) := diagAt _
  constructor
  · intro h
    rcases (import_order_embeds c cTrue cFalse).1 h _ _ hd with h1 | h1
    · exact absurd h1 (by simp [cTrue])
    · exact absurd h1 (by simp [cTrue, cFalse])
  · intro h
    rcases (import_order_embeds c cFalse cTrue).1 h _ _ hd with h1 | h1
    · exact absurd h1 (by simp [cFalse])
    · exact absurd h1 (by simp [cTrue, cFalse])

/-! ### The fill on a composite is not a factor operation -/
/-- **The composite fill DOES write the cross region.** Filling the whole assemblage by one scale supplies a
verdict at every cross cell, the import's own value where it had one and the scale's verdict where it did
not. -/
theorem composite_fill_writes_cross (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (s : (∀ i, X i) → Nat)
    {a b : ∀ i, X i} (h : IsCross a b) :
    totalization s (nary c imp) a b = some ((imp a b).getD (decide (s b ≤ s a))) := by
  simp only [totalization, nary_apply_imp c imp h]

/-- Sharply: where the import abstained, the composite fill writes a verdict the import never carried. -/
theorem composite_fill_overwrites_absent_cross (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (s : (∀ i, X i) → Nat)
    {a b : ∀ i, X i} (h : IsCross a b) (habs : imp a b = none) :
    totalization s (nary c imp) a b = some (decide (s b ≤ s a)) := by
  rw [composite_fill_writes_cross c imp s h, habs, Option.getD_none]

/-- **So the two are genuinely different operations.** If the import abstains anywhere on the cross region, the
composite fill is not equal to ANY assemblage over that same import, whatever factors are used. A composite fill
cannot be presented as a factor operation. -/
theorem composite_fill_not_a_factor_operation (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (s : (∀ i, X i) → Nat)
    {a b : ∀ i, X i} (hcross : IsCross a b) (habs : imp a b = none)
    (c' : ∀ i, X i → X i → Option Bool) :
    totalization s (nary c imp) ≠ nary c' imp := by
  intro h
  have hc := congrFun (congrFun h a) b
  rw [composite_fill_overwrites_absent_cross c imp s hcross habs,
    nary_apply_imp c' imp hcross, habs] at hc
  exact absurd hc (Option.some_ne_none _)

/-! ## The fibre-preserving symmetries

A map built coordinatewise fixes an assembly exactly when it fixes each factor off that factor's own diagonal
and fixes the import on the cross. The two clauses have different shapes, and that difference is the whole
content: the factor conditions are per-coordinate and local, the import condition is global. -/
/-- A FIBRE-PRESERVING map: one built coordinatewise, acting inside each coordinate and mixing none. -/
def Fib (π : ∀ k, X k → X k) (a : Pt X) : Pt X := fun k => π k (a k)

omit [∀ i, DecidableEq (X i)] in
theorem Fib_apply (π : ∀ k, X k → X k) (a : Pt X) (k : Fin n) : Fib π a k = π k (a k) := rfl

omit [∀ i, DecidableEq (X i)] in
/-- **A fibre-preserving injection preserves each region setwise**, in both directions. -/
theorem Fib_differsInOne (π : ∀ k, X k → X k) (hinj : ∀ k, Function.Injective (π k))
    (a b : Pt X) (k : Fin n) :
    differsInOne (Fib π a) (Fib π b) k ↔ differsInOne a b k := by
  constructor
  · rintro ⟨hne, hoth⟩
    refine ⟨fun hc => hne (by rw [Fib_apply, Fib_apply, hc]), fun j hj => ?_⟩
    exact hinj j (hoth j hj)
  · rintro ⟨hne, hoth⟩
    refine ⟨fun hc => hne (hinj k hc), fun j hj => ?_⟩
    rw [Fib_apply, Fib_apply, hoth j hj]

omit [∀ i, DecidableEq (X i)] in
/-- And it preserves the cross region setwise. -/
theorem Fib_cross (π : ∀ k, X k → X k) (hinj : ∀ k, Function.Injective (π k)) (a b : Pt X) :
    IsCross (Fib π a) (Fib π b) ↔ IsCross a b := by
  constructor
  · rintro h ⟨k, hk⟩
    exact h ⟨k, (Fib_differsInOne π hinj a b k).mpr hk⟩
  · rintro h ⟨k, hk⟩
    exact h ⟨k, (Fib_differsInOne π hinj a b k).mp hk⟩

/-- **THE LAW.** A fibre-preserving injection fixes an assembly exactly when it fixes each FACTOR off that
factor's own diagonal, and fixes the IMPORT on the cross region. The two clauses are of different shapes: the
factor clause is a conjunction of per-coordinate conditions, each mentioning one factor and one coordinate map;
the import clause is a single global condition on the whole tuple. -/
theorem fib_fixes_iff [∀ k, Inhabited (X k)] (π : ∀ k, X k → X k)
    (hinj : ∀ k, Function.Injective (π k)) (c : ∀ k, X k → X k → Option Bool)
    (imp : Pt X → Pt X → Option Bool) :
    relabel (Fib π) (nary c imp) = nary c imp
      ↔ ((∀ (k : Fin n) (x y : X k), x ≠ y → c k (π k x) (π k y) = c k x y)
          ∧ (∀ a b : Pt X, IsCross a b → imp (Fib π a) (Fib π b) = imp a b)) := by
  constructor
  · intro h
    constructor
    · intro k x y hxy
      set a : Pt X := Function.update (fun j => (default : X j)) k x with ha
      set b : Pt X := Function.update (fun j => (default : X j)) k y with hb
      have hd : differsInOne a b k := by
        refine ⟨?_, fun j hj => ?_⟩
        · rw [ha, hb]; simp only [Function.update_self]; exact hxy
        · rw [ha, hb]; simp only [Function.update_of_ne hj]
      have hd' : differsInOne (Fib π a) (Fib π b) k := (Fib_differsInOne π hinj a b k).mpr hd
      have hcell : nary c imp (Fib π a) (Fib π b) = nary c imp a b := congrFun (congrFun h a) b
      rw [nary_apply_differ c imp hd', nary_apply_differ c imp hd] at hcell
      have hax : a k = x := by rw [ha]; simp
      have hbk : b k = y := by rw [hb]; simp
      rw [Fib_apply, Fib_apply, hax, hbk] at hcell
      exact hcell
    · intro a b hcr
      have hcell : nary c imp (Fib π a) (Fib π b) = nary c imp a b := congrFun (congrFun h a) b
      rw [nary_apply_imp c imp ((Fib_cross π hinj a b).mpr hcr), nary_apply_imp c imp hcr] at hcell
      exact hcell
  · rintro ⟨hc, himp⟩
    funext a b
    show nary c imp (Fib π a) (Fib π b) = nary c imp a b
    by_cases hex : ∃ k, differsInOne a b k
    · obtain ⟨k, hk⟩ := hex
      have hk' : differsInOne (Fib π a) (Fib π b) k := (Fib_differsInOne π hinj a b k).mpr hk
      rw [nary_apply_differ c imp hk', nary_apply_differ c imp hk, Fib_apply, Fib_apply]
      exact hc k (a k) (b k) hk.1
    · rw [nary_apply_imp c imp ((Fib_cross π hinj a b).mpr hex), nary_apply_imp c imp hex]
      exact himp a b hex

omit [∀ i, DecidableEq (X i)] in
/-- **The factor clause is coordinatewise: no factor constrains any other coordinate's map.** Replacing every
factor except the one at `k` leaves the condition at `k` untouched. -/
theorem factor_condition_is_local (c c' : ∀ k, X k → X k → Option Bool) (π : ∀ k, X k → X k)
    (k : Fin n) (h : c k = c' k) :
    (∀ x y : X k, x ≠ y → c k (π k x) (π k y) = c k x y)
      ↔ (∀ x y : X k, x ≠ y → c' k (π k x) (π k y) = c' k x y) := by rw [h]

/-- **When nothing constrains, every fibre-preserving injection is an automorphism.** If each factor is
off-diagonally invariant under every coordinate injection and the import is invariant under every
fibre-preserving injection, the fibre-preserving automorphism group is the FULL product of the coordinate
symmetry groups. On a finite carrier its order is the product of the factorials of the fibre sizes: the general
LAW behind the measured count, which is a product of per-coordinate symmetries and not a fixed number. -/
theorem full_product_when_unconstrained [∀ k, Inhabited (X k)]
    (c : ∀ k, X k → X k → Option Bool) (imp : Pt X → Pt X → Option Bool)
    (hc : ∀ (k : Fin n) (ρ : X k → X k), Function.Injective ρ →
      ∀ x y : X k, x ≠ y → c k (ρ x) (ρ y) = c k x y)
    (himp : ∀ ρ : ∀ k, X k → X k, (∀ k, Function.Injective (ρ k)) →
      ∀ a b : Pt X, IsCross a b → imp (Fib ρ a) (Fib ρ b) = imp a b)
    (π : ∀ k, X k → X k) (hinj : ∀ k, Function.Injective (π k)) :
    relabel (Fib π) (nary c imp) = nary c imp :=
  (fib_fixes_iff π hinj c imp).mpr
    ⟨fun k x y hxy => hc k (π k) (hinj k) x y hxy, himp π hinj⟩

/-! ### The region blow-up, and what it does not force -/
/-- The coordinate a region cell reads. -/
def coordCell (i : Fin n) (p : Pt X × Pt X) : X i × X i := (p.1 i, p.2 i)

/-- **THE BLOW-UP.** On region `i`, the verdict factors through the coordinate-`i` pair: two region-`i` cells
with the same coordinate pair carry the same verdict, however the other coordinates differ. So the region-`i`
block of the verdict-partition is the PULLBACK of the factor's own off-diagonal partition along `coordCell i`,
each factor cell blown up across the other coordinates' fibres. -/
theorem region_verdict_factors_through_coord (c : ∀ i, X i → X i → Option Bool)
    (imp : Pt X → Pt X → Option Bool) (i : Fin n) (p q : Pt X × Pt X)
    (hp : differsInOne p.1 p.2 i) (hq : differsInOne q.1 q.2 i)
    (h : coordCell i p = coordCell i q) :
    nary c imp p.1 p.2 = nary c imp q.1 q.2 := by
  have h1 : p.1 i = q.1 i := congrArg Prod.fst h
  have h2 : p.2 i = q.2 i := congrArg Prod.snd h
  exact nary_region_independent c imp hp hq h1 h2

/-- **A rigid factor pins its own coordinate, whatever the blow-up.** If every factor admits only the identity
off its diagonal, the only fibre-preserving automorphism is the identity, at any carrier and any fibre sizes.
The region blow-up makes each factor cell repeat across the other coordinates' fibres, but the automorphism
condition reads the factor's own partition, which the repetition leaves untouched. -/
theorem rigid_factors_force_identity [∀ k, Inhabited (X k)] (π : ∀ k, X k → X k)
    (hinj : ∀ k, Function.Injective (π k)) (c : ∀ k, X k → X k → Option Bool)
    (imp : Pt X → Pt X → Option Bool)
    (hrigid : ∀ (k : Fin n) (ρ : X k → X k), (∀ x y : X k, x ≠ y → c k (ρ x) (ρ y) = c k x y) → ρ = id)
    (h : relabel (Fib π) (nary c imp) = nary c imp) : Fib π = id := by
  have hfac := ((fib_fixes_iff π hinj c imp).1 h).1
  have hid : ∀ k, π k = id := fun k => hrigid k (π k) (fun x y hxy => hfac k x y hxy)
  funext a
  funext k
  show π k (a k) = a k
  rw [hid k]
  rfl

/-! ## The assembly as a limit of its pieces

Each piece is the assembly opened by a mask written in `differsInOne`, so a piece is a value of the down-move
and a projection is a mask arrow by definition. Over a total source the mask arrows out of it are determined,
and the assembly is then a genuine limit of its pieces. In the full setting it is a jointly monic cone that is
not a limit, obstructed in two independent ways. -/
/-- Fires everywhere EXCEPT region `i`. -/
def regionMask (i : Fin n) : (∀ i, X i) → (∀ i, X i) → Bool := fun a b => decide (¬ differsInOne a b i)

/-- Fires everywhere EXCEPT the cross. -/
def crossMask : (∀ i, X i) → (∀ i, X i) → Bool := fun a b => decide (∃ i, differsInOne a b i)

/-- Fires exactly where the classification abstains. -/
def absenceMask (A : (∀ i, X i) → (∀ i, X i) → Option Bool) : (∀ i, X i) → (∀ i, X i) → Bool :=
  fun a b => decide (A a b = none)

/-- The region-`i` piece: the classification opened everywhere but region `i`. -/
def regionSlice (i : Fin n) (A : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    (∀ i, X i) → (∀ i, X i) → Option Bool := partialization (regionMask i) A

/-- The cross piece: the classification opened everywhere but the cross. -/
def crossSlice (A : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    (∀ i, X i) → (∀ i, X i) → Option Bool := partialization crossMask A

/-- **THE EQUIVALENCE, region half.** This is verbatim the defining equation of the archived `regionPiece`, so
the canonical slice IS the same object and the finding is preserved rather than changed. -/
theorem regionSlice_apply (i : Fin n) (A : (∀ i, X i) → (∀ i, X i) → Option Bool) (a b : ∀ i, X i) :
    regionSlice i A a b = if differsInOne a b i then A a b else none := by
  by_cases h : differsInOne a b i
  · have hm : regionMask i a b = false := decide_eq_false (fun hn => hn h)
    simp only [regionSlice, partialization, hm, Bool.false_eq_true, if_false]
    rw [if_pos h]
  · have hm : regionMask i a b = true := decide_eq_true h
    simp only [regionSlice, partialization, hm, if_true]
    rw [if_neg h]

/-- **THE EQUIVALENCE, cross half.** Verbatim the defining equation of the archived `crossPiece`. -/
theorem crossSlice_apply (A : (∀ i, X i) → (∀ i, X i) → Option Bool) (a b : ∀ i, X i) :
    crossSlice A a b = if (¬ ∃ i, differsInOne a b i) then A a b else none := by
  by_cases h : ∃ i, differsInOne a b i
  · have hm : crossMask a b = true := decide_eq_true h
    simp only [crossSlice, partialization, hm, if_true]
    rw [if_neg (not_not_intro h)]
  · have hm : crossMask a b = false := decide_eq_false h
    simp only [crossSlice, partialization, hm, Bool.false_eq_true, if_false]
    rw [if_pos h]

/-- **Taking a piece twice is taking it once.** The region slice is idempotent, so the piece
decomposition has no depth of its own: a piece of a piece at the same region is that piece. -/
theorem regionSlice_idempotent (i : Fin n) (A : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    regionSlice i (regionSlice i A) = regionSlice i A := by
  funext a b
  rw [regionSlice_apply, regionSlice_apply]
  by_cases h : differsInOne a b i
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- **And two distinct regions share no cell, so their pieces annihilate.** A pair differs in at most one
coordinate, so slicing at one region and then at another leaves nothing standing anywhere. The regions
partition what they touch and the decomposition is flat rather than nested. -/
theorem regionSlice_of_distinct_regions {i j : Fin n} (hij : i ≠ j)
    (A : (∀ i, X i) → (∀ i, X i) → Option Bool) :
    regionSlice j (regionSlice i A) = botC (∀ i, X i) := by
  funext a b
  rw [regionSlice_apply, regionSlice_apply]
  by_cases hj : differsInOne a b j
  · rw [if_pos hj, if_neg (fun hi => hij (differsInOne_unique hi hj))]; rfl
  · rw [if_neg hj]; rfl

/-- **And the pieces read the canonical assembly structure.** The region piece is the factor, by
`nary_apply_differ`. This is content the archived version did not have: there the pieces were about an
arbitrary classification. -/
theorem regionSlice_reads_factor (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) (i : Fin n) {a b : ∀ i, X i}
    (h : differsInOne a b i) : regionSlice i (nary c imp) a b = c i (a i) (b i) := by
  rw [regionSlice_apply, if_pos h, nary_apply_differ c imp h]

/-- The cross piece is the import, by `nary_apply_imp`. -/
theorem crossSlice_reads_import (c : ∀ i, X i → X i → Option Bool)
    (imp : (∀ i, X i) → (∀ i, X i) → Option Bool) {a b : ∀ i, X i}
    (h : ¬ ∃ i, differsInOne a b i) : crossSlice (nary c imp) a b = imp a b := by
  rw [crossSlice_apply, if_pos h, nary_apply_imp c imp h]

omit [∀ i, DecidableEq (X i)] in
/-- A mask-only leg out of a TOTAL source is completely determined: it fires exactly where the target
abstains. This is what removes the laziness obstruction inside the subcategory. -/
theorem leg_of_total (T Tgt : (∀ i, X i) → (∀ i, X i) → Option Bool) (hT : ∀ a b, T a b ≠ none)
    (v : (∀ i, X i) → (∀ i, X i) → Bool) (h : partialization v T = Tgt) (a b : ∀ i, X i) :
    (v a b = true ↔ Tgt a b = none) ∧ (v a b = false → T a b = Tgt a b) := by
  have hc : (if v a b then none else T a b) = Tgt a b := congrFun (congrFun h a) b
  cases hv : v a b
  · rw [hv] at hc
    simp only [Bool.false_eq_true, if_false] at hc
    refine ⟨⟨fun hx => absurd hx (by simp), fun hx => absurd (hc.trans hx) (hT a b)⟩, fun _ => hc⟩
  · rw [hv] at hc
    simp only [if_true] at hc
    exact ⟨⟨fun _ => hc.symm, fun _ => rfl⟩, fun hx => absurd hx (by simp)⟩

/-- **EXISTENCE, in the mask subcategory over a total source, on canonical pieces.** The absence mask of the
assembly mediates: it reproduces the assembly from the source and factors every leg. -/
theorem mediator_exists (A T : (∀ i, X i) → (∀ i, X i) → Option Bool) (hT : ∀ a b, T a b ≠ none)
    (vR : Fin n → (∀ i, X i) → (∀ i, X i) → Bool) (vC : (∀ i, X i) → (∀ i, X i) → Bool)
    (hR : ∀ i, partialization (vR i) T = regionSlice i A)
    (hC : partialization vC T = crossSlice A) :
    partialization (absenceMask A) T = A
      ∧ (∀ i, (fun a b => regionMask i a b || absenceMask A a b) = vR i)
      ∧ (fun a b => crossMask a b || absenceMask A a b) = vC := by
  have key : ∀ a b : ∀ i, X i, (A a b ≠ none → T a b = A a b) := by
    intro a b hpres
    by_cases hex : ∃ i, differsInOne a b i
    · obtain ⟨i, hi⟩ := hex
      have hL := leg_of_total T (regionSlice i A) hT (vR i) (hR i) a b
      have h2 : regionSlice i A a b = A a b := by rw [regionSlice_apply, if_pos hi]
      have hv : vR i a b = false := by
        cases hvv : vR i a b
        · rfl
        · exact absurd (h2.symm.trans (hL.1.mp hvv)) hpres
      exact (hL.2 hv).trans h2
    · have hL := leg_of_total T (crossSlice A) hT vC hC a b
      have h2 : crossSlice A a b = A a b := by rw [crossSlice_apply, if_pos hex]
      have hv : vC a b = false := by
        cases hvv : vC a b
        · rfl
        · exact absurd (h2.symm.trans (hL.1.mp hvv)) hpres
      exact (hL.2 hv).trans h2
  refine ⟨?_, ?_, ?_⟩
  · funext a b
    show (if absenceMask A a b then none else T a b) = A a b
    by_cases hp : A a b = none
    · rw [show absenceMask A a b = true from decide_eq_true hp]
      simp [hp]
    · rw [show absenceMask A a b = false from decide_eq_false hp]
      simpa using key a b hp
  · intro i
    funext a b
    have hL := leg_of_total T (regionSlice i A) hT (vR i) (hR i) a b
    by_cases hi : differsInOne a b i
    · rw [show regionMask i a b = false from decide_eq_false (fun hn => hn hi)]
      simp only [Bool.false_or]
      have h2 : regionSlice i A a b = A a b := by rw [regionSlice_apply, if_pos hi]
      cases hv : vR i a b
      · refine decide_eq_false (fun hp => ?_)
        exact absurd (hL.1.mpr (h2.trans hp)) (by simp [hv])
      · exact decide_eq_true (h2.symm.trans (hL.1.mp hv))
    · rw [show regionMask i a b = true from decide_eq_true hi, Bool.true_or]
      exact (hL.1.mpr (show regionSlice i A a b = none by rw [regionSlice_apply, if_neg hi])).symm
  · funext a b
    have hL := leg_of_total T (crossSlice A) hT vC hC a b
    by_cases hex : ∃ i, differsInOne a b i
    · rw [show crossMask a b = true from decide_eq_true hex, Bool.true_or]
      exact (hL.1.mpr (show crossSlice A a b = none by
        rw [crossSlice_apply, if_neg (not_not_intro hex)])).symm
    · rw [show crossMask a b = false from decide_eq_false hex]
      simp only [Bool.false_or]
      have h2 : crossSlice A a b = A a b := by rw [crossSlice_apply, if_pos hex]
      cases hv : vC a b
      · refine decide_eq_false (fun hp => ?_)
        exact absurd (hL.1.mpr (h2.trans hp)) (by simp [hv])
      · exact decide_eq_true (h2.symm.trans (hL.1.mp hv))

/-- **UNIQUENESS, and it needs no totality.** The projection masks are false exactly on their own parts, and
the parts exhaust the cells, so the cone is jointly monic. -/
theorem mediator_unique (w w' : (∀ i, X i) → (∀ i, X i) → Bool)
    (hR : ∀ i, (fun a b => regionMask i a b || w a b) = (fun a b => regionMask i a b || w' a b))
    (hC : (fun a b => crossMask a b || w a b) = (fun a b => crossMask a b || w' a b)) : w = w' := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · obtain ⟨i, hi⟩ := hex
    have hw : regionMask i a b = false := decide_eq_false (fun hn => hn hi)
    have h := congrFun (congrFun (hR i) a) b
    rwa [hw, Bool.false_or, Bool.false_or] at h
  · have hw : crossMask a b = false := decide_eq_false hex
    have h := congrFun (congrFun hC a) b
    rwa [hw, Bool.false_or, Bool.false_or] at h

/-- **Obstruction A, laziness.** If the assembly abstains at a cell outside region `i`, a mask-only leg may
decline to fire there and no mediator can match it: the projection fires there and every composite through it
inherits that. Carrier-general, uniform in `n`, and it uses identity relabellings only, so restricting the cone
to a shared relabelling does not remove it. -/
theorem lazy_leg_no_mediator [DecidableEq (∀ i, X i)]
    (A : (∀ i, X i) → (∀ i, X i) → Option Bool) (i : Fin n) (a b : ∀ i, X i)
    (hnr : ¬ differsInOne a b i) (habs : A a b = none) :
    partialization (fun p q => regionMask i p q && !(decide (p = a ∧ q = b))) A = regionSlice i A
      ∧ ¬ ∃ w : (∀ i, X i) → (∀ i, X i) → Bool,
          (fun p q => regionMask i p q || w p q)
            = (fun p q => regionMask i p q && !(decide (p = a ∧ q = b))) := by
  constructor
  · funext p q
    rw [regionSlice_apply]
    show (if (regionMask i p q && !(decide (p = a ∧ q = b))) then none else A p q)
      = (if differsInOne p q i then A p q else none)
    by_cases hpq : p = a ∧ q = b
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [show (decide (p = p ∧ q = q)) = true from decide_eq_true ⟨rfl, rfl⟩]
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
      rw [if_neg hnr]
      exact habs
    · rw [show (decide (p = a ∧ q = b)) = false from decide_eq_false hpq]
      simp only [Bool.not_false, Bool.and_true]
      by_cases hi : differsInOne p q i
      · rw [if_pos hi, show regionMask i p q = false from decide_eq_false (fun hn => hn hi)]
        simp
      · rw [if_neg hi, show regionMask i p q = true from decide_eq_true hi]
        simp
  · rintro ⟨w, hw⟩
    have hc := congrFun (congrFun hw a) b
    rw [show regionMask i a b = true from decide_eq_true hnr,
      show (decide (a = a ∧ b = b)) = true from decide_eq_true ⟨rfl, rfl⟩] at hc
    simp at hc

/-- **Obstruction B, symmetry.** A non-identity relabelling fixing the assembly gives a second, equally valid
leg to the region-`i` piece with a different relabelling component. The projections have identity relabelling
components, so a mediator's relabelling component would have to be the composite's, that is `id` for one leg
and the automorphism for the other. Those are different, so no mediator exists. Carrier-general and uniform in
`i`; the automorphism need not permute the pieces, fixing the assembly is enough. -/
theorem automorphism_breaks_existence (A : (∀ i, X i) → (∀ i, X i) → Option Bool)
    (σ : (∀ i, X i) → (∀ i, X i)) (i : Fin n) (hσ : relabel σ A = A) (hne : σ ≠ id) :
    partialization (regionMask i) (relabel σ A) = regionSlice i A
      ∧ ¬ ∃ u : (∀ i, X i) → (∀ i, X i), u = id ∧ u = σ := by
  refine ⟨by rw [hσ]; rfl, ?_⟩
  rintro ⟨u, h1, h2⟩
  exact hne (h1.symm.trans h2).symm

/-! ## THE VERDICTS

PART 1: the pieces are canonical, and they are BETTER than the archived ones.

`regionMask` and `crossMask` are written in canonical `differsInOne` and nothing else. `regionSlice` and
`crossSlice` are not new constructions at all: each is `partialization` applied to the assembly, so a piece is a
value of the canonical DOWN-MOVE and a projection is a mask arrow by definition, not by a lemma.

`regionSlice_apply` and `crossSlice_apply` prove the defining equations of the archived `regionPiece` and
`crossPiece` verbatim, so the canonical pieces are THE SAME OBJECTS and the finding is preserved, not changed.
The projections coincide too, definitionally, since the archived projections were already partializations by
`wRegion` and `wCross` and those masks are pointwise equal to `regionMask` and `crossMask`.

One thing is gained rather than merely preserved. `regionSlice_reads_factor` and `crossSlice_reads_import`
identify the pieces with the FACTORS and the IMPORT through canonical `nary_apply_differ` and `nary_apply_imp`.
The archived version could not say this: its pieces were slices of an arbitrary classification, which is exactly
what made it partition-generic. Stated canonically, the diagram is about assemblies.

PART 2: the limit stands, with no archived dependency.

`leg_of_total`, `mediator_exists` and `mediator_unique` are re-proved on the canonical slices. Nothing from
the archived apparatus appears: no `regionPiece`, no `crossPiece`, no `wRegion`, no `wCross`, no `absMask`, and
no `cell_cases`, whose role is taken by a `by_cases` on the canonical `∃ i, differsInOne a b i`, which is the
same case split canonical `nary` itself performs.

The finding is unchanged. In the mask subcategory over total sources the assembly is a genuine limit of its
pieces: the absence mask mediates and the cone is jointly monic. Uniqueness needs no totality.

PART 3: both obstructions stand canonically.

`lazy_leg_no_mediator` is obstruction A, carrier-general and uniform in `n`, on the canonical slice. It uses
identity relabellings only, so it is not removed by restricting the cone.

`automorphism_breaks_existence` is obstruction B, and re-expressing it canonically made it SHARPER than the
witness form it had. The archived route exhibited it on a two-point carrier through the arrow apparatus; here
it is stated for any carrier, any assembly, any coordinate, and any non-identity automorphism, and the
contradiction is that the mediator's relabelling component would have to be both the identity and the
automorphism. The arrow apparatus is not needed to see it, only the fact that the projections have identity
relabelling components.

So the full verdict survives on canonical foundations: existence fails in the full category by two independent
obstructions, uniqueness holds throughout, and existence is restored exactly in the mask subcategory over total
sources. That is the mono-cone finding as it stood.

WHAT REMAINS OPEN

1. Obstruction B is stated at the level of relabelling components, which is where the contradiction lives. A
   version phrased through the composed arrows would need the combined-category apparatus that the dry run
   graduates separately; it would add no content.
2. The pieces are shown to read the factors and the import. Whether the limit property itself can be stated
   over the FACTOR carriers rather than the product carrier, which is what a genuinely assembly-shaped diagram
   would be, is not attempted here.
3. Nothing graduates in this file. It readies a rebuild for the graduation pass. -/

/-! ## The full symmetry group of a classification

Dropping the fibre-preserving restriction, and dropping the assembly structure entirely: a carrier map fixes a
classification exactly when the induced cell map preserves every level set. The group is a fact about the
verdict-partition, and absence is not distinguished among the verdicts. -/

section FullGroup

variable {P : Type}

/-- The map a carrier permutation induces on CELLS. -/
def cellMap (σ : P → P) (p : P × P) : P × P := (σ p.1, σ p.2)

/-- The level sets of a classification: the cells carrying a given verdict. -/
def Level (A : P → P → Option Bool) (v : Option Bool) (p : P × P) : Prop := A p.1 p.2 = v

/-- **THE CHARACTERIZATION.** A carrier map fixes a classification exactly when the cell map it induces
preserves every level set. Carrier-general, no finiteness, and NO assemblage structure is used: the full
automorphism group is a fact about classifications, not about assemblies. -/
theorem fixes_iff_levels (σ : P → P) (A : P → P → Option Bool) :
    relabel σ A = A ↔ ∀ (v : Option Bool) (p : P × P), Level A v p → Level A v (cellMap σ p) := by
  constructor
  · intro h v p hp
    have hc : A (σ p.1) (σ p.2) = A p.1 p.2 := congrFun (congrFun h p.1) p.2
    exact hc.trans hp
  · intro h
    funext a b
    exact h (A a b) (a, b) rfl

/-- **NO.** Relabelling the VERDICTS by any injection leaves the automorphism group unchanged, because the
characterization reads only the level-set PARTITION and never which verdict labels which block. So a large
absence set generates exactly the symmetries a large present set of the same shape would. -/
theorem aut_invariant_under_value_relabel (g : Option Bool → Option Bool)
    (hg : Function.Injective g) (A : P → P → Option Bool) (σ : P → P) :
    relabel σ (fun a b => g (A a b)) = (fun a b => g (A a b)) ↔ relabel σ A = A := by
  constructor
  · intro h
    funext a b
    exact hg (congrFun (congrFun h a) b)
  · intro h
    funext a b
    exact congrArg g (congrFun (congrFun h a) b)

end FullGroup

/-! ### Witnesses on a two-by-two carrier

section Witnesses is on concrete carriers, so the product-carrier variables above are not in scope here. -/

section Witnesses

abbrev Q2 := ∀ _ : Fin 2, Fin 2

def mk2 (c0 c1 : Fin 2 → Fin 2 → Option Bool) (imp : Q2 → Q2 → Option Bool) : Q2 → Q2 → Option Bool :=
  fun a b =>
    if a 0 ≠ b 0 ∧ a 1 = b 1 then c0 (a 0) (b 0)
    else if a 1 ≠ b 1 ∧ a 0 = b 0 then c1 (a 1) (b 1)
    else imp a b

def wreath : Q2 → Q2 := fun a => fun i => if i = 0 then a 0 else (if a 0 = 0 then a 1 else a 1 + 1)

-- The level-set sizes and the automorphism counts, over all 256 carrier maps. Recorded output:
--   8   absent cells of `Agq`;  4  true cells;  4  false cells
--   4   absent cells of `AgqS`; 8  true cells;  4  false cells
--   8   automorphisms of `Agq`
--   8   automorphisms of `AgqS`
-- The large level set moved from absence to presence and the count did not change.

/-- **NO DECOMPOSITION: the mixing automorphisms are not a subgroup.** The mixing map squares to the identity,
which is fibre-preserving, so the non-fibre-preserving elements are not closed under composition. There is
therefore no complement to the fibre-preserving subgroup and no product or extension splitting the group into a
value part and an absence part. -/
theorem mixing_not_closed : wreath ∘ wreath = (id : Q2 → Q2) ∧ wreath ≠ (id : Q2 → Q2) := by
  refine ⟨by decide, ?_⟩
  intro h
  exact absurd (congrFun (congrFun h ![1, 0]) 1) (by decide)

/-! ## THE VERDICTS

PART 1: the full group is characterized by LEVEL SETS, carrier-general.

`fixes_iff_levels`: a carrier map fixes a classification exactly when the induced cell map preserves every
level set. No finiteness, no hypotheses, and NO ASSEMBLAGE STRUCTURE. That last point is itself a finding: the
mixing part is not an assemblage phenomenon at all. `fib_fixes_iff` was about assemblies because it read the
factors and the import separately; the full group reads only the partition of cells by verdict, and an assembly
is just one way of producing such a partition.

`aut_comp` and `aut_id` confirm the automorphisms form a group in the usual way.

PART 2: absence is NOT distinguished. The reading is denied.

`aut_invariant_under_value_relabel` is the theorem: relabelling the verdicts by ANY injection leaves the
automorphism group unchanged, because the characterization reads the level-set PARTITION and never which
verdict labels which block. So a large absence set generates exactly the symmetries a large present set of the
same shape would, and there is nothing special about `none`.

`constant_has_all_automorphisms` makes the same point at the extreme: the maximally symmetric classifications
are the constant ones, and the order bottom is not distinguished among them. `cTrue` and `cFalse` have the same
full symmetry as `botC`.

MEASURED, and it agrees. `AgqS` is the witness assembly with absence and the true verdict exchanged, still an
assembly by `nary_value_relabel` and `AgqS_is_an_assembly`. Its large level set is now presence, not absence:
the recorded counts move from eight absent and four true, to four absent and eight true. Its automorphism count
is UNCHANGED at eight, and `mixing_survives_the_value_swap` shows the same mixing map fixes it.

THE BOUNDARY QUESTION, answered and reframed. Mixing automorphisms DO identify a region cell with a cross cell:
`boundary_break_is_not_absence` shows the map carrying a region-0 pair to a cross pair. But it happens in BOTH
versions, at absence in one and at the true verdict in the other. So the mechanism is not that absence dissolves
the region-cross boundary. It is that the boundary is invisible to the object wherever the object fails to
SEPARATE the two sides by verdict. Absence is the commonest way that happens, not the reason it happens.

PART 3: no genuine decomposition. The split is a description, not group structure.

The fibre-preserving automorphisms form a subgroup (`Fib_closed` with `aut_comp`). The mixing ones do NOT:
`mixing_not_closed` shows the mixing map squares to the identity, which is fibre-preserving, so the
non-fibre-preserving elements are not closed under composition. A set that is not closed cannot be a subgroup,
so there is no complement, no semidirect product, and no extension splitting the group into two parts.

So the proposed reading fails twice over. The mixing part is not governed by absence (Part 2), and it is not a
group-theoretic part at all (Part 3). The only genuine structure is: the fibre-preserving automorphisms are a
subgroup of the full automorphism group, and the full group is cut out by the level-set partition. Calling the
one part "said" and the other "unsaid" would be a description laid over a subgroup and its complement, and the
complement is not an object.

WHAT REMAINS OPEN

1. Whether the fibre-preserving subgroup is NORMAL in the full automorphism group is not settled. On the
   four-point carrier used here it is, since the product maps there form the Klein four-group inside the
   symmetric group on four points, but that is a coincidence of two-by-two and no general claim is made.
2. `fixes_iff_levels` characterizes the group by the level-set partition. Which partitions of the cell set
   arise from assemblies, and how the assembly structure constrains them, is not measured; that is the question
   that would connect the full group back to `fib_fixes_iff`.
3. The counts are decide-bound observations on one carrier. The level-set characterization and the
   value-relabel invariance are the carrier-general theorems; the counts illustrate them and prove nothing on
   their own. -/

def gC : Fin 2 → Fin 2 → Option Bool := fun x y => if x = y then some true else none

def qC : Fin 2 → Fin 2 → Option Bool := fun x y => some (decide (x = y))

def impD : Q2 → Q2 → Option Bool := fun a b => if a = b then some true else none

def impPin : Q2 → Q2 → Option Bool :=
  fun a b => if a = b then (if a = ![0, 0] then some true else none)
             else if a = ![0, 1] ∧ b = ![1, 0] then some false else none

def Aopen : Q2 → Q2 → Option Bool := mk2 gC qC impD

def Apin : Q2 → Q2 → Option Bool := mk2 gC qC impPin

set_option maxRecDepth 100000 in
/-- **THE CROSS FREEDOM LEAVES THE FULL GROUP OPEN.** Two assemblies with the SAME factors, differing only in
the import, have different automorphism groups: one admits a non-identity map, the other admits none. So the
region constraint of Part 1 does not determine the full group, and knowing the factors is not enough. -/
theorem full_group_not_determined_by_factors :
    (wreath ≠ id ∧ ∀ a b : Q2, Aopen (wreath a) (wreath b) = Aopen a b)
      ∧ (∀ σ : Q2 → Q2, relabel σ Apin = Apin → σ = id) := by
  refine ⟨⟨?_, by decide⟩, by decide⟩
  intro h
  exact absurd (congrFun (congrFun h ![1, 0]) 1) (by decide)

/-! ## THE VERDICTS

PART 1: the constraint is the blow-up, and the characterization is ALREADY CANONICAL.

`region_verdict_factors_through_coord` is the structural fact: on region `i` the verdict factors through the
coordinate-`i` pair, so the region-`i` block of the verdict-partition is the PULLBACK of the factor's own
off-diagonal partition, each factor cell blown up across the other coordinates' fibres.
`every_factor_cell_is_realized` shows the pullback is onto, and `cross_is_free` shows the cross block is
unconstrained.

But the characterization of realizable partitions is canonical `nary_form_iff`, restated:
`realizable_iff` proves an assignment is assembly-realizable exactly when it is region-independent. So Part 1's
question had an answer in the framework already, and what this file adds is only the partition reading. The
class IS clean and checkable: given a verdict-assignment, test region-independence, which is a finite check per
region on a finite carrier.

PART 2: THE BLOW-UP FORCES NOTHING. The hypothesis is refuted.

The reasoning behind the hypothesis was that region cells sharing a coordinate pair must share a verdict, so
cells that must agree can be permuted. That is true at the level of CELLS and false at the level of CARRIER
MAPS, because a carrier map that exploits region `i`'s coarseness must move other coordinates, and those moves
are seen by the other factors' regions.

`fib_forces_factor_condition` makes the point visible: the condition a fibre-preserving map must satisfy
mentions one factor and one coordinate map, and the blow-up MULTIPLICITY does not appear in it at all. The
coarseness lives in the cell count; the automorphism condition reads the factor's own partition, which the
blow-up leaves untouched.

`rigid_factors_force_identity` is the theorem, carrier-general: if every factor is rigid off its diagonal, the
only fibre-preserving automorphism is the identity, at any carrier and any multiplicity. `lin_rigid` shows
rigid factors exist, and `blowup_forces_nothing` instantiates it on a carrier where every region cell is blown
up threefold and the group is trivial regardless.

So the stronger second proof that asymmetry lives only in the import is NOT available. The factors can supply
rigidity, which is `AssemblySymmetry`'s Correction 1 again, now seen from the partition side and with an
explicit rigid factor.

PART 3: the class is clean, the full group is NOT.

`full_group_not_determined_by_factors` settles it: two assemblies with the SAME factors, differing only in the
import, have different automorphism groups. One is fixed by a non-identity coordinate-mixing map; the other is
fixed by nothing but the identity, checked over all two hundred and fifty six carrier maps. Recorded counts
eight and one.

So the bridge exists but does not close the gap. Part 1 pins the REGION part of the partition exactly, and by
`fixes_iff_levels` the full group is the partition's stabilizer; but the CROSS part of the partition is free,
so the stabilizer ranges from the fibre-preserving part up to everything as the import varies. Knowing an
object is an assembly, and knowing its factors, does not determine its full automorphism group.

What the two theorems now share is precise. `fib_fixes_iff` characterizes the fibre-preserving part from the
factors and the import separately. `fixes_iff_levels` characterizes the full group from the partition. Part 1
says which partitions occur. The residual gap is exactly the cross block, which is free, and that is the same
free parameter every earlier build in this thread arrived at.

WHAT REMAINS OPEN

1. The region blocks are pullbacks; the cross block is free. Whether some coarse INVARIANT of the full group,
   short of the group itself, is determined by the factors alone is not measured.
2. `lin_rigid` is a three-point rigidity check by decision. Which classifications are rigid off their
   diagonals, carrier-generally, is not characterized; a linear order suffices but is not shown necessary.
3. `realizable_iff` is canonical restated. If any of this graduates, that theorem is not new content and the
   partition reading would be documentation on `nary_form_iff`, not a theorem beside it. -/

end Witnesses

/-! ## The import map, and the order structure it carries

With the factors held fixed, sending an import to the assembly it completes is a MAP from the import space to
the classification space. Read that way, the results above say it is an order embedding that preserves the
meet; what remains is the exact sense in which it is faithful, which is not injectivity on the nose. -/

/-- The import map: `nary c` read as a map in the import, with the factors fixed. -/
noncomputable def importMap (c : ∀ i, X i → X i → Option Bool) (imp : Pt X → Pt X → Option Bool) :
    Pt X → Pt X → Option Bool := nary c imp

/-- **The kernel of the import map, exactly.** Two imports have the same image precisely when they agree on the
cross region. So the map is NOT injective: imports differing only on the regions are overwritten by the factors,
and faithfulness means injectivity modulo cross-agreement. -/
theorem importMap_kernel (c : ∀ i, X i → X i → Option Bool) (imp imp' : Pt X → Pt X → Option Bool) :
    importMap c imp = importMap c imp' ↔ ∀ a b, IsCross a b → imp a b = imp' a b := by
  simp only [importMap]
  constructor
  · intro h a b hc
    have hcell := congrFun (congrFun h a) b
    rwa [nary_apply_imp c imp hc, nary_apply_imp c imp' hc] at hcell
  · intro h
    funext a b
    by_cases hex : ∃ i, differsInOne a b i
    · rw [nary_apply_differ c imp hex.choose_spec, nary_apply_differ c imp' hex.choose_spec]
    · rw [nary_apply_imp c imp hex, nary_apply_imp c imp' hex]
      exact h a b hex

/-- Imports supported on the cross region: the canonical representatives of the kernel classes. -/
def CrossSupported (imp : Pt X → Pt X → Option Bool) : Prop :=
  ∀ a b, ¬ IsCross a b → imp a b = none

/-- **Faithful, literally.** On cross-supported representatives the import map is injective, at any carrier. -/
theorem importMap_injective_on_crossSupported (c : ∀ i, X i → X i → Option Bool)
    (imp imp' : Pt X → Pt X → Option Bool) (h : CrossSupported imp) (h' : CrossSupported imp')
    (heq : importMap c imp = importMap c imp') : imp = imp' := by
  funext a b
  by_cases hc : IsCross a b
  · exact (importMap_kernel c imp imp').1 heq a b hc
  · rw [h a b hc, h' a b hc]

/-- **THE EMBEDDING, one statement.** The import map is a meet-embedding of the import order into the
classification order with its kernel identified: the order transmits both ways, meets are preserved on the
nose, two imports collide exactly when they agree on the cross, and on cross-supported representatives the map
is injective. Carrier-general: arbitrary `n`, arbitrary fibres, no finiteness and no inhabitation. -/
theorem importMap_is_a_meet_embedding (c : ∀ i, X i → X i → Option Bool) :
    (∀ imp imp' : Pt X → Pt X → Option Bool,
        cLE (importMap c imp) (importMap c imp') ↔ ∀ a b, IsCross a b → optLE (imp a b) (imp' a b))
      ∧ (∀ imp imp' : Pt X → Pt X → Option Bool,
        importMap c (cMeet imp imp') = cMeet (importMap c imp) (importMap c imp'))
      ∧ (∀ imp imp' : Pt X → Pt X → Option Bool,
        importMap c imp = importMap c imp' ↔ ∀ a b, IsCross a b → imp a b = imp' a b)
      ∧ (∀ imp imp' : Pt X → Pt X → Option Bool,
        CrossSupported imp → CrossSupported imp' → importMap c imp = importMap c imp' → imp = imp') :=
  ⟨import_order_embeds c, nary_meet c, importMap_kernel c, importMap_injective_on_crossSupported c⟩

/-- **The map singles out emptiness and refuses to single out content.** The empty import is the least element,
and there is NO greatest element at all: any candidate would have to agree with both the all-true and the
all-false import at a cross cell. So exactly one point is distinguished, and it is the one that supplies
nothing. -/
theorem importMap_singles_out_emptiness [∀ i, Inhabited (X i)]
    (c : ∀ i, X i → X i → Option Bool) :
    (∀ imp : Pt X → Pt X → Option Bool, cLE (importMap c (botC (Pt X))) (importMap c imp))
      ∧ ¬ ∃ t : Pt X → Pt X → Option Bool,
          ∀ imp : Pt X → Pt X → Option Bool, cLE (importMap c imp) (importMap c t) := by
  refine ⟨import_bottom c, ?_⟩
  rintro ⟨t, ht⟩
  have hd : IsCross (fun i => (default : X i)) (fun i => (default : X i)) := diagAt _
  have h1 := (import_order_embeds c cTrue t).1 (ht cTrue) _ _ hd
  have h2 := (import_order_embeds c cFalse t).1 (ht cFalse) _ _ hd
  rcases h1 with h1 | h1
  · exact absurd h1 (by simp [cTrue])
  rcases h2 with h2 | h2
  · exact absurd h2 (by simp [cFalse])
  have e1 : (some true : Option Bool) = t (fun i => (default : X i)) (fun i => (default : X i)) := h1
  have e2 : (some false : Option Bool) = t (fun i => (default : X i)) (fun i => (default : X i)) := h2
  exact absurd (e1.trans e2.symm) (by simp)

/-! ## The structure of external relations, and the classification of the cross

The import of an assemblage, its cross content, is EXTERNAL to the factors, IRREDUCIBLE to any operation on
them, FREE of every framework condition, and nonetheless STRUCTURED. This section proves those four properties
and then classifies the structure: the invariant readings of the cross are exactly the coarsenings of the
EQUINUMEROSITY-TYPED DIFFERING COUNT, over any product carrier, with no finiteness hypothesis.

The vocabulary is the differing set of a pair of points, adjacency (differing in exactly one coordinate, so the
region cells), and the cross-stable bijections, which are the carrier bijections preserving cross-hood.
Grouping coordinates by the EXISTENCE OF A BIJECTION between their fibres rather than by a cardinal is what
makes the classification finiteness-free; the cardinal reading is recovered at the end as a corollary. -/

/-! ### The differing set, adjacency, and the orbit relation -/


def diffSet (a b : Pt X) : Finset (Fin n) := Finset.univ.filter (fun i => a i ≠ b i)

theorem mem_diffSet {a b : Pt X} {i : Fin n} : i ∈ diffSet a b ↔ a i ≠ b i := by
  simp [diffSet]

theorem differsInOne_iff_diffSet (a b : Pt X) (i : Fin n) :
    differsInOne a b i ↔ diffSet a b = {i} := by
  constructor
  · rintro ⟨hne, hoth⟩
    ext j
    rw [mem_diffSet, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hji
      exact hj (hoth j hji)
    · intro hj; subst hj; exact hne
  · intro h
    refine ⟨?_, fun j hj => ?_⟩
    · exact mem_diffSet.mp (by rw [h]; exact Finset.mem_singleton_self i)
    · by_contra hc
      exact hj (Finset.mem_singleton.mp (by rw [← h]; exact mem_diffSet.mpr hc))

def Adjacent (a b : Pt X) : Prop := ∃ i, differsInOne a b i

omit [∀ i, DecidableEq (X i)] in
theorem not_adjacent_self (a : Pt X) : ¬ Adjacent a a := by
  rintro ⟨i, hne, _⟩
  exact hne rfl

def CrossStable (e : Pt X ≃ Pt X) : Prop := ∀ a b, IsCross a b ↔ IsCross (e a) (e b)

omit [∀ i, DecidableEq (X i)] in
theorem crossStable_iff_adjacent (e : Pt X ≃ Pt X) :
    CrossStable e ↔ ∀ a b, Adjacent a b ↔ Adjacent (e a) (e b) := by
  constructor
  · intro h a b; exact not_iff_not.mp (h a b)
  · intro h a b; exact not_iff_not.mpr (h a b)

/-- The common-neighbour characterization, restated. NOTE: this is a POINTWISE equivalence and uses no
counting, so it carries no finiteness. That is what makes the lift below possible. -/
theorem common_neighbours (a c : Pt X) (i : Fin n) (hac : differsInOne a c i) (d : Pt X) :
    (Adjacent a d ∧ Adjacent c d) ↔ (differsInOne a d i ∧ d ≠ c) := by
  constructor
  · rintro ⟨⟨k, hk⟩, hcd⟩
    have hki : k = i := by
      by_contra hne
      obtain ⟨l, hl⟩ := hcd
      have h1 : c i ≠ d i := by
        rw [← hk.2 i (fun hc => hne hc.symm)]
        exact fun hc => hac.1 hc.symm
      have h2 : c k ≠ d k := by
        rw [← hac.2 k hne]
        exact hk.1
      have hsing := (differsInOne_iff_diffSet c d l).mp hl
      have hi : i ∈ diffSet c d := mem_diffSet.mpr h1
      have hk' : k ∈ diffSet c d := mem_diffSet.mpr h2
      rw [hsing, Finset.mem_singleton] at hi hk'
      exact hne (hk'.trans hi.symm)
    subst hki
    refine ⟨hk, ?_⟩
    rintro rfl
    exact not_adjacent_self d hcd
  · rintro ⟨had, hdc⟩
    refine ⟨⟨i, had⟩, ⟨i, ?_, fun j hj => ?_⟩⟩
    · intro hc
      refine hdc (funext fun j => ?_)
      by_cases hj : j = i
      · subst hj; exact hc.symm
      · rw [← had.2 j hj, hac.2 j hj]
    · rw [← hac.2 j hj, had.2 j hj]

/-! ## Part 1: the equinumerosity type of a coordinate

The grouping the typed count does by cardinal, done instead by the existence of a bijection. Nothing here
mentions finiteness. -/

/-- Two coordinates are of the same type when their fibres admit a bijection. -/
def Equinumerous (i j : Fin n) : Prop := Nonempty (X i ≃ X j)

omit [∀ i, DecidableEq (X i)] in
theorem equinumerous_refl (i : Fin n) : Equinumerous (X := X) i i := ⟨Equiv.refl _⟩

omit [∀ i, DecidableEq (X i)] in
theorem equinumerous_symm {i j : Fin n} (h : Equinumerous (X := X) i j) :
    Equinumerous (X := X) j i := ⟨h.some.symm⟩

omit [∀ i, DecidableEq (X i)] in
theorem equinumerous_trans {i j k : Fin n} (h : Equinumerous (X := X) i j)
    (h' : Equinumerous (X := X) j k) : Equinumerous (X := X) i k := ⟨h.some.trans h'.some⟩

open Classical in
/-- **THE EQUINUMEROSITY-TYPED COUNT.** How many of the differing coordinates share a coordinate's type. The
grouping is by the existence of a bijection between fibres, so the definition carries NO finiteness. -/
noncomputable def eqTypedCount (a b : Pt X) (j : Fin n) : ℕ :=
  ((diffSet a b).filter (fun i => Equinumerous (X := X) i j)).card

/-- **It reduces to the cardinal typed count on finite fibres**, because equinumerosity of finite types is
equality of cardinality. So the finite reading is a special case, not a different object. -/
theorem eqTypedCount_eq_typedCount_of_finite [∀ i, Fintype (X i)] (a b : Pt X) (j : Fin n) :
    eqTypedCount a b j
      = ((diffSet a b).filter (fun i => Fintype.card (X i) = Fintype.card (X j))).card := by
  classical
  rw [eqTypedCount]
  congr 1
  apply Finset.filter_congr
  intro i _
  exact ⟨fun h => Fintype.card_eq.mpr h, fun h => Fintype.card_eq.mp h⟩

/-! ## Part 2: does the invariance lift?

The finite proof read the fibre SIZE off the graph by counting a line. That count needs finiteness. The
finiteness-free replacement reads the line as a SET and transports it, which gives a bijection rather than an
equal number. -/

/-- The line through `a` spanned by an adjacent `c`, characterized graph-theoretically: the neighbours of `a`
that are `c` or adjacent to `c`. No coordinate is named and no counting occurs. -/
def lineSet (a c : Pt X) : Set (Pt X) := {d | Adjacent a d ∧ (d = c ∨ Adjacent c d)}

/-- **The graph-theoretic line IS the coordinate line.** Finiteness-free, by `common_neighbours`. -/
theorem lineSet_eq (a c : Pt X) (i : Fin n) (hac : differsInOne a c i) :
    lineSet a c = {d | differsInOne a d i} := by
  ext d
  simp only [lineSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hadj, hd | hd⟩
    · subst hd; exact hac
    · exact ((common_neighbours a c i hac d).mp ⟨hadj, hd⟩).1
  · intro hd
    by_cases hdc : d = c
    · subst hdc; exact ⟨⟨i, hd⟩, Or.inl rfl⟩
    · exact ⟨⟨i, hd⟩, Or.inr ((common_neighbours a c i hac d).mpr ⟨hd, hdc⟩).2⟩

/-- The coordinate line is the fibre with one point removed: a point of the line is determined by its value at
that coordinate, which is anything other than the base point's value. -/
def lineEquiv (a : Pt X) (i : Fin n) :
    {d : Pt X // differsInOne a d i} ≃ {v : X i // v ≠ a i} where
  toFun d := ⟨d.1 i, fun h => d.2.1 h.symm⟩
  invFun v := ⟨Function.update a i v.1, by
    refine ⟨?_, fun j hj => ?_⟩
    · rw [Function.update_self]; exact fun h => v.2 h.symm
    · rw [Function.update_of_ne hj]⟩
  left_inv d := by
    refine Subtype.ext (funext fun j => ?_)
    show Function.update a i (d.1 i) j = d.1 j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]
    · rw [Function.update_of_ne hj]; exact d.2.2 j hj
  right_inv v := by
    refine Subtype.ext ?_
    show Function.update a i v.1 i = v.1
    rw [Function.update_self]

omit [∀ i, DecidableEq (X i)] in
/-- A cross-stable bijection carries a line to a line: membership is defined by adjacency alone. -/
theorem mem_lineSet_map (e : Pt X ≃ Pt X) (he : CrossStable e) (a c d : Pt X) :
    d ∈ lineSet a c ↔ e d ∈ lineSet (e a) (e c) := by
  have hadj := (crossStable_iff_adjacent e).mp he
  simp only [lineSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨(hadj a d).mp h1, Or.inl (by rw [h2])⟩
    · exact ⟨(hadj a d).mp h1, Or.inr ((hadj c d).mp h2)⟩
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨(hadj a d).mpr h1, Or.inl (e.injective h2)⟩
    · exact ⟨(hadj a d).mpr h1, Or.inr ((hadj c d).mpr h2)⟩

/-- Punctured types with a bijection between them have a bijection between the wholes: add the removed point
back on each side. Finiteness-free. -/
def eqSubtypeEquivUnit {A : Type} (x : A) : {v : A // v = x} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨x, rfl⟩
  left_inv v := Subtype.ext v.2.symm
  right_inv _ := rfl

theorem equiv_of_punctured {A B : Type} [DecidableEq A] [DecidableEq B] (x : A) (y : B)
    (h : {v : A // v ≠ x} ≃ {v : B // v ≠ y}) : Nonempty (A ≃ B) :=
  ⟨(Equiv.sumCompl (· = x)).symm.trans
    ((Equiv.sumCongr (eqSubtypeEquivUnit x) h).trans
      ((Equiv.sumCongr (eqSubtypeEquivUnit y).symm (Equiv.refl _)).trans
        (Equiv.sumCompl (· = y))))⟩

/-- **THE INVARIANCE MECHANISM, LIFTED OFF FINITENESS.** If a cross-stable bijection carries a pair differing
at coordinate `i` to a pair differing at coordinate `j`, then the two fibres are EQUINUMEROUS. The finite proof
counted a line; this one transports the line as a set and reads a bijection off it, so no finiteness is used
anywhere. -/
theorem crossStable_equinumerous (e : Pt X ≃ Pt X) (he : CrossStable e) (a c : Pt X) (i j : Fin n)
    (hac : differsInOne a c i) (hej : differsInOne (e a) (e c) j) :
    Equinumerous (X := X) i j := by
  have hline : {d : Pt X // differsInOne a d i} ≃ {d : Pt X // differsInOne (e a) d j} := by
    refine ⟨fun d => ⟨e d.1, ?_⟩, fun d => ⟨e.symm d.1, ?_⟩, ?_, ?_⟩
    · have hmem : d.1 ∈ lineSet a c := by rw [lineSet_eq a c i hac]; exact d.2
      have := (mem_lineSet_map e he a c d.1).mp hmem
      rwa [lineSet_eq (e a) (e c) j hej] at this
    · have hmem : d.1 ∈ lineSet (e a) (e c) := by rw [lineSet_eq (e a) (e c) j hej]; exact d.2
      have := (mem_lineSet_map e he a c (e.symm d.1)).mpr (by rwa [Equiv.apply_symm_apply])
      rwa [lineSet_eq a c i hac] at this
    · intro d; exact Subtype.ext (Equiv.symm_apply_apply e d.1)
    · intro d; exact Subtype.ext (Equiv.apply_symm_apply e d.1)
  exact equiv_of_punctured (a i) ((e a) j)
    (((lineEquiv a i).symm.trans hline).trans (lineEquiv (e a) j))

theorem exists_differsInOne_iff_card (a b : Pt X) :
    (∃ k, differsInOne a b k) ↔ (diffSet a b).card = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    rw [(differsInOne_iff_diffSet a b k).mp hk]
    exact Finset.card_singleton k
  · intro h
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h
    exact ⟨k, (differsInOne_iff_diffSet a b k).mpr hk⟩

/-- A bijection permuting the differing set by a fixed index permutation is cross-stable: the differing sets
correspond, so their sizes agree, and being cross is the size not being one. -/
theorem crossStable_of_diffSet_perm (e : Pt X ≃ Pt X) (σ : Equiv.Perm (Fin n))
    (h : ∀ a b k, k ∈ diffSet (e a) (e b) ↔ σ k ∈ diffSet a b) : CrossStable e := by
  intro a b
  have hmap : diffSet (e a) (e b) = (diffSet a b).map σ.symm.toEmbedding := by
    ext k
    rw [h a b k, Finset.mem_map]
    constructor
    · intro hk
      refine ⟨σ k, hk, ?_⟩
      show σ.symm (σ k) = k
      rw [Equiv.symm_apply_apply]
    · rintro ⟨m, hm, rfl⟩
      show σ (σ.symm m) ∈ _
      rw [Equiv.apply_symm_apply]
      exact hm
  have hcard : (diffSet (e a) (e b)).card = (diffSet a b).card := by
    rw [hmap, Finset.card_map]
  show (¬ ∃ k, differsInOne a b k) ↔ (¬ ∃ k, differsInOne (e a) (e b) k)
  rw [exists_differsInOne_iff_card, exists_differsInOne_iff_card, hcard]

def SameOrbit (a b a' b' : Pt X) : Prop :=
  ∃ e : Pt X ≃ Pt X, CrossStable e ∧ e a = a' ∧ e b = b'

omit [∀ i, DecidableEq (X i)] in
theorem crossStable_trans {e f : Pt X ≃ Pt X} (he : CrossStable e) (hf : CrossStable f) :
    CrossStable (e.trans f) := fun a b => (he a b).trans (hf (e a) (e b))

omit [∀ i, DecidableEq (X i)] in
theorem sameOrbit_trans {a b a' b' a'' b'' : Pt X}
    (h : SameOrbit a b a' b') (h' : SameOrbit a' b' a'' b'') : SameOrbit a b a'' b'' := by
  obtain ⟨e, he, h1, h2⟩ := h
  obtain ⟨f, hf, k1, k2⟩ := h'
  refine ⟨e.trans f, crossStable_trans he hf, ?_, ?_⟩
  · show f (e a) = a''; rw [h1, k1]
  · show f (e b) = b''; rw [h2, k2]

theorem exists_equiv_pair {Y : Type} [DecidableEq Y] {u v u' v' : Y} (huv : u ≠ v) (huv' : u' ≠ v') :
    ∃ f : Y ≃ Y, f u = u' ∧ f v = v' := by
  refine ⟨(Equiv.swap u u').trans (Equiv.swap (Equiv.swap u u' v) v'), ?_, ?_⟩
  · show Equiv.swap (Equiv.swap u u' v) v' (Equiv.swap u u' u) = u'
    rw [Equiv.swap_apply_left]
    by_cases hw : Equiv.swap u u' v = v'
    · rw [hw, Equiv.swap_self]
      rfl
    · refine Equiv.swap_apply_of_ne_of_ne ?_ huv'
      intro hc
      by_cases hvu' : v = u'
      · rw [hvu', Equiv.swap_apply_right] at hc
        exact huv (hvu'.trans hc).symm
      · rw [Equiv.swap_apply_of_ne_of_ne (fun hx => huv hx.symm) hvu'] at hc
        exact hvu' hc.symm
  · show Equiv.swap (Equiv.swap u u' v) v' (Equiv.swap u u' v) = v'
    exact Equiv.swap_apply_left _ _

noncomputable def movePair {Y : Type} [DecidableEq Y] (u v u' v' : Y) : Y ≃ Y :=
  if h : u ≠ v ∧ u' ≠ v' then Classical.choose (exists_equiv_pair h.1 h.2)
  else Equiv.swap u u'

theorem movePair_spec_ne {Y : Type} [DecidableEq Y] {u v u' v' : Y} (huv : u ≠ v) (huv' : u' ≠ v') :
    movePair u v u' v' u = u' ∧ movePair u v u' v' v = v' := by
  have hd : u ≠ v ∧ u' ≠ v' := ⟨huv, huv'⟩
  rw [movePair, dif_pos hd]
  exact Classical.choose_spec (exists_equiv_pair hd.1 hd.2)

theorem movePair_spec_eq {Y : Type} [DecidableEq Y] {u v u' v' : Y} (huv : u = v) (huv' : u' = v') :
    movePair u v u' v' u = u' ∧ movePair u v u' v' v = v' := by
  have hd : ¬ (u ≠ v ∧ u' ≠ v') := fun h => h.1 huv
  rw [movePair, dif_neg hd]
  refine ⟨Equiv.swap_apply_left u u', ?_⟩
  rw [← huv, Equiv.swap_apply_left u u']
  exact huv'

def fibEquiv (π : ∀ k, X k ≃ X k) : Pt X ≃ Pt X where
  toFun a := fun k => π k (a k)
  invFun a := fun k => (π k).symm (a k)
  left_inv a := by funext k; exact (π k).symm_apply_apply (a k)
  right_inv a := by funext k; exact (π k).apply_symm_apply (a k)

theorem diffSet_fibEquiv (π : ∀ k, X k ≃ X k) (a b : Pt X) :
    diffSet (fibEquiv π a) (fibEquiv π b) = diffSet a b := by
  ext k
  rw [mem_diffSet, mem_diffSet]
  show π k (a k) ≠ π k (b k) ↔ a k ≠ b k
  exact ⟨fun h hc => h (by rw [hc]), fun h hc => h ((π k).injective hc)⟩

theorem fibEquiv_crossStable (π : ∀ k, X k ≃ X k) : CrossStable (fibEquiv π) :=
  crossStable_of_diffSet_perm _ (Equiv.refl _) (fun a b k => by
    rw [diffSet_fibEquiv]; exact Iff.rfl)

/-- The coordinatewise half: two cells with the same differing set lie in one orbit, no hypothesis. -/
theorem sameOrbit_of_same_diffSet (a b a' b' : Pt X) (h : diffSet a b = diffSet a' b') :
    SameOrbit a b a' b' := by
  refine ⟨fibEquiv (fun k => movePair (a k) (b k) (a' k) (b' k)),
    fibEquiv_crossStable _, ?_, ?_⟩
  · funext k
    show movePair (a k) (b k) (a' k) (b' k) (a k) = a' k
    by_cases hk : a k = b k
    · have hk' : a' k = b' k := by
        by_contra hc
        have h1 : k ∈ diffSet a' b' := mem_diffSet.mpr hc
        rw [← h] at h1
        exact (mem_diffSet.mp h1) hk
      exact (movePair_spec_eq hk hk').1
    · have hk' : a' k ≠ b' k := by
        intro hc
        have h1 : k ∈ diffSet a b := mem_diffSet.mpr hk
        rw [h] at h1
        exact (mem_diffSet.mp h1) hc
      exact (movePair_spec_ne hk hk').1
  · funext k
    show movePair (a k) (b k) (a' k) (b' k) (b k) = b' k
    by_cases hk : a k = b k
    · have hk' : a' k = b' k := by
        by_contra hc
        have h1 : k ∈ diffSet a' b' := mem_diffSet.mpr hc
        rw [← h] at h1
        exact (mem_diffSet.mp h1) hk
      exact (movePair_spec_eq hk hk').2
    · have hk' : a' k ≠ b' k := by
        intro hc
        have h1 : k ∈ diffSet a b := mem_diffSet.mpr hk
        rw [h] at h1
        exact (mem_diffSet.mp h1) hc
      exact (movePair_spec_ne hk hk').2

/-! ## Part 1: the exchange between equinumerous fibres

The map below is the one the previous build did not attempt. It exchanges coordinates `i` and `j` while
carrying the value across an equivalence `X i` to `X j`. The value at `i` has type `X i` and must be delivered
at `j`, which needs a CAST, and every lemma about the map passes through it. -/

/-- **THE TYPED EXCHANGE.** Swap coordinates `i` and `j`, transporting the values along `ψ`. The two casts are
what make the definition typecheck at all: the branch for `k = i` produces a value of type `X i` and must be
delivered at type `X k`. -/
def swapT (i j : Fin n) (ψ : X i ≃ X j) (a : Pt X) : Pt X :=
  fun k =>
    if hi : k = i then cast (congrArg X hi.symm) (ψ.symm (a j))
    else if hj : k = j then cast (congrArg X hj.symm) (ψ (a i))
    else a k

omit [∀ i, DecidableEq (X i)] in
/-- Reading the exchange at `i`: the cast is along `rfl` and vanishes. -/
theorem swapT_i (ψ : X i ≃ X j) (a : Pt X) : swapT i j ψ a i = ψ.symm (a j) := by
  show (if hi : i = i then cast (congrArg X hi.symm) (ψ.symm (a j))
        else if hj : i = j then cast (congrArg X hj.symm) (ψ (a i)) else a i) = ψ.symm (a j)
  rw [dif_pos (rfl : i = i)]
  rfl

omit [∀ i, DecidableEq (X i)] in
/-- Reading the exchange at `j`. -/
theorem swapT_j (hij : i ≠ j) (ψ : X i ≃ X j) (a : Pt X) : swapT i j ψ a j = ψ (a i) := by
  show (if hi : j = i then cast (congrArg X hi.symm) (ψ.symm (a j))
        else if hj : j = j then cast (congrArg X hj.symm) (ψ (a i)) else a j) = ψ (a i)
  rw [dif_neg (fun h => hij h.symm), dif_pos (rfl : j = j)]
  rfl

omit [∀ i, DecidableEq (X i)] in
/-- Reading the exchange anywhere else: untouched. -/
theorem swapT_other (ψ : X i ≃ X j) (a : Pt X) {k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    swapT i j ψ a k = a k := by
  show (if hi : k = i then cast (congrArg X hi.symm) (ψ.symm (a j))
        else if hj : k = j then cast (congrArg X hj.symm) (ψ (a i)) else a k) = a k
  rw [dif_neg hki, dif_neg hkj]

omit [∀ i, DecidableEq (X i)] in
theorem swapT_involutive (hij : i ≠ j) (ψ : X i ≃ X j) (a : Pt X) :
    swapT i j ψ (swapT i j ψ a) = a := by
  funext k
  by_cases hki : k = i
  · subst hki
    rw [swapT_i, swapT_j hij, Equiv.symm_apply_apply]
  · by_cases hkj : k = j
    · subst hkj
      rw [swapT_j hij, swapT_i, Equiv.apply_symm_apply]
    · rw [swapT_other ψ _ hki hkj, swapT_other ψ a hki hkj]

/-- The exchange as a bijection of the carrier. -/
def coordSwapT (hij : i ≠ j) (ψ : X i ≃ X j) : Pt X ≃ Pt X :=
  ⟨swapT i j ψ, swapT i j ψ, swapT_involutive hij ψ, swapT_involutive hij ψ⟩

/-- **The exchange permutes the differing set by the index swap.** Every clause passes through a cast, and the
casts are discharged by the three reading lemmas above rather than by any tactic guessing. -/
theorem mem_diffSet_swapT (hij : i ≠ j) (ψ : X i ≃ X j) (a b : Pt X) (k : Fin n) :
    k ∈ diffSet (swapT i j ψ a) (swapT i j ψ b) ↔ Equiv.swap i j k ∈ diffSet a b := by
  rw [mem_diffSet, mem_diffSet]
  by_cases hki : k = i
  · subst hki
    rw [swapT_i, swapT_i, Equiv.swap_apply_left]
    exact ⟨fun h hc => h (by rw [hc]), fun h hc => h (ψ.symm.injective hc)⟩
  · by_cases hkj : k = j
    · subst hkj
      rw [swapT_j hij, swapT_j hij, Equiv.swap_apply_right]
      exact ⟨fun h hc => h (by rw [hc]), fun h hc => h (ψ.injective hc)⟩
    · rw [swapT_other ψ a hki hkj, swapT_other ψ b hki hkj,
        Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem diffSet_swapT (hij : i ≠ j) (ψ : X i ≃ X j) (a b : Pt X) :
    diffSet (swapT i j ψ a) (swapT i j ψ b)
      = (diffSet a b).map (Equiv.swap i j).toEmbedding := by
  ext k
  rw [mem_diffSet_swapT hij, Finset.mem_map]
  constructor
  · intro hk
    refine ⟨Equiv.swap i j k, hk, ?_⟩
    show Equiv.swap i j (Equiv.swap i j k) = k
    rw [Equiv.swap_apply_self]
  · rintro ⟨m, hm, rfl⟩
    show Equiv.swap i j (Equiv.swap i j m) ∈ _
    rw [Equiv.swap_apply_self]
    exact hm

/-- **The exchange is cross-stable.** -/
theorem coordSwapT_crossStable (hij : i ≠ j) (ψ : X i ≃ X j) :
    CrossStable (coordSwapT hij ψ) :=
  crossStable_of_diffSet_perm _ (Equiv.swap i j) (fun a b k => mem_diffSet_swapT hij ψ a b k)

/-- The exchange step, at the level of the set difference. -/
theorem sdiff_after_swapT (S T : Finset (Fin n)) {i j : Fin n}
    (hi : i ∈ S) (hiT : i ∉ T) (hj : j ∈ T) (hjS : j ∉ S) :
    (S.map (Equiv.swap i j).toEmbedding) \ T = (S \ T).erase i := by
  ext k
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hkT⟩
    have hpi : p ≠ i := by
      intro hc
      subst hc
      rw [Equiv.swap_apply_left] at hkT
      exact hkT hj
    have hpj : p ≠ j := fun hc => hjS (hc ▸ hp)
    rw [Equiv.swap_apply_of_ne_of_ne hpi hpj] at hkT ⊢
    exact ⟨hpi, hp, hkT⟩
  · rintro ⟨hki, hkS, hkT⟩
    have hkj : k ≠ j := fun hc => hkT (hc ▸ hj)
    exact ⟨⟨k, hkS, Equiv.swap_apply_of_ne_of_ne hki hkj⟩, hkT⟩

/-! ## Part 2b: does the transitivity lift?

The exchange takes a bijection between two fibres as a parameter and never mentions cardinality. The finite
proof obtained that bijection from equal cardinalities; here it comes straight from equinumerosity, which is
the only place finiteness entered. -/

/-- **The exchange preserves every equinumerosity-typed count.** It swaps two coordinates of the SAME type, so
each type class keeps its membership count. Finiteness-free. -/
theorem eqTypedCount_swapT {i j : Fin n} (hij : i ≠ j) (ψ : X i ≃ X j)
    (heq : Equinumerous (X := X) i j) (a b : Pt X) (m : Fin n) :
    eqTypedCount (swapT i j ψ a) (swapT i j ψ b) m = eqTypedCount a b m := by
  classical
  have hP : ∀ p : Fin n,
      Equinumerous (X := X) (Equiv.swap i j p) m ↔ Equinumerous (X := X) p m := by
    intro p
    by_cases hpi : p = i
    · subst hpi
      rw [Equiv.swap_apply_left]
      exact ⟨fun h => equinumerous_trans heq h, fun h => equinumerous_trans (equinumerous_symm heq) h⟩
    · by_cases hpj : p = j
      · subst hpj
        rw [Equiv.swap_apply_right]
        exact ⟨fun h => equinumerous_trans (equinumerous_symm heq) h,
          fun h => equinumerous_trans heq h⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj]
  have hset : ((diffSet a b).map (Equiv.swap i j).toEmbedding).filter
        (fun p => Equinumerous (X := X) p m)
      = ((diffSet a b).filter (fun p => Equinumerous (X := X) p m)).map
        (Equiv.swap i j).toEmbedding := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hk⟩
      exact ⟨p, ⟨hp, (hP p).mp hk⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hq⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, (hP p).mpr hq⟩
  rw [eqTypedCount, eqTypedCount, diffSet_swapT hij, hset, Finset.card_map]

/-- **THE TRANSITIVITY, FINITENESS-FREE.** Two cells with the same equinumerosity-typed count lie in one
orbit, at any product carrier, finite or not. The induction is the finite one with the bijection sourced from
equinumerosity instead of from equal cardinalities. -/
theorem sameOrbit_of_same_eqTypedCount_aux : ∀ (N : ℕ) (a b a' b' : Pt X),
    (diffSet a b \ diffSet a' b').card = N →
    (∀ m, eqTypedCount a b m = eqTypedCount a' b' m) →
    SameOrbit a b a' b' := by
  classical
  intro N
  induction N with
  | zero =>
    intro a b a' b' hN hq
    have hsub : diffSet a b ⊆ diffSet a' b' := by
      rw [← Finset.sdiff_eq_empty_iff_subset]
      exact Finset.card_eq_zero.mp hN
    refine sameOrbit_of_same_diffSet a b a' b' ?_
    by_contra hne
    obtain ⟨j, hj⟩ : (diffSet a' b' \ diffSet a b).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hc
      exact hne (Finset.Subset.antisymm hsub hc)
    rw [Finset.mem_sdiff] at hj
    have hss : (diffSet a b).filter (fun p => Equinumerous (X := X) p j)
        ⊂ (diffSet a' b').filter (fun p => Equinumerous (X := X) p j) := by
      refine ⟨Finset.filter_subset_filter _ hsub, ?_⟩
      intro hc
      have : j ∈ (diffSet a b).filter (fun p => Equinumerous (X := X) p j) :=
        hc (Finset.mem_filter.mpr ⟨hj.1, equinumerous_refl j⟩)
      exact hj.2 (Finset.mem_filter.mp this).1
    have := Finset.card_lt_card hss
    rw [← eqTypedCount, ← eqTypedCount, hq j] at this
    omega
  | succ M ih =>
    intro a b a' b' hN hq
    set S := diffSet a b with hS
    set T := diffSet a' b' with hT
    have hne : (S \ T).Nonempty := Finset.card_pos.mp (by rw [hN]; omega)
    obtain ⟨k, hkST⟩ := hne
    rw [Finset.mem_sdiff] at hkST
    set A := S.filter (fun p => Equinumerous (X := X) p k) with hA
    set B := T.filter (fun p => Equinumerous (X := X) p k) with hB
    have hkA : k ∈ A := Finset.mem_filter.mpr ⟨hkST.1, equinumerous_refl k⟩
    have hkB : k ∉ B := fun hc => hkST.2 (Finset.mem_filter.mp hc).1
    have hABcard : A.card = B.card := hq k
    have hBA : (B \ A).Nonempty := by
      refine Finset.card_pos.mp ?_
      have h1 : (A \ B).card + (A ∩ B).card = A.card := Finset.card_sdiff_add_card_inter A B
      have h2 : (B \ A).card + (B ∩ A).card = B.card := Finset.card_sdiff_add_card_inter B A
      have h3 : (A ∩ B).card = (B ∩ A).card := by rw [Finset.inter_comm]
      have h4 : 0 < (A \ B).card :=
        Finset.card_pos.mpr ⟨k, Finset.mem_sdiff.mpr ⟨hkA, hkB⟩⟩
      omega
    obtain ⟨j, hjBA⟩ := hBA
    rw [Finset.mem_sdiff] at hjBA
    have hjT : j ∈ T := (Finset.mem_filter.mp hjBA.1).1
    have hjq : Equinumerous (X := X) j k := (Finset.mem_filter.mp hjBA.1).2
    have hjS : j ∉ S := fun hc => hjBA.2 (Finset.mem_filter.mpr ⟨hc, hjq⟩)
    have hkj : k ≠ j := fun hc => hjS (hc ▸ hkST.1)
    have hkjEq : Equinumerous (X := X) k j := equinumerous_symm hjq
    let ψ : X k ≃ X j := hkjEq.some
    have hstep : SameOrbit a b (swapT k j ψ a) (swapT k j ψ b) :=
      ⟨coordSwapT hkj ψ, coordSwapT_crossStable hkj ψ, rfl, rfl⟩
    refine sameOrbit_trans hstep (ih (swapT k j ψ a) (swapT k j ψ b) a' b' ?_ ?_)
    · rw [diffSet_swapT hkj, ← hS, ← hT,
        sdiff_after_swapT S T hkST.1 hkST.2 hjT hjS,
        Finset.card_erase_of_mem (Finset.mem_sdiff.mpr hkST)]
      omega
    · intro r
      rw [eqTypedCount_swapT hkj ψ hkjEq]
      exact hq r

theorem sameOrbit_of_same_eqTypedCount (a b a' b' : Pt X)
    (h : ∀ m, eqTypedCount a b m = eqTypedCount a' b' m) : SameOrbit a b a' b' :=
  sameOrbit_of_same_eqTypedCount_aux _ a b a' b' rfl h

theorem diffSet_eq_empty_iff (a b : Pt X) : diffSet a b = ∅ ↔ a = b := by
  constructor
  · intro h
    funext i
    by_contra hne
    have : i ∈ (∅ : Finset (Fin n)) := by rw [← h]; exact mem_diffSet.mpr hne
    simp at this
  · intro h
    subst h
    exact Finset.filter_eq_empty_iff.mpr (fun _ _ => by simp)

theorem diffSet_subset_union (a b c : Pt X) : diffSet a b ⊆ diffSet a c ∪ diffSet c b := by
  intro i hi
  rw [mem_diffSet] at hi
  rw [Finset.mem_union, mem_diffSet, mem_diffSet]
  by_contra hc
  have h1 : a i = c i := by by_contra h; exact hc (Or.inl h)
  have h2 : c i = b i := by by_contra h; exact hc (Or.inr h)
  exact hi (h1.trans h2)

def Steps : Nat → Pt X → Pt X → Prop
  | 0, a, b => a = b
  | (m + 1), a, b => ∃ c, Adjacent a c ∧ Steps m c b

theorem steps_of_diffSet : ∀ (k : Nat) (a b : Pt X), (diffSet a b).card = k → Steps k a b := by
  intro k
  induction k with
  | zero =>
    intro a b h
    exact (diffSet_eq_empty_iff a b).mp (Finset.card_eq_zero.mp h)
  | succ m ih =>
    intro a b h
    have hne : (diffSet a b).Nonempty := Finset.card_pos.mp (by rw [h]; omega)
    obtain ⟨i, hi⟩ := hne
    refine ⟨Function.update a i (b i), ⟨i, ?_⟩, ?_⟩
    · refine ⟨?_, fun j hj => ?_⟩
      · rw [Function.update_self]
        exact mem_diffSet.mp hi
      · rw [Function.update_of_ne hj]
    · refine ih _ b ?_
      have hset : diffSet (Function.update a i (b i)) b = (diffSet a b).erase i := by
        ext j
        rw [mem_diffSet, Finset.mem_erase, mem_diffSet]
        by_cases hj : j = i
        · subst hj
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hj]
          exact ⟨fun hc => ⟨hj, hc⟩, fun hc => hc.2⟩
      rw [hset, Finset.card_erase_of_mem hi, h]
      omega

theorem card_le_of_steps : ∀ (m : Nat) (a b : Pt X), Steps m a b → (diffSet a b).card ≤ m := by
  intro m
  induction m with
  | zero =>
    intro a b h
    have hab : a = b := h
    subst hab
    simp [(diffSet_eq_empty_iff a a).mpr rfl]
  | succ m ih =>
    intro a b h
    obtain ⟨c, ⟨i, hi⟩, hrest⟩ := h
    have hac : (diffSet a c).card = 1 := by
      rw [(differsInOne_iff_diffSet a c i).mp hi]
      exact Finset.card_singleton i
    have hcb := ih c b hrest
    calc (diffSet a b).card
        ≤ (diffSet a c ∪ diffSet c b).card := Finset.card_le_card (diffSet_subset_union a b c)
      _ ≤ (diffSet a c).card + (diffSet c b).card := Finset.card_union_le _ _
      _ ≤ 1 + m := Nat.add_le_add (le_of_eq hac) hcb
      _ = m + 1 := by omega

omit [∀ i, DecidableEq (X i)] in
theorem crossStable_symm {e : Pt X ≃ Pt X} (he : CrossStable e) : CrossStable e.symm := by
  intro a b
  have h := he (e.symm a) (e.symm b)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact h.symm

omit [∀ i, DecidableEq (X i)] in
theorem steps_transport {e : Pt X ≃ Pt X} (he : CrossStable e) :
    ∀ (m : Nat) (a b : Pt X), Steps m a b → Steps m (e a) (e b) := by
  intro m
  induction m with
  | zero => intro a b h; exact congrArg e h
  | succ m ih =>
    intro a b h
    obtain ⟨c, hadj, hrest⟩ := h
    exact ⟨e c, ((crossStable_iff_adjacent e).mp he a c).mp hadj, ih c b hrest⟩

/-- The plain differing count is preserved: cross-stability is adjacency preservation, and the count is the
shortest chain length. -/
theorem crossStable_preserves_diffCard {e : Pt X ≃ Pt X} (he : CrossStable e) (a b : Pt X) :
    (diffSet (e a) (e b)).card = (diffSet a b).card := by
  refine Nat.le_antisymm ?_ ?_
  · exact card_le_of_steps _ _ _ (steps_transport he _ a b (steps_of_diffSet _ a b rfl))
  · have hs := steps_of_diffSet (diffSet (e a) (e b)).card (e a) (e b) rfl
    have ht := steps_transport (crossStable_symm he) _ (e a) (e b) hs
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at ht
    exact card_le_of_steps _ _ _ ht

/-- The point one step from `p` toward `q` along coordinate `i`. -/
def stepAt (p q : Pt X) (i : Fin n) : Pt X := Function.update p i (q i)

theorem diffSet_stepAt_left {p q : Pt X} {i : Fin n} (hi : i ∈ diffSet p q) :
    diffSet p (stepAt p q i) = {i} := by
  ext j
  rw [mem_diffSet, Finset.mem_singleton]
  by_cases hj : j = i
  · subst hj
    rw [stepAt, Function.update_self]
    exact ⟨fun _ => rfl, fun _ => mem_diffSet.mp hi⟩
  · rw [stepAt, Function.update_of_ne hj]
    exact ⟨fun hc => absurd rfl hc, fun hc => absurd hc hj⟩

theorem diffSet_stepAt_right (p q : Pt X) (i : Fin n) :
    diffSet (stepAt p q i) q = (diffSet p q).erase i := by
  ext j
  rw [mem_diffSet, Finset.mem_erase, mem_diffSet]
  by_cases hj : j = i
  · subst hj
    rw [stepAt, Function.update_self]
    exact ⟨fun hc => absurd rfl hc, fun hc => absurd rfl hc.1⟩
  · rw [stepAt, Function.update_of_ne hj]
    exact ⟨fun hc => ⟨hj, hc⟩, fun hc => hc.2⟩

theorem stepAt_injOn (p q : Pt X) :
    ∀ i ∈ diffSet p q, ∀ j ∈ diffSet p q, stepAt p q i = stepAt p q j → i = j := by
  intro i hi j _ h
  by_contra hij
  have := congrFun h i
  rw [stepAt, stepAt, Function.update_self, Function.update_of_ne hij] at this
  exact (mem_diffSet.mp hi) this.symm

/-! ## Part 2c: assembling the mechanism into arbitrary-distance invariance

The mechanism is local, so it must be lifted to a whole cell by the first steps: each differing coordinate
sends its first step across, and the image is a first step of the image cell at an equinumerous coordinate. -/

/-- The image of a first step is a first step. -/
theorem image_step_adjacent (e : Pt X ≃ Pt X) (he : CrossStable e) (a b : Pt X) {i : Fin n}
    (hi : i ∈ diffSet a b) : ∃ j, differsInOne (e a) (e (stepAt a b i)) j := by
  have hadj : Adjacent a (stepAt a b i) := ⟨i, (differsInOne_iff_diffSet _ _ i).mpr
    (diffSet_stepAt_left hi)⟩
  exact (crossStable_iff_adjacent e).mp he a (stepAt a b i) |>.mp hadj

/-- And it lands at a differing coordinate of the image cell, because the plain count is preserved and the
step reduced it by one. -/
theorem image_step_mem (e : Pt X ≃ Pt X) (he : CrossStable e) (a b : Pt X) {i : Fin n}
    (hi : i ∈ diffSet a b) {j : Fin n} (hj : differsInOne (e a) (e (stepAt a b i)) j) :
    j ∈ diffSet (e a) (e b) := by
  by_contra hmem
  have hstep : (diffSet (e (stepAt a b i)) (e b)).card + 1 = (diffSet (e a) (e b)).card := by
    rw [crossStable_preserves_diffCard he, crossStable_preserves_diffCard he,
      diffSet_stepAt_right, Finset.card_erase_of_mem hi]
    have := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have hins : diffSet (e (stepAt a b i)) (e b) = insert j (diffSet (e a) (e b)) := by
    ext p
    rw [mem_diffSet, Finset.mem_insert, mem_diffSet]
    by_cases hp : p = j
    · subst hp
      have hpq : (e a) p = (e b) p := by
        by_contra hc
        exact hmem (mem_diffSet.mpr hc)
      exact ⟨fun _ => Or.inl rfl, fun _ hc => hj.1 (hpq.trans hc.symm)⟩
    · rw [hj.2 p hp]
      exact ⟨fun hc => Or.inr hc, fun hc => hc.resolve_left hp⟩
  rw [hins, Finset.card_insert_of_notMem hmem] at hstep
  omega

/-- The image of a first step is the first step of the image cell at that coordinate, so the correspondence is
injective. -/
theorem image_step_eq (e : Pt X ≃ Pt X) (he : CrossStable e) (a b : Pt X) {i : Fin n}
    (hi : i ∈ diffSet a b) {j : Fin n} (hj : differsInOne (e a) (e (stepAt a b i)) j) :
    e (stepAt a b i) = stepAt (e a) (e b) j := by
  have hjm := image_step_mem e he a b hi hj
  have hval : (e (stepAt a b i)) j = (e b) j := by
    by_contra hval
    have hsame : diffSet (e (stepAt a b i)) (e b) = diffSet (e a) (e b) := by
      ext p
      rw [mem_diffSet, mem_diffSet]
      by_cases hp : p = j
      · subst hp
        exact ⟨fun _ => mem_diffSet.mp hjm, fun _ => hval⟩
      · rw [hj.2 p hp]
    have hcnt : (diffSet (e (stepAt a b i)) (e b)).card + 1 = (diffSet (e a) (e b)).card := by
      rw [crossStable_preserves_diffCard he, crossStable_preserves_diffCard he,
        diffSet_stepAt_right, Finset.card_erase_of_mem hi]
      have := Finset.card_pos.mpr ⟨i, hi⟩
      omega
    rw [hsame] at hcnt
    omega
  funext p
  by_cases hp : p = j
  · subst hp
    show e (stepAt a b i) p = Function.update (e a) p ((e b) p) p
    rw [Function.update_self]
    exact hval
  · show e (stepAt a b i) p = Function.update (e a) j ((e b) j) p
    rw [Function.update_of_ne hp]
    exact (hj.2 p hp).symm

open Classical in
/-- **THE INVARIANCE, FINITENESS-FREE.** Every cross-stable bijection preserves every equinumerosity-typed
count, at arbitrary distance and at any carrier. The counting is over coordinates, which are finite by the
arity; nothing counts values. -/
theorem eqTypedCount_crossStable_invariant (e : Pt X ≃ Pt X) (he : CrossStable e) (a b : Pt X)
    (m : Fin n) : eqTypedCount (e a) (e b) m = eqTypedCount a b m := by
  classical
  have key : ∀ (f : Pt X ≃ Pt X), CrossStable f → ∀ p q : Pt X,
      ((diffSet p q).filter (fun i => Equinumerous (X := X) i m)).card
        ≤ ((diffSet (f p) (f q)).filter (fun i => Equinumerous (X := X) i m)).card := by
    intro f hf p q
    refine Finset.card_le_card_of_injOn
      (fun i => if hi : i ∈ diffSet p q then (image_step_adjacent f hf p q hi).choose else i)
      ?_ ?_
    · intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      simp only [Finset.mem_coe, Finset.mem_filter, dif_pos hi.1]
      have hspec := (image_step_adjacent f hf p q hi.1).choose_spec
      refine ⟨image_step_mem f hf p q hi.1 hspec, ?_⟩
      have heq := crossStable_equinumerous f hf p (stepAt p q i) i _
        ((differsInOne_iff_diffSet _ _ i).mpr (diffSet_stepAt_left hi.1)) hspec
      exact equinumerous_trans (equinumerous_symm heq) hi.2
    · intro i hi j hj hij
      rw [Finset.mem_coe, Finset.mem_filter] at hi hj
      simp only [dif_pos hi.1, dif_pos hj.1] at hij
      have e1 := image_step_eq f hf p q hi.1 (image_step_adjacent f hf p q hi.1).choose_spec
      have e2 := image_step_eq f hf p q hj.1 (image_step_adjacent f hf p q hj.1).choose_spec
      have : f (stepAt p q i) = f (stepAt p q j) := by rw [e1, e2, hij]
      exact stepAt_injOn p q i hi.1 j hj.1 (f.injective this)
  refine Nat.le_antisymm ?_ (key e he a b)
  have hback := key e.symm (crossStable_symm he) (e a) (e b)
  rwa [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hback

/-- **THE ORBIT PARTITION IS THE EQUINUMEROSITY-TYPED COUNT, over ANY product carrier**, finite or not. Both
inclusions, no `Fintype` anywhere in the statement or in either proof. -/
theorem orbit_partition_is_eqTypedCount (a b a' b' : Pt X) :
    SameOrbit a b a' b' ↔ ∀ m, eqTypedCount a b m = eqTypedCount a' b' m := by
  constructor
  · rintro ⟨e, he, rfl, rfl⟩ m
    exact (eqTypedCount_crossStable_invariant e he a b m).symm
  · exact sameOrbit_of_same_eqTypedCount a b a' b'

/-- Every structural label is a coarsening of the equinumerosity-typed count, and the count is itself
structural, so it is the finest rung. Finiteness-free. -/
theorem eqTypedCount_is_finest_structural {Q : Type} (lab : Pt X → Pt X → Q)
    (hstruct : ∀ (e : Pt X ≃ Pt X), CrossStable e → ∀ p q, lab (e p) (e q) = lab p q)
    (a b a' b' : Pt X) (h : ∀ m, eqTypedCount a b m = eqTypedCount a' b' m) :
    lab a b = lab a' b' := by
  obtain ⟨e, he, rfl, rfl⟩ := (orbit_partition_is_eqTypedCount a b a' b').mpr h
  exact (hstruct e he a b).symm

/-! ## THE VERDICTS

PART 1: the equinumerosity-typed count is defined without finiteness, and the finite count is its special case.

`Equinumerous` groups coordinates by the existence of a bijection between their fibres, not by a cardinal.
`equinumerous_refl`, `_symm`, `_trans` make it an equivalence with no finiteness anywhere.
`eqTypedCount` counts, for each coordinate type, how many differing coordinates share it. THE COUNTING IS OVER
COORDINATES, which are finite because the arity is; nothing counts values, which is where the old definition
needed `Fintype`.

`eqTypedCount_eq_typedCount_of_finite` shows the reduction: with finite fibres, equinumerosity is equality of
cardinality, so the two objects coincide. The finite typed count is a reading of this one, not a rival.

PART 2: THE LIFT WORKS, and the step that looked like it needed finiteness had a replacement.

THE INVARIANCE MECHANISM, which was the doubtful half. The finite proof read the fibre SIZE off the graph by
COUNTING a line, and that count is irreducibly finite. The replacement reads the same line as a SET and
transports it, which yields a BIJECTION where the old proof yielded an equal number. `lineSet` characterizes
the line graph-theoretically, `lineSet_eq` identifies it with the coordinate line by `common_neighbours`, which
is a pointwise equivalence and carries no finiteness, `lineEquiv` identifies the line with the fibre minus one
point, `mem_lineSet_map` transports it along a cross-stable bijection, and `equiv_of_punctured` puts the removed
point back on each side. `crossStable_equinumerous` is the result: a cross-stable bijection relates two
coordinates only if their fibres are EQUINUMEROUS, proved with no finiteness at all.

THE TRANSITIVITY, which was the easy half and stayed easy. `swapT` takes a bijection between two fibres as a
parameter and never mentions cardinality; the finite proof manufactured that bijection with
`Fintype.equivOfCardEq`, and here it comes straight from the equinumerosity hypothesis.
`eqTypedCount_swapT` and `sameOrbit_of_same_eqTypedCount` follow the finite argument line for line.

THE ASSEMBLY. `image_step_adjacent`, `image_step_mem` and `image_step_eq` carry the local mechanism to a whole
cell: each differing coordinate sends its first step across, the image is a first step of the image cell, and
the correspondence is injective. `eqTypedCount_crossStable_invariant` concludes, by injecting both ways rather
than exhibiting a bijection, that every cross-stable bijection preserves every equinumerosity-typed count at
arbitrary distance.

NO STEP GENUINELY NEEDED FINITENESS. The one that appeared to, the link count, needed only that a line be
transported, and a set transports as well as a number counts.

A NOTE ON THE AUDIT, since a false lift was the thing to watch. Several results carry `Classical.choice`. In
every case it extracts a bijection that the hypothesis ASSERTS to exist, or decides a proposition for a filter
over the coordinate index. Nowhere does it manufacture a bijection out of finite structure, which is what
`Fintype.equivOfCardEq` did in the finite proof and what a false lift would have hidden. The distinction is
visible in the statements: no theorem below mentions `Fintype` except the one that names it to compare.

PART 3: THE PRESENTATION CHOICE DISSOLVES.

`orbit_partition_is_eqTypedCount` is both inclusions over ANY product carrier, with no `Fintype` in the
statement or in either proof. So there is ONE object, and it is at once

  GENERAL, since it needs no finiteness and so covers every carrier the framework admits;
  CONCRETE, since it says exactly what the rungs are, namely differing coordinates grouped by fibre type; and
  REDUCIBLE, since on finite fibres it IS the cardinal typed count.

The abstract and concrete forms were not two readings of one fact; they were one fact and a finiteness-bound
approximation of it. The choice was an artefact of stating the concrete form with cardinals.

PART 4: the resolved structure clause.

THE STRUCTURE CLAUSE SHOULD SAY: the invariant readings of the cross are exactly the coarsenings of the
EQUINUMEROSITY-TYPED DIFFERING COUNT. That is concrete and carries no finiteness hypothesis, so it replaces
both candidates rather than choosing between them. `eqTypedCount_is_finest_structural` is the tower statement:
every structural label is a coarsening of it and it is itself structural, so it is the finest rung.

The cardinal typed count keeps a place as the finite reading, cited by
`eqTypedCount_eq_typedCount_of_finite`, and the reachability form remains available as the definition of the
orbit partition. Neither is primary any more; both are corollaries.

GRADUATION SHELF. The classification group graduates as before, at `Model/NaryAssemblage`, with this file
replacing the cardinal-typed clause: the equinumerosity vocabulary and `eqTypedCount` first, then the lifted
mechanism, then the two inclusions, then the finite reduction as a corollary. The one dependency worth noting
is that `eqTypedCount` is `noncomputable` because its filter is classically decided; canonical `nary` is
already noncomputable, so this adds nothing new to the module.

VOCABULARY NOTE FOR THE SPEC, NOT FOR ANY THEOREM NAME. Equinumerosity classes of coordinates are the alphabet
TYPES; the equinumerosity-typed count is the class scheme of a product of Hamming schemes grouped by alphabet
type rather than alphabet size, which is the infinite-friendly form of the same object. Those names belong in a
spec entry citing the known setting, and nothing above is claimed as new relative to them.

WHAT REMAINS OPEN

1. The coordinate index is `Fin n`, so the ARITY is still finite. Only the fibres were lifted. An infinite
   arity would change the differing set from a `Finset` to something else and is not considered.
2. Nothing here is graduated; this readies the graduable form.
-/


/-! ### The abstract reading: orbits and structural labels -/


/-- Two cross cells share an orbit when a cross-stable bijection carries one to the other. -/
def Reachable (a b a' b' : Pt X) : Prop :=
  ∃ e : Pt X ≃ Pt X, CrossStable e ∧ e a = a' ∧ e b = b'

def Structural {Q : Type} (q : Pt X → Pt X → Q) : Prop :=
  ∀ e : Pt X ≃ Pt X, CrossStable e → ∀ a b, IsCross a b → q (e a) (e b) = q a b

def Bound {Q : Type} (q : Pt X → Pt X → Q) (imp : Pt X → Pt X → Option Bool) : Prop :=
  ∀ a b a' b', IsCross a b → IsCross a' b' → q a b = q a' b' → imp a b = imp a' b'

omit [∀ i, DecidableEq (X i)] in
/-- **The orbit partition classifies the structural readings.** A reading is invariant under the group exactly
when it is constant on orbits, so the structural readings are precisely the coarsenings of the orbit partition
and the orbit partition is the finest of them. -/
theorem structural_iff_orbit_constant {Q : Type} (q : Pt X → Pt X → Q) :
    Structural q ↔ ∀ a b a' b', IsCross a b → Reachable a b a' b' → q a' b' = q a b := by
  constructor
  · rintro hs a b a' b' hab ⟨e, he, h1, h2⟩
    rw [← h1, ← h2]
    exact hs e he a b hab
  · intro ho e he a b hab
    exact ho a b (e a) (e b) hab ⟨e, he, rfl, rfl⟩

omit [∀ i, DecidableEq (X i)] in
/-- Anything computed from a reading is bound at it, so every reading is inhabited by imports. -/
theorem bound_of_factors {Q : Type} (q : Pt X → Pt X → Q) (g : Q → Option Bool) :
    Bound q (fun a b => g (q a b)) := by
  intro a b a' b' _ _ hq
  show g (q a b) = g (q a' b')
  rw [hq]

/-- **No reading is fixed either.** At any reading whatever, a bound import and an arbitrary one both assemble
over the same factors and agree on every region cell, so the structure does not narrow the freedom at any
rung. -/
theorem no_reading_is_fixed {Q : Type} (c : ∀ i, X i → X i → Option Bool)
    (q : Pt X → Pt X → Q) (g : Q → Option Bool) (imp : Pt X → Pt X → Option Bool) :
    isAssemblageN (nary c (fun a b => g (q a b)))
      ∧ isAssemblageN (nary c imp)
      ∧ ∀ (a b : Pt X) (i : Fin n), differsInOne a b i →
          nary c (fun a b => g (q a b)) a b = nary c imp a b := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun _ _ _ _ _ hd hd' ha hb => nary_region_independent _ _ hd hd' ha hb
  · exact fun _ _ _ _ _ hd hd' ha hb => nary_region_independent _ _ hd hd' ha hb
  · intro a b i h
    rw [nary_apply_differ c _ h, nary_apply_differ c imp h]


/-! ### THE STRUCTURE OF EXTERNAL RELATIONS: four properties of the import -/


/-- **(a) EXTERNALITY.** No change of factors reaches the cross. Replacing every factor by anything at all
leaves every cross cell where it was, so the external relation is underivable from the factors. -/
theorem externality (c c' : ∀ i, X i → X i → Option Bool) (imp : Pt X → Pt X → Option Bool)
    {a b : Pt X} (h : IsCross a b) : nary c imp a b = nary c' imp a b := by
  rw [nary_apply_imp c imp h, nary_apply_imp c' imp h]

/-- **(b) IRREDUCIBILITY.** An operation on the whole does reach the cross, and it writes there what no factor
operation could: a fill on the composite overwrites an absent cross cell, while by (a) every factor-side fill
leaves it untouched. So the external relation is reached only from the whole. -/
theorem irreducibility (c : ∀ i, X i → X i → Option Bool) (imp : Pt X → Pt X → Option Bool)
    (s : Pt X → Nat) (si : ∀ i, X i → Nat) {a b : Pt X} (h : IsCross a b)
    (habs : imp a b = none) :
    totalization s (nary c imp) a b = some (decide (s b ≤ s a))
      ∧ nary (fun i => totalization (si i) (c i)) imp a b = nary c imp a b :=
  ⟨composite_fill_overwrites_absent_cross c imp s h habs, externality _ c imp h⟩

/-- **(c) FREEDOM.** Any cross content whatever is realized: for an arbitrary target the assembly over it as
import agrees with it on every cross cell, over any factors. The framework fixes no value. -/
theorem freedom (c : ∀ i, X i → X i → Option Bool) (V : Pt X → Pt X → Option Bool)
    {a b : Pt X} (h : IsCross a b) : nary c V a b = V a b :=
  nary_apply_imp c V h

/-! ### (d) STRUCTURE: the invariant readings of the cross

A READING of the cross is a label on its cells; an import is BOUND at a reading when its verdict is a function
of the label. A reading is STRUCTURAL when the cross-stable bijections cannot move a cell out of its block.
These are the definitions the tower lineage settled on, restated here so the bundle is self-contained. -/

/-- **THE DISCIPLINE CHECK: no import is selected.** The bundle above is a property of an arbitrary `imp` over
arbitrary factors, and every clause quantifies over the objects it discusses. Concretely: two arbitrary imports
satisfy it alike, so nothing in it distinguishes one from another. -/
theorem bundle_selects_no_import (c : ∀ i, X i → X i → Option Bool)
    (imp imp' : Pt X → Pt X → Option Bool) :
    (∀ (c' : ∀ i, X i → X i → Option Bool) (a b : Pt X), IsCross a b →
        nary c imp a b = nary c' imp a b)
      ∧ (∀ (c' : ∀ i, X i → X i → Option Bool) (a b : Pt X), IsCross a b →
        nary c imp' a b = nary c' imp' a b) :=
  ⟨fun c' _ _ h => externality c c' imp h, fun c' _ _ h => externality c c' imp' h⟩

/-! ## Part 2: the seam

The external relation is what the framework leaves free. The orbit partition is what the framework's symmetries
fix. The seam theorem is that the second classifies the first. -/


/-! ### The link count: fibre size read off the graph, on finite fibres -/

omit [∀ i, DecidableEq (X i)] in
theorem crossStable_adjacent (e : Pt X ≃ Pt X) (he : CrossStable e) (a b : Pt X) :
    Adjacent a b ↔ Adjacent (e a) (e b) := (crossStable_iff_adjacent e).mp he a b

/-- Differing in exactly one coordinate is decidable, since the arity is finite and the fibres have decidable
equality. -/
instance decDiffersInOne (a b : Pt X) (i : Fin n) : Decidable (differsInOne a b i) := by
  unfold differsInOne; infer_instance

instance decAdjacent (a b : Pt X) : Decidable (Adjacent a b) := by
  unfold Adjacent; infer_instance




section FiniteLink

variable [∀ i, Fintype (X i)]


/-- A differing coordinate has at least two values in its fibre, so the link count recovers the fibre size. -/
theorem two_le_card_of_mem_diffSet {a b : Pt X} {i : Fin n} (h : i ∈ diffSet a b) :
    2 ≤ Fintype.card (X i) := by
  have hne : a i ≠ b i := mem_diffSet.mp h
  have h1 : ({a i, b i} : Finset (X i)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  calc 2 = ({a i, b i} : Finset (X i)).card := h1.symm
    _ ≤ Fintype.card (X i) := Finset.card_le_univ _

/-- The points differing from `a` exactly at coordinate `i`: the line through `a` in that direction, minus `a`
itself. -/
def lineAt (a : Pt X) (i : Fin n) : Finset (Pt X) :=
  Finset.univ.filter (fun d : Pt X => differsInOne a d i)

/-- **The line has one point per other fibre value.** Sending a point of the line to its value at `i` is a
bijection onto the values other than `a i`. -/
theorem lineAt_card (a : Pt X) (i : Fin n) :
    (lineAt a i).card = Fintype.card (X i) - 1 := by
  have hbij : (lineAt a i).card = (Finset.univ.filter (fun v : X i => v ≠ a i)).card := by
    refine Finset.card_bij (fun d _ => d i) ?_ ?_ ?_
    · intro d hd
      rw [lineAt, Finset.mem_filter] at hd
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun hc => hd.2.1 hc.symm⟩
    · intro d1 h1 d2 h2 h
      rw [lineAt, Finset.mem_filter] at h1 h2
      funext j
      by_cases hj : j = i
      · subst hj; exact h
      · rw [← h1.2.2 j hj, h2.2.2 j hj]
    · intro v hv
      rw [Finset.mem_filter] at hv
      refine ⟨Function.update a i v, ?_, ?_⟩
      · rw [lineAt, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, fun j hj => ?_⟩
        · rw [Function.update_self]; exact fun hc => hv.2 hc.symm
        · rw [Function.update_of_ne hj]
      · rw [Function.update_self]
  rw [hbij]
  have : (Finset.univ.filter (fun v : X i => v ≠ a i)).card
      = Fintype.card (X i) - (Finset.univ.filter (fun v : X i => v = a i)).card := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (X i))) (p := fun v => v = a i)
    have heq : (Finset.univ.filter (fun v : X i => ¬ v = a i)).card
        = (Finset.univ.filter (fun v : X i => v ≠ a i)).card := rfl
    rw [Finset.card_univ] at hsum
    omega
  rw [this, Finset.filter_eq' Finset.univ (a i)]
  simp

/-- The number of vertices adjacent to both members of a pair. -/
def linkCount (a c : Pt X) : ℕ :=
  (Finset.univ.filter (fun d : Pt X => Adjacent a d ∧ Adjacent c d)).card

/-- **The link count is a cross-stable invariant.** Adjacency transports both ways and the bijection is
injective, so the two filtered sets correspond. Carrier-general. -/
theorem linkCount_invariant (e : Pt X ≃ Pt X) (he : CrossStable e) (a c : Pt X) :
    linkCount (e a) (e c) = linkCount a c := by
  have hset : (Finset.univ.filter (fun d : Pt X => Adjacent (e a) d ∧ Adjacent (e c) d))
      = (Finset.univ.filter (fun d : Pt X => Adjacent a d ∧ Adjacent c d)).image e := by
    ext d
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, h1, h2⟩
      refine ⟨e.symm d, ?_, Equiv.apply_symm_apply e d⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [crossStable_adjacent e he, Equiv.apply_symm_apply]; exact h1
      · rw [crossStable_adjacent e he, Equiv.apply_symm_apply]; exact h2
    · rintro ⟨d0, hd0, rfl⟩
      rw [Finset.mem_filter] at hd0
      exact ⟨Finset.mem_univ _, (crossStable_adjacent e he a d0).mp hd0.2.1,
        (crossStable_adjacent e he c d0).mp hd0.2.2⟩
  rw [linkCount, linkCount, hset, Finset.card_image_of_injective _ e.injective]

/-- **THE LOCAL READING.** The link count of an adjacent pair is two less than the size of the fibre they
differ in. So the graph structure alone sees fibre size, at every adjacent pair. Carrier-general. -/
theorem linkCount_eq (a c : Pt X) (i : Fin n) (hac : differsInOne a c i) :
    linkCount a c = Fintype.card (X i) - 2 := by
  have hset : (Finset.univ.filter (fun d : Pt X => Adjacent a d ∧ Adjacent c d))
      = (lineAt a i).erase c := by
    ext d
    rw [Finset.mem_filter, Finset.mem_erase, lineAt, Finset.mem_filter]
    constructor
    · intro hd
      have := (common_neighbours a c i hac d).mp hd.2
      exact ⟨this.2, Finset.mem_univ _, this.1⟩
    · intro hd
      exact ⟨Finset.mem_univ _, (common_neighbours a c i hac d).mpr ⟨hd.2.2, hd.1⟩⟩
  have hmem : c ∈ lineAt a i := by
    rw [lineAt, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hac⟩
  rw [linkCount, hset, Finset.card_erase_of_mem hmem, lineAt_card]
  omega

/-- How many of the differing coordinates have a fibre of a given size. -/
def typedCount (a b : Pt X) (q : ℕ) : ℕ :=
  ((diffSet a b).filter (fun i => Fintype.card (X i) = q)).card


end FiniteLink



/-! ### The strict separation: the plain count fails on unequal fibres -/


def sz : Fin 3 → ℕ := ![2, 2, 3]

theorem sz_two_le : ∀ i, 2 ≤ sz i := by decide

/-- A carrier with two fibres of one size and one of another. -/
abbrev Het := ∀ i : Fin 3, Fin (sz i)

def zeroP : Het := fun i => ⟨0, by have := sz_two_le i; omega⟩

/-- The point that is one on a chosen set of coordinates and zero elsewhere. -/
def oneOn (S : Finset (Fin 3)) : Het :=
  fun i => if i ∈ S then ⟨1, by have := sz_two_le i; omega⟩ else ⟨0, by have := sz_two_le i; omega⟩

theorem diffSet_oneOn (S : Finset (Fin 3)) :
    diffSet (X := fun i => Fin (sz i)) zeroP (oneOn S) = S := by
  ext i
  rw [mem_diffSet]
  by_cases hi : i ∈ S
  · simp only [hi, iff_true]
    show zeroP i ≠ (oneOn S) i
    rw [oneOn, if_pos hi]
    intro hc
    exact absurd (congrArg Fin.val hc) (by simp [zeroP])
  · simp only [hi, iff_false, not_not]
    show zeroP i = (oneOn S) i
    rw [oneOn, if_neg hi]
    rfl

theorem card_fibre (i : Fin 3) : Fintype.card (Fin (sz i)) = sz i := Fintype.card_fin _

/-- The two cells: both differ in exactly two coordinates, so both are cross and both have the same plain
differing count. -/
theorem both_cross :
    IsCross (X := fun i => Fin (sz i)) zeroP (oneOn {0, 1})
      ∧ IsCross (X := fun i => Fin (sz i)) zeroP (oneOn {0, 2})
      ∧ (diffSet (X := fun i => Fin (sz i)) zeroP (oneOn {0, 1})).card
          = (diffSet (X := fun i => Fin (sz i)) zeroP (oneOn {0, 2})).card := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, hi⟩
    rw [differsInOne_iff_diffSet, diffSet_oneOn] at hi
    have hc := congrArg Finset.card hi
    rw [Finset.card_singleton] at hc
    exact absurd hc (by decide)
  · rintro ⟨i, hi⟩
    rw [differsInOne_iff_diffSet, diffSet_oneOn] at hi
    have hc := congrArg Finset.card hi
    rw [Finset.card_singleton] at hc
    exact absurd hc (by decide)
  · rw [diffSet_oneOn, diffSet_oneOn]
    decide

/-- Two points differing from the base point only at coordinate zero coincide, because that fibre has just two
values. -/
theorem eq_of_differs_at_zero (u v : Het)
    (hu : differsInOne (X := fun i => Fin (sz i)) zeroP u 0)
    (hv : differsInOne (X := fun i => Fin (sz i)) zeroP v 0) : u = v := by
  funext j
  by_cases hj : j = 0
  · subst hj
    have hu0 : (u 0).val ≠ 0 := by
      intro hc
      exact hu.1 (Fin.val_injective (by rw [hc]; rfl))
    have hv0 : (v 0).val ≠ 0 := by
      intro hc
      exact hv.1 (Fin.val_injective (by rw [hc]; rfl))
    have hub : (u 0).val < 2 := (u 0).isLt
    have hvb : (v 0).val < 2 := (v 0).isLt
    exact Fin.val_injective (by omega)
  · rw [← hu.2 j hj, hv.2 j hj]

/-- **THE SEPARATION.** No cross-stable bijection relates the two cells. They have the same plain differing
count, so the orbit partition is STRICTLY finer than the differing count on this carrier, and the sandwich
`HowManyIsOrbit` left open is strict. -/
theorem no_crossStable_relates :
    ¬ ∃ e : Het ≃ Het, CrossStable (X := fun i => Fin (sz i)) e
        ∧ e zeroP = zeroP ∧ e (oneOn {0, 1}) = oneOn {0, 2} := by
  rintro ⟨e, he, ha, hb⟩
  have key : ∀ c : Het, differsInOne (X := fun i => Fin (sz i)) zeroP c 0 ∨
      differsInOne (X := fun i => Fin (sz i)) zeroP c 1 →
      Adjacent (X := fun i => Fin (sz i)) c (oneOn {0, 1}) →
      differsInOne (X := fun i => Fin (sz i)) zeroP (e c) 0 := by
    intro c hc hcb
    have hac : Adjacent (X := fun i => Fin (sz i)) zeroP c := by
      rcases hc with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have h1 : Adjacent (X := fun i => Fin (sz i)) zeroP (e c) := by
      have := (crossStable_adjacent e he zeroP c).mp hac
      rwa [ha] at this
    have h2 : Adjacent (X := fun i => Fin (sz i)) (e c) (oneOn {0, 2}) := by
      have := (crossStable_adjacent e he c (oneOn {0, 1})).mp hcb
      rwa [hb] at this
    obtain ⟨m, hm⟩ := h1
    obtain ⟨l, hl⟩ := h2
    -- the link count reads the fibre size and is preserved
    have hlink : Fintype.card (Fin (sz m)) - 2 = Fintype.card (Fin (sz 0)) - 2 ∨
        Fintype.card (Fin (sz m)) - 2 = Fintype.card (Fin (sz 1)) - 2 := by
      rcases hc with h | h
      · refine Or.inl ?_
        rw [← linkCount_eq zeroP (e c) m hm, ← linkCount_eq zeroP c 0 h]
        have := linkCount_invariant e he zeroP c
        rwa [ha] at this
      · refine Or.inr ?_
        rw [← linkCount_eq zeroP (e c) m hm, ← linkCount_eq zeroP c 1 h]
        have := linkCount_invariant e he zeroP c
        rwa [ha] at this
    have hszm : sz m ≤ 2 := by
      rw [Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at hlink
      have h0 : sz 0 = 2 := by decide
      have h1' : sz 1 = 2 := by decide
      have h2' : 2 ≤ sz m := sz_two_le m
      rcases hlink with h | h
      · rw [h0] at h; omega
      · rw [h1'] at h; omega
    have hm2 : m ≠ 2 := by
      intro hc2
      subst hc2
      exact absurd hszm (by decide)
    -- the triangle inclusion pins the coordinate
    have hsub := diffSet_subset_union (X := fun i => Fin (sz i)) zeroP (oneOn {0, 2}) (e c)
    rw [diffSet_oneOn, (differsInOne_iff_diffSet zeroP (e c) m).mp hm,
      (differsInOne_iff_diffSet (e c) (oneOn {0, 2}) l).mp hl] at hsub
    have h2mem : (2 : Fin 3) ∈ ({m} : Finset (Fin 3)) ∪ {l} := hsub (by decide)
    have h0mem : (0 : Fin 3) ∈ ({m} : Finset (Fin 3)) ∪ {l} := hsub (by decide)
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at h2mem h0mem
    have hl2 : l = 2 := by
      rcases h2mem with h | h
      · exact absurd h.symm hm2
      · exact h.symm
    have hm0 : m = 0 := by
      rcases h0mem with h | h
      · exact h.symm
      · rw [hl2] at h; exact absurd h (by decide)
    rw [hm0] at hm
    exact hm
  have hc0 : differsInOne (X := fun i => Fin (sz i)) zeroP (e (oneOn {0})) 0 :=
    key (oneOn {0}) (Or.inl (by decide)) ⟨1, by decide⟩
  have hc1 : differsInOne (X := fun i => Fin (sz i)) zeroP (e (oneOn {1})) 0 :=
    key (oneOn {1}) (Or.inr (by decide)) ⟨0, by decide⟩
  have := e.injective (eq_of_differs_at_zero _ _ hc0 hc1)
  exact absurd this (by decide)

/-! ## THE VERDICTS

PART 1: the typed count, and how much of its invariance is PROVED.

`typedCount` records, for each fibre size, how many of the differing coordinates have a fibre of that size. It
is cast-free: it reads `Fintype.card (X i)`, never a type equality. `plain_from_typed` shows it refines the
plain count, since summing it over the occurring sizes returns that count, and
`typed_eq_plain_of_homogeneous` shows the two coincide when there is one size, which is exactly why homogeneity
collapsed the sandwich. `typedCount_fibEquiv` gives invariance under the coordinatewise family, trivially,
since those maps fix the differing set outright.

THE SUBSTANTIVE HALF IS THE TYPING CONSTRAINT, and it is proved from cross-stability alone.
`common_neighbours` is the structural lemma: the vertices adjacent to both members of an adjacent pair are
exactly the rest of the line that pair spans, because anything differing from one endpoint elsewhere differs
from the other in two coordinates. `lineAt_card` counts a line, `linkCount_eq` therefore reads the FIBRE SIZE
off the graph at every adjacent pair, and `linkCount_invariant` shows that count is preserved by any
cross-stable bijection. Together, `crossStable_preserves_fibre_card`: a cross-stable bijection can carry a pair
differing at coordinate `i` to a pair differing at coordinate `j` ONLY IF the two fibres have the same size.
Carrier-general, and with no identification of the group, which `CrossStableGroup` left open and which is still
not needed.

NOT PROVED: invariance of the typed count at arbitrary distance. The argument is available and is sketched
here rather than formalized. Along a shortest chain from `a` to `b` each differing coordinate is used exactly
once; a cross-stable bijection carries shortest chains to shortest chains; and each step keeps its fibre size
by the typing constraint. So the multiset of fibre sizes over the differing set is preserved. Formalizing it
needs the chain machinery plus the bookkeeping that a shortest chain uses each coordinate once, and that is not
done in this file.

PART 2: TRANSITIVITY IS NOT PROVED, and the classification is NOT completed unconditionally.

This is the honest state. The reverse direction needs exchanges between DISTINCT coordinates whose fibres are
merely equinumerous rather than identical, and such an exchange must transport a value across a type
equivalence. In a dependent product that is a cast at every use, and every lemma about the resulting map has to
be proved through the cast. Nothing here attempts it. So `sameOrbit_iff_same_typed_count` is not established,
and the conjecture that the orbit partition IS the typed count remains a conjecture, now with one half of its
evidence proved.

PART 3: THE SANDWICH IS STRICT. This is settled, and it is the headline.

`both_cross` exhibits two cells on a carrier with fibre sizes two, two and three: one differing at the two
small coordinates, the other at one small and the large one. Both are cross and both have plain differing count
two. `no_crossStable_relates` proves NO cross-stable bijection carries the first to the second.

The proof uses only what is above. Either witness neighbour must map to a point adjacent to the base and to the
target, so its coordinate is pinned by the triangle inclusion; the link count forces that coordinate to have a
size-two fibre, which rules out the large one; the two remaining possibilities collapse because the pinned
coordinate has only two values, so both witnesses would have the same image; and the bijection is injective.

So on a heterogeneous carrier the orbit partition is STRICTLY finer than the differing count, and
`HowManyIsOrbit`'s homogeneity hypothesis was NECESSARY, not an artefact of its proof. That was the open
question and it now has an answer.

PART 4: what this licenses, and the status change it forces.

The external-relation bundle's STRUCTURE clause must STAY in its abstract form, the coarsenings of the orbit
partition. But the reason has CHANGED, and the change matters. Before this build the abstract form was kept
because the heterogeneous case was OPEN. Now the concrete plain-count form is PROVABLY FALSE over arbitrary
product carriers, by `no_crossStable_relates`. The abstract form is not a hedge against ignorance; it is the
only correct unconditional statement.

The concrete form remains available with its hypothesis: on a homogeneous carrier the structural readings are
the coarsenings of the differing count, by `HowManyIsOrbit`. What is not yet available is a concrete
unconditional form, since that would be the typed count and Part 2 is open.

VOCABULARY NOTE FOR THE SPEC, NOT FOR ANY THEOREM NAME. The adjacency structure here is a Hamming graph with
unequal alphabet sizes; `common_neighbours` is the standard fact that its maximal cliques are the lines;
`crossStable_preserves_fibre_card` is the standard consequence that an automorphism permutes the coordinate
directions only within equal-alphabet classes; and the conjectured orbit partition is the class scheme of a
product of Hamming schemes with distinct alphabet sizes. Those names belong in a spec entry citing the known
setting, and nothing above is claimed as new relative to them.

WHAT REMAINS OPEN

1. Transitivity, hence the identification of the orbit partition with the typed count. Stated in Part 2.
2. Typed-count invariance at arbitrary distance. Sketched in Part 1, not formalized.
3. The separation is exhibited at one carrier. Whether every pair of differing sets with equal plain count and
   unequal typed count is separated follows from 1 and 2 and is not proved directly.
4. Nothing here is graduated. -/


/-! ### The closed forms for the two natural labels -/


/-- **The which-differ label has `2 ^ n - n` possible values.** Its values are the subsets of the coordinate
set whose size is not one, since a size-one set is a region cell and not a cross cell. Carrier-general in `n`,
no evaluation. -/
theorem whichDiffer_value_count (m : ℕ) :
    (Finset.univ.filter (fun S : Finset (Fin m) => S.card ≠ 1)).card = 2 ^ m - m := by
  have hone : (Finset.univ.filter (fun S : Finset (Fin m) => S.card = 1)).card = m := by
    have : (Finset.univ.filter (fun S : Finset (Fin m) => S.card = 1))
        = Finset.powersetCard 1 (Finset.univ : Finset (Fin m)) := by
      ext S
      simp [Finset.mem_powersetCard]
    rw [this, Finset.card_powersetCard]
    simp
  have htot : (Finset.univ : Finset (Finset (Fin m))).card = 2 ^ m := by
    simp [Finset.card_univ, Fintype.card_finset]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Finset (Fin m)))) (p := fun S => S.card = 1)
  rw [hone, htot] at hsum
  have hne : (Finset.univ.filter (fun S : Finset (Fin m) => ¬ S.card = 1)).card
      = (Finset.univ.filter (fun S : Finset (Fin m) => S.card ≠ 1)).card := rfl
  omega

/-- **The how-many label has `n` possible values.** Its values are the admissible differing counts: zero, and
everything from two to `n`. Carrier-general in `n`, no evaluation. -/
theorem howMany_value_count (m : ℕ) (hm : 0 < m) :
    ((Finset.range (m + 1)).filter (fun k => k ≠ 1)).card = m := by
  have hone : ((Finset.range (m + 1)).filter (fun k => k = 1)).card = 1 := by
    have : (Finset.range (m + 1)).filter (fun k => k = 1) = {1} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro rfl; exact ⟨by omega, rfl⟩
    rw [this]
    simp
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Finset.range (m + 1)) (p := fun k => k = 1)
  rw [hone, Finset.card_range] at hsum
  have hne : ((Finset.range (m + 1)).filter (fun k => ¬ k = 1)).card
      = ((Finset.range (m + 1)).filter (fun k => k ≠ 1)).card := rfl
  omega

/-! ## The label values are realized

The counts above are counts of POSSIBLE values. They are the block counts only if every value occurs, which
needs a second element in each fibre. -/

/-! ### The finite readings, as corollaries

Every result above is finiteness-free. What follows are its readings when the fibres are finite, which is where
the classification was first proved. -/

section FiniteReadings

variable [∀ i, Fintype (X i)]

/-- The equinumerosity count at a coordinate is the cardinal count at that coordinate's fibre size. -/
theorem eqTypedCount_eq_typedCount (a b : Pt X) (j : Fin n) :
    eqTypedCount a b j = typedCount a b (Fintype.card (X j)) :=
  eqTypedCount_eq_typedCount_of_finite a b j

/-- **The cardinal typed count classifies exactly as the equinumerosity count does**, on finite fibres. The
two agree at every occurring fibre size, and at a size no fibre has, both counts are zero. -/
theorem typedCount_iff_eqTypedCount (a b a' b' : Pt X) :
    (∀ r, typedCount a b r = typedCount a' b' r) ↔ ∀ j, eqTypedCount a b j = eqTypedCount a' b' j := by
  constructor
  · intro h j
    rw [eqTypedCount_eq_typedCount, eqTypedCount_eq_typedCount]
    exact h _
  · intro h r
    by_cases hr : ∃ j : Fin n, Fintype.card (X j) = r
    · obtain ⟨j, hj⟩ := hr
      have := h j
      rw [eqTypedCount_eq_typedCount, eqTypedCount_eq_typedCount, hj] at this
      exact this
    · simp only [not_exists] at hr
      have e1 : typedCount a b r = 0 := by
        rw [typedCount, Finset.filter_false_of_mem, Finset.card_empty]
        exact fun i _ => hr i
      have e2 : typedCount a' b' r = 0 := by
        rw [typedCount, Finset.filter_false_of_mem, Finset.card_empty]
        exact fun i _ => hr i
      rw [e1, e2]

/-- **The finite form of the classification**, a corollary of the general one. -/
theorem orbit_partition_is_typedCount (a b a' b' : Pt X) :
    SameOrbit a b a' b' ↔ ∀ r, typedCount a b r = typedCount a' b' r := by
  rw [orbit_partition_is_eqTypedCount, ← typedCount_iff_eqTypedCount]

/-- On a homogeneous carrier the cardinal count collapses to the plain differing count. -/
theorem typedCount_eq_card_of_homogeneous (r : ℕ) (hr : ∀ i, Fintype.card (X i) = r) (a b : Pt X) :
    typedCount a b r = (diffSet a b).card := by
  rw [typedCount, Finset.filter_true_of_mem]
  intro i _
  exact hr i

/-- **The homogeneous form of the classification**, a corollary in turn: with one fibre size, two cells share
an orbit exactly when they differ in the same number of coordinates. -/
theorem orbit_partition_is_diffCard_of_homogeneous (r : ℕ) (hr : ∀ i, Fintype.card (X i) = r)
    (a b a' b' : Pt X) :
    SameOrbit a b a' b' ↔ (diffSet a b).card = (diffSet a' b').card := by
  rw [orbit_partition_is_typedCount]
  constructor
  · intro h
    rw [← typedCount_eq_card_of_homogeneous r hr, ← typedCount_eq_card_of_homogeneous r hr]
    exact h r
  · intro h s
    by_cases hs : s = r
    · subst hs
      rw [typedCount_eq_card_of_homogeneous s hr, typedCount_eq_card_of_homogeneous s hr]
      exact h
    · have e1 : typedCount a b s = 0 := by
        rw [typedCount, Finset.filter_false_of_mem, Finset.card_empty]
        intro i _
        rw [hr i]; exact fun hc => hs hc.symm
      have e2 : typedCount a' b' s = 0 := by
        rw [typedCount, Finset.filter_false_of_mem, Finset.card_empty]
        intro i _
        rw [hr i]; exact fun hc => hs hc.symm
      rw [e1, e2]

end FiniteReadings


/-! ## Deconstruction, the free locus, and region coverage

Three groups. What makes a classification reproducible from parts and a filling; where a value is undetermined
by everything else; and when the two extreme fillings give wholes no relabelling can identify.

BOUNDS, recorded with the results. The open-cell equivalence is the LOCAL sense, with the parts held: over
varying parts it fails, and `a_shared_part_cell_blocks_openness` says why. It is also not licence, since
admissibility can constrain cross cells jointly. The two region-coverage laws are SUFFICIENT and not
necessary: `a_part_exchanging_permutation_collapses_the_tops` is a further route to collapse, and no converse
from bare verdict-coverage is proved. Their hypotheses are unequal: the affirm case allows an arbitrary
carrier map, the deny case needs an onto one. -/

/-- The parts SEPARATE when some point has two single-move neighbours whose verdicts differ. -/
def FactorsSeparate (c : ∀ i, X i → X i → Option Bool) : Prop :=
  ∃ (a b q : Pt X) (i j : Fin n), differsInOne a q i ∧ differsInOne b q j ∧
    c i (a i) (q i) ≠ c j (b j) (q j)

/-- **SEPARATING PARTS DEFEAT EVERY FILLING.** Two rows are told apart at a single-move cell, which no filling reaches, so no filling collapses the whole. -/
theorem separating_factors_defeat_every_import (c : ∀ i, X i → X i → Option Bool)
    (h : FactorsSeparate c) (imp : Pt X → Pt X → Option Bool) : NonDegenerate (nary c imp) := by
  obtain ⟨a, b, q, i, j, ha, hb, hne⟩ := h
  refine ⟨a, b, fun hEq => hne ?_⟩
  have hq := congrFun hEq q
  rwa [nary_apply_differ c imp ha, nary_apply_differ c imp hb] at hq

/-- **NO FILLING RESCUES A GRAIN VIOLATION.** A classification breaking the region grain is reproduced by no parts and no filling. The basis of deconstruction: a filling lives at cross cells, a grain violation at a single-move cell, and the two never meet. -/
theorem no_filling_rescues_a_grain_violation (A : Pt X → Pt X → Option Bool)
    (h : ¬ isAssemblageN A) (c : ∀ i, X i → X i → Option Bool)
    (imp : Pt X → Pt X → Option Bool) : nary c imp ≠ A := by
  intro hEq
  exact h (hEq ▸ (fun _ _ _ _ _ hd hd' ha hb => nary_region_independent c imp hd hd' ha hb))

/-- A cell is OPEN, given the parts, when two wholes over those parts agree at every other cell and differ there. -/
def OpenGivenParts (c : ∀ i, X i → X i → Option Bool) (a b : Pt X) : Prop :=
  ∃ imp imp' : Pt X → Pt X → Option Bool,
    nary c imp a b ≠ nary c imp' a b ∧
      ∀ p q : Pt X, (p, q) ≠ (a, b) → nary c imp p q = nary c imp' p q

/-- **AN OPEN CELL IS A CROSS CELL.** Where a coordinate moved, the value is the part's verdict and no filling reaches it. -/
theorem open_implies_cross (c : ∀ i, X i → X i → Option Bool) {a b : Pt X}
    (h : OpenGivenParts c a b) : IsCross a b := by
  rintro ⟨i, hi⟩
  obtain ⟨imp, imp', hne, -⟩ := h
  exact hne (by rw [nary_apply_differ c imp hi, nary_apply_differ c imp' hi])

open scoped Classical in
/-- **AND A CROSS CELL IS OPEN.** The empty filling against the filling that speaks at that one cell. -/
theorem cross_implies_open (c : ∀ i, X i → X i → Option Bool) {a b : Pt X}
    (h : IsCross a b) : OpenGivenParts c a b := by
  refine ⟨fun _ _ => none, fun p q => if (p, q) = (a, b) then some true else none, ?_, ?_⟩
  · rw [nary_apply_imp c _ h, nary_apply_imp c _ h]; simp
  · intro p q hpq
    by_cases hex : ∃ i, differsInOne p q i
    · obtain ⟨i, hi⟩ := hex
      rw [nary_apply_differ c _ hi, nary_apply_differ c _ hi]
    · rw [nary_apply_imp c _ hex, nary_apply_imp c _ hex]; simp [hpq]

/-- **THE OPEN CELLS ARE EXACTLY THE CROSS CELLS.** With the parts held, the cross region is precisely where a value is undetermined by everything else. Local sense: undetermined by the rest, not licence to take any value jointly. -/
theorem the_open_cells_are_exactly_the_cross (c : ∀ i, X i → X i → Option Bool) (a b : Pt X) :
    OpenGivenParts c a b ↔ IsCross a b :=
  ⟨open_implies_cross c, cross_implies_open c⟩

/-- **A SECOND CELL SHARING A PART'S CELL BLOCKS OPENNESS OVER VARYING PARTS.** Any change to that part shows at both, so the two cannot differ at one cell alone. This is why the equivalence above holds only with the parts held. -/
theorem a_shared_part_cell_blocks_openness (c c' : ∀ i, X i → X i → Option Bool)
    (imp : Pt X → Pt X → Option Bool) {a b p q : Pt X} {i : Fin n}
    (hab : differsInOne a b i) (hpq : differsInOne p q i)
    (h1 : p i = a i) (h2 : q i = b i) (hne : nary c imp a b ≠ nary c' imp a b) :
    nary c imp p q ≠ nary c' imp p q := by
  rw [nary_apply_differ c imp hpq, nary_apply_differ c' imp hpq, h1, h2]
  rw [nary_apply_differ c imp hab, nary_apply_differ c' imp hab] at hne
  exact hne

omit [∀ i, DecidableEq (X i)] in
/-- The grain forces agreement between two points sharing a coordinate value. -/
theorem rows_agree_when_a_coordinate_is_shared {V : Type} (g : Pt X → V)
    (h : isAssemblageN (fun a _ : Pt X => g a)) {a a' : Pt X} (i : Fin n)
    (hi : a i = a' i) (t : X i) (ht : a i ≠ t) : g a = g a' := by
  have hd : differsInOne a (Function.update a i t) i := by
    refine ⟨?_, fun k hk => ?_⟩
    · rw [Function.update_self]; exact ht
    · exact (Function.update_of_ne hk t a).symm
  have hd' : differsInOne a' (Function.update a' i t) i := by
    refine ⟨?_, fun k hk => ?_⟩
    · rw [Function.update_self, ← hi]; exact ht
    · exact (Function.update_of_ne hk t a').symm
  exact h a _ a' _ i hd hd' hi (by rw [Function.update_self, Function.update_self])

/-- The path from one point to another, switching coordinates over one at a time. -/
def coordPath (a a' : Pt X) (m : ℕ) : Pt X := fun k => if k.val < m then a' k else a k

omit [∀ i, DecidableEq (X i)] in
/-- The path starts where it should. -/
theorem coordPath_zero (a a' : Pt X) : coordPath a a' 0 = a := by
  funext k; simp [coordPath]

omit [∀ i, DecidableEq (X i)] in
/-- And ends where it should. -/
theorem coordPath_full (a a' : Pt X) : coordPath a a' n = a' := by
  funext k; simp [coordPath, k.isLt]

omit [∀ i, DecidableEq (X i)] in
/-- Consecutive points of the path agree at every coordinate but one. -/
theorem coordPath_agree (a a' : Pt X) (m : ℕ) {j : Fin n} (hj : j.val ≠ m) :
    coordPath a a' m j = coordPath a a' (m + 1) j := by
  simp only [coordPath]
  by_cases h : j.val < m
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- So the grain carries the value along each step. -/
theorem coordPath_step {V : Type} (g : Pt X → V) (h : isAssemblageN (fun a _ : Pt X => g a))
    (hn : 2 ≤ n) (hfib : ∀ i : Fin n, ∃ s t : X i, s ≠ t) (a a' : Pt X) (m : ℕ) :
    g (coordPath a a' m) = g (coordPath a a' (m + 1)) := by
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j.val ≠ m := by
    rcases eq_or_ne m 0 with h0 | h0
    · exact ⟨⟨1, by omega⟩, by simp [h0]⟩
    · exact ⟨⟨0, by omega⟩, Ne.symm h0⟩
  obtain ⟨s, t, hst⟩ := hfib j
  by_cases hv : coordPath a a' m j = s
  · exact rows_agree_when_a_coordinate_is_shared g h j (coordPath_agree a a' m hj) t (by rw [hv]; exact hst)
  · exact rows_agree_when_a_coordinate_is_shared g h j (coordPath_agree a a' m hj) s hv

/-- And hence along the whole path. -/
theorem coordPath_const {V : Type} (g : Pt X → V) (h : isAssemblageN (fun a _ : Pt X => g a))
    (hn : 2 ≤ n) (hfib : ∀ i : Fin n, ∃ s t : X i, s ≠ t) (a a' : Pt X) :
    ∀ m, g (coordPath a a' m) = g a := by
  intro m
  induction m with
  | zero => rw [coordPath_zero]
  | succ k ih => rw [← coordPath_step g h hn hfib a a' k]; exact ih

/-- **A CONSTANT-ROW CLASSIFICATION IS NEVER AN ASSEMBLY.** On any product carrier with two or more coordinates and non-trivial fibres, reading only the first argument respects no grain unless it carries no distinction at all. At an arbitrary value space. -/
theorem constant_row_registers_are_bases (hn : 2 ≤ n) (hfib : ∀ i : Fin n, ∃ s t : X i, s ≠ t)
    {V : Type} (g : Pt X → V) (hg : ∃ a a' : Pt X, g a ≠ g a') :
    ¬ isAssemblageN (fun a _ : Pt X => g a) := by
  intro h
  obtain ⟨a, a', hne⟩ := hg
  have hc := coordPath_const g h hn hfib a a' n
  rw [coordPath_full] at hc
  exact hne hc.symm

/-- **AND THE SHAPE SURVIVES EVERY RELABELLING.** Reading a constant-row classification through a relabelling gives another, so these resist under every presentation. -/
theorem the_family_survives_every_relabelling (hn : 2 ≤ n)
    (hfib : ∀ i : Fin n, ∃ s t : X i, s ≠ t) {V : Type} (g : Pt X → V) (f : Pt X → Pt X)
    (hg : ∃ a a' : Pt X, g (f a) ≠ g (f a')) :
    ¬ isAssemblageN (fun a _ : Pt X => g (f a)) :=
  constant_row_registers_are_bases hn hfib (fun a => g (f a)) hg

omit [∀ i, DecidableEq (X i)] in
/-- Such a classification is a genuine object: its rows differ. -/
theorem constant_row_registers_are_nondegenerate {V : Type} (g : Pt X → V)
    (hg : ∃ a a' : Pt X, g a ≠ g a') : NonDegenerate (fun a _ : Pt X => g a) := by
  obtain ⟨a, a', hne⟩ := hg
  exact ⟨a, a', fun hEq => hne (congrFun hEq a)⟩

/-- **THE PARTS HAVE A KERNEL.** Rules agreeing away from their diagonals give the same whole: a rule's diagonal is never read. -/
theorem parts_agreeing_off_the_diagonal_give_the_same_whole
    (c c' : ∀ i, X i → X i → Option Bool) (imp : Pt X → Pt X → Option Bool)
    (h : ∀ (i : Fin n) (x y : X i), x ≠ y → c i x y = c' i x y) : nary c imp = nary c' imp := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · obtain ⟨i, hi⟩ := hex
    rw [nary_apply_differ c imp hi, nary_apply_differ c' imp hi]
    exact h i (a i) (b i) hi.1
  · rw [nary_apply_imp c imp hex, nary_apply_imp c' imp hex]

/-- **AND THE FILLING HAS A KERNEL TOO.** Fillings agreeing on the cross give the same whole. -/
theorem fillings_agreeing_on_the_cross_give_the_same_whole
    (c : ∀ i, X i → X i → Option Bool) (imp imp' : Pt X → Pt X → Option Bool)
    (h : ∀ a b : Pt X, IsCross a b → imp a b = imp' a b) : nary c imp = nary c imp' := by
  funext a b
  by_cases hex : ∃ i, differsInOne a b i
  · obtain ⟨i, hi⟩ := hex
    rw [nary_apply_differ c imp hi, nary_apply_differ c imp' hi]
  · rw [nary_apply_imp c imp hex, nary_apply_imp c imp' hex]; exact h a b hex

/-- **SO THE OPERATION IS FREE ON NEITHER ARGUMENT.** What the parts generate is a term structure only after quotienting by both kernels. -/
theorem the_operation_is_free_on_neither_argument
    (c c' : ∀ i, X i → X i → Option Bool) (imp imp' : Pt X → Pt X → Option Bool)
    (hc : ∀ (i : Fin n) (x y : X i), x ≠ y → c i x y = c' i x y)
    (hi : ∀ a b : Pt X, IsCross a b → imp a b = imp' a b) :
    nary c imp = nary c' imp ∧ nary c imp = nary c imp' :=
  ⟨parts_agreeing_off_the_diagonal_give_the_same_whole c c' imp hc,
   fillings_agreeing_on_the_cross_give_the_same_whole c imp imp' hi⟩

omit [∀ i, DecidableEq (X i)] in
/-- **THE GRAIN IS STABLE UNDER TRANSPOSE.** So the transpose of a base is a base, at any value space. -/
theorem grain_is_transpose_stable {V : Type} (A : Pt X → Pt X → V) (h : isAssemblageN A) :
    isAssemblageN (fun a b => A b a) := by
  intro a b a' b' i hd hd' ha hb
  exact h b a b' a' i ⟨Ne.symm hd.1, fun j hj => (hd.2 j hj).symm⟩
    ⟨Ne.symm hd'.1, fun j hj => (hd'.2 j hj).symm⟩ hb ha

/-- **THE EXTREME WHOLES ARE DISTINCT WHEN THE DETERMINED REGION NEVER AFFIRMS.** If no single-move cell affirms while some abstains and some denies, and some cell is free, no relabelling of carrier and values relates the two extreme wholes. The carrier map is arbitrary here. SUFFICIENT, not necessary. -/
theorem the_tops_are_distinct_when_the_region_never_affirms
    (c : ∀ i, X i → X i → Option Bool)
    (hmiss : ∀ (a b : Pt X) (i : Fin n), differsInOne a b i → c i (a i) (b i) ≠ some true)
    {p q : Pt X} {i : Fin n} (hpq : differsInOne p q i) (hnone : c i (p i) (q i) = none)
    {r s : Pt X} {j : Fin n} (hrs : differsInOne r s j) (hfalse : c j (r j) (s j) = some false)
    {u v : Pt X} (huv : IsCross u v)
    (σ : Pt X → Pt X) (g : Option Bool → Option Bool) (hg : Function.Injective g)
    (h : ∀ a b, g (nary c (fun _ _ => some true) a b)
        = nary c (fun _ _ => some false) (σ a) (σ b)) : False := by
  have hnever : ∀ a b : Pt X, nary c (fun _ _ => some false) a b ≠ some true := by
    intro a b
    by_cases hex : ∃ i, differsInOne a b i
    · obtain ⟨k, hk⟩ := hex
      rw [nary_apply_differ c _ hk]; exact hmiss a b k hk
    · rw [nary_apply_imp c _ hex]; simp
  have hT : nary c (fun _ _ => some true) u v = some true := by
    rw [nary_apply_imp c _ huv]
  have hN : nary c (fun _ _ => some true) p q = none := by
    rw [nary_apply_differ c _ hpq]; exact hnone
  have hF : nary c (fun _ _ => some true) r s = some false := by
    rw [nary_apply_differ c _ hrs]; exact hfalse
  have gn : g none ≠ some true := by
    have e := h p q; rw [hN] at e; rw [e]; exact hnever _ _
  have gf : g (some false) ≠ some true := by
    have e := h r s; rw [hF] at e; rw [e]; exact hnever _ _
  have gt : g (some true) ≠ some true := by
    have e := h u v; rw [hT] at e; rw [e]; exact hnever _ _
  have d12 : g none ≠ g (some false) := fun e => by simpa using hg e
  have d13 : g none ≠ g (some true) := fun e => by simpa using hg e
  have d23 : g (some false) ≠ g (some true) := fun e => by simpa using hg e
  rcases hgn : g none with _ | b1
  · rcases hgf : g (some false) with _ | b2
    · exact d12 (by rw [hgn, hgf])
    · rcases hgt : g (some true) with _ | b3
      · exact d13 (by rw [hgn, hgt])
      · cases b2 <;> cases b3
        · exact d23 (by rw [hgf, hgt])
        · exact gt (by rw [hgt])
        · exact gf (by rw [hgf])
        · exact gf (by rw [hgf])
  · cases b1
    · rcases hgf : g (some false) with _ | b2
      · rcases hgt : g (some true) with _ | b3
        · exact d23 (by rw [hgf, hgt])
        · cases b3
          · exact d13 (by rw [hgn, hgt])
          · exact gt (by rw [hgt])
      · cases b2
        · exact d12 (by rw [hgn, hgf])
        · exact gf (by rw [hgf])
    · exact gn (by rw [hgn])

/-- With no denial on the determined region, the affirming whole takes only two of the three values. -/
theorem the_affirming_whole_is_two_valued (c : ∀ i, X i → X i → Option Bool)
    (hmiss : ∀ (a b : Pt X) (i : Fin n), differsInOne a b i → c i (a i) (b i) ≠ some false)
    (a b : Pt X) :
    nary c (fun _ _ => some true) a b = none ∨ nary c (fun _ _ => some true) a b = some true := by
  by_cases hex : ∃ i, differsInOne a b i
  · obtain ⟨k, hk⟩ := hex
    rw [nary_apply_differ c _ hk]
    rcases hv : c k (a k) (b k) with _ | v
    · exact Or.inl rfl
    · cases v
      · exact absurd hv (hmiss a b k hk)
      · exact Or.inr rfl
  · rw [nary_apply_imp c _ hex]; exact Or.inr rfl

/-- **THE MIRROR, AND IT IS NOT FREE.** If the region never denies, some cell there abstains and some affirms, and some cell is free, then no relabelling with an ONTO carrier map relates the two extreme wholes. The surjectivity is load-bearing: the counting runs the other way here, and no condition on the value map is needed. -/
theorem the_tops_are_distinct_when_the_region_never_denies (c : ∀ i, X i → X i → Option Bool)
    (hmiss : ∀ (a b : Pt X) (i : Fin n), differsInOne a b i → c i (a i) (b i) ≠ some false)
    {p q : Pt X} {i : Fin n} (hpq : differsInOne p q i) (hnone : c i (p i) (q i) = none)
    {r s : Pt X} {j : Fin n} (hrs : differsInOne r s j) (htrue : c j (r j) (s j) = some true)
    {u v : Pt X} (huv : IsCross u v)
    (σ : Pt X → Pt X) (hσ : Function.Surjective σ)
    (g : Option Bool → Option Bool)
    (h : ∀ a b, g (nary c (fun _ _ => some true) a b)
        = nary c (fun _ _ => some false) (σ a) (σ b)) : False := by
  obtain ⟨a1, ha1⟩ := hσ p; obtain ⟨b1, hb1⟩ := hσ q
  obtain ⟨a2, ha2⟩ := hσ r; obtain ⟨b2, hb2⟩ := hσ s
  obtain ⟨a3, ha3⟩ := hσ u; obtain ⟨b3, hb3⟩ := hσ v
  have e1 : g (nary c (fun _ _ => some true) a1 b1) = none := by
    rw [h, ha1, hb1, nary_apply_differ c _ hpq]; exact hnone
  have e2 : g (nary c (fun _ _ => some true) a2 b2) = some true := by
    rw [h, ha2, hb2, nary_apply_differ c _ hrs]; exact htrue
  have e3 : g (nary c (fun _ _ => some true) a3 b3) = some false := by
    rw [h, ha3, hb3, nary_apply_imp c _ huv]
  rcases the_affirming_whole_is_two_valued c hmiss a1 b1 with h1 | h1 <;>
    rcases the_affirming_whole_is_two_valued c hmiss a2 b2 with h2 | h2 <;>
      rcases the_affirming_whole_is_two_valued c hmiss a3 b3 with h3 | h3 <;>
        rw [h1] at e1 <;> rw [h2] at e2 <;> rw [h3] at e3 <;>
          simp_all

section ConstantFibre

variable {F : Type} [DecidableEq F]

/-- A carrier whose fibres are all the same. -/
abbrev CCar (n : ℕ) (F : Type) : Fin n → Type := fun _ => F

/-- Relabelling a point by permuting its coordinates. -/
def byCoord (τ : Fin n → Fin n) (p : Pt (CCar n F)) : Pt (CCar n F) := fun i => p (τ i)

omit [∀ i, DecidableEq (X i)] [DecidableEq F] in
/-- The relabelling carries a move in one coordinate to a move in another. -/
theorem byCoord_differs {τ : Fin n → Fin n} (hτ : ∀ k, τ (τ k) = k)
    {a b : Pt (CCar n F)} {i : Fin n} (h : differsInOne a b i) :
    differsInOne (byCoord τ a) (byCoord τ b) (τ i) := by
  refine ⟨?_, fun j hj => ?_⟩
  · show a (τ (τ i)) ≠ b (τ (τ i))
    rw [hτ]; exact h.1
  · show a (τ j) = b (τ j)
    refine h.2 (τ j) (fun he => hj ?_)
    rw [← he, hτ]

omit [∀ i, DecidableEq (X i)] [DecidableEq F] in
/-- And it carries free cells to free cells. -/
theorem byCoord_cross {τ : Fin n → Fin n} (hτ : ∀ k, τ (τ k) = k)
    {a b : Pt (CCar n F)} (h : IsCross a b) :
    IsCross (byCoord τ a) (byCoord τ b) := by
  rintro ⟨k, hk⟩
  refine h ⟨τ k, ?_⟩
  have hb : ∀ p : Pt (CCar n F), byCoord τ (byCoord τ p) = p := by
    intro p; funext m; show p (τ (τ m)) = p m; rw [hτ]
  have := byCoord_differs hτ hk
  rwa [hb, hb] at this

/-- **A PART-EXCHANGING PERMUTATION COLLAPSES THE TWO EXTREME WHOLES.** An involutive permutation of coordinates under which each part becomes the next one's verdict-flip identifies them. A FURTHER route to collapse, which is why the two laws above are sufficient and not necessary. -/
theorem a_part_exchanging_permutation_collapses_the_tops
    (c : ∀ i, CCar n F i → CCar n F i → Option Bool) (τ : Fin n → Fin n) (hτ : ∀ k, τ (τ k) = k)
    (hexch : ∀ (k : Fin n) (x y : F), x ≠ y → (c k x y).map (fun t => !t) = c (τ k) x y)
    (a b : Pt (CCar n F)) :
    (nary c (fun _ _ => some true) a b).map (fun t => !t)
      = nary c (fun _ _ => some false) (byCoord τ a) (byCoord τ b) := by
  by_cases hex : ∃ i, differsInOne a b i
  · obtain ⟨i, hi⟩ := hex
    rw [nary_apply_differ c _ hi, nary_apply_differ c _ (byCoord_differs hτ hi)]
    show (c i (a i) (b i)).map (fun t => !t) = c (τ i) (a (τ (τ i))) (b (τ (τ i)))
    rw [hτ]
    exact hexch i (a i) (b i) hi.1
  · rw [nary_apply_imp c _ hex, nary_apply_imp c _ (byCoord_cross hτ hex)]
    rfl

end ConstantFibre


/-! ### The fine structure: what the parts decide and what the carrier only permits

The four features of a filling's fine structure are governed by the PARTS, not by the carrier. Whether the
floor cuts the fillings down, and whether the whole can be made total, each have an exact condition on the
parts alone. The carrier enters only as a CEILING, through thinness: a thin carrier forces the floor to bite
whatever the parts are, and a carrier that is not thin always permits parts that make it vacuous.

BOUNDS. These are laws; the census of WHICH small carriers are thin is a finite observation and is not here.
The maxima result assumes two distinct points. -/

open scoped Classical in
/-- The value the parts agree on around a point, when they agree on anything there. -/
noncomputable def lvl (c : ∀ i, X i → X i → Option Bool) (q : Pt X) : Option Bool :=
  if h : ∃ p : Pt X × Fin n, differsInOne p.1 q p.2
    then c h.choose.2 (h.choose.1 h.choose.2) (q h.choose.2) else none

/-- The filling that levels every cross cell to that value. -/
noncomputable def levelling (c : ∀ i, X i → X i → Option Bool) : Pt X → Pt X → Option Bool :=
  fun _ q => lvl c q

/-- Under it every row takes the same value at every point. -/
theorem levelled_rows_agree (c : ∀ i, X i → X i → Option Bool) (h : ¬ FactorsSeparate c)
    (a q : Pt X) : nary c (levelling c) a q = lvl c q := by
  by_cases hex : ∃ i, differsInOne a q i
  · obtain ⟨i, hi⟩ := hex
    rw [nary_apply_differ c _ hi]
    have hp : ∃ p : Pt X × Fin n, differsInOne p.1 q p.2 := ⟨(a, i), hi⟩
    rw [lvl, dif_pos hp]
    by_contra hne
    exact h ⟨a, hp.choose.1, q, i, hp.choose.2, hi, hp.choose_spec, hne⟩
  · rw [nary_apply_imp c _ hex]; rfl

/-- **NON-SEPARATING PARTS ADMIT A FILLING THAT COLLAPSES THE WHOLE.** The levelling filling is the explicit witness. -/
theorem unseparating_factors_admit_a_levelling_import (c : ∀ i, X i → X i → Option Bool)
    (h : ¬ FactorsSeparate c) : ¬ NonDegenerate (nary c (levelling c)) := by
  rintro ⟨a, b, hne⟩
  exact hne (funext fun q => by
    rw [levelled_rows_agree c h a q, levelled_rows_agree c h b q])

/-- **THE FLOOR IS VACUOUS EXACTLY WHEN THE PARTS SEPARATE.** Carrier-general, both directions. Whether the floor cuts the fillings down is decided by the PARTS; the carrier appears nowhere in the condition. -/
theorem the_floor_is_vacuous_iff_the_factors_separate (c : ∀ i, X i → X i → Option Bool) :
    (∀ imp, NonDegenerate (nary c imp)) ↔ FactorsSeparate c := by
  refine ⟨fun hall => ?_, fun h imp => separating_factors_defeat_every_import c h imp⟩
  by_contra h
  exact unseparating_factors_admit_a_levelling_import c h (hall _)

/-- A carrier is THIN when no point has two distinct single-move neighbours. This is what the coordinate count and the points-per-coordinate count collapse into. -/
abbrev Thin (X : Fin n → Type) : Prop :=
  ∀ (a b q : Pt X) (i j : Fin n), differsInOne a q i → differsInOne b q j → a = b

omit [∀ i, DecidableEq (X i)] in
/-- On a thin carrier no parts separate: the two neighbours are the same point and the same coordinate. -/
theorem thin_carriers_admit_no_separating_factors (hT : Thin X)
    (c : ∀ i, X i → X i → Option Bool) : ¬ FactorsSeparate c := by
  rintro ⟨a, b, q, i, j, ha, hb, hne⟩
  have hab : a = b := hT a b q i j ha hb
  subst hab
  have hij : i = j := differsInOne_unique ha hb
  subst hij
  exact hne rfl

/-- **ON A THIN CARRIER THE FLOOR BITES WHATEVER THE PARTS ARE.** -/
theorem the_floor_bites_at_every_factor_choice_on_a_thin_carrier (hT : Thin X)
    (c : ∀ i, X i → X i → Option Bool) : ∃ imp, ¬ NonDegenerate (nary c imp) :=
  ⟨levelling c, unseparating_factors_admit_a_levelling_import c
    (thin_carriers_admit_no_separating_factors hT c)⟩

/-- Parts built to answer one way on one named neighbour and the other way everywhere else. -/
def sepFactors (i : Fin n) (u : X i) : ∀ k, X k → X k → Option Bool :=
  fun k x _ => if h : k = i then some (decide (h ▸ x = u)) else some false

/-- **A CARRIER THAT IS NOT THIN ADMITS SEPARATING PARTS.** So the ceiling is exact. -/
theorem a_carrier_that_is_not_thin_admits_separating_factors (hT : ¬ Thin X) :
    ∃ c : ∀ i, X i → X i → Option Bool, FactorsSeparate c := by
  simp only [Thin, not_forall] at hT
  obtain ⟨a, b, q, i, j, ha, hb, hab⟩ := hT
  refine ⟨sepFactors i (a i), a, b, q, i, j, ha, hb, ?_⟩
  have hleft : sepFactors i (a i) i (a i) (q i) = some true := by simp [sepFactors]
  have hright : sepFactors i (a i) j (b j) (q j) = some false := by
    by_cases hji : j = i
    · subst hji
      have hne : b j ≠ a j := by
        intro hEq
        exact hab (funext fun k => by
          by_cases hk : k = j
          · subst hk; exact hEq.symm
          · rw [ha.2 k hk, ← hb.2 k hk])
      simp [sepFactors, hne]
    · simp [sepFactors, hji]
  rw [hleft, hright]
  simp

/-- **THE CARRIER FORCES THE FLOOR TO BITE EXACTLY WHEN IT IS THIN.** Carrier-general, both directions. This is the whole of the carrier's contribution: it does not decide the feature, it decides whether the feature is still free to vary once the parts are chosen. -/
theorem the_carrier_forces_the_floor_iff_it_is_thin :
    (∀ c : ∀ i, X i → X i → Option Bool, ∃ imp, ¬ NonDegenerate (nary c imp)) ↔ Thin X := by
  refine ⟨fun hall => ?_, fun hT c => the_floor_bites_at_every_factor_choice_on_a_thin_carrier hT c⟩
  by_contra hT
  obtain ⟨c, hc⟩ := a_carrier_that_is_not_thin_admits_separating_factors hT
  obtain ⟨imp, himp⟩ := hall c
  exact himp (separating_factors_defeat_every_import c hc imp)

/-- **THE WHOLE CAN BE MADE TOTAL EXACTLY WHEN THE PARTS LEAVE NO ABSENCE ON THE REGION.** A filling can fill every cross cell and no region cell, so the region's absences are beyond every filling's reach. -/
theorem the_whole_can_be_total_iff_the_factors_are_present_on_the_region
    (c : ∀ i, X i → X i → Option Bool) :
    (∃ imp, isTotal (nary c imp)) ↔
      ∀ (a b : Pt X) (i : Fin n), differsInOne a b i → c i (a i) (b i) ≠ none := by
  constructor
  · rintro ⟨imp, hT⟩ a b i hi
    have := hT a b
    rwa [nary_apply_differ c imp hi] at this
  · intro hpres
    refine ⟨fun _ _ => some true, fun a b => ?_⟩
    by_cases hex : ∃ i, differsInOne a b i
    · obtain ⟨i, hi⟩ := hex
      rw [nary_apply_differ c _ hi]; exact hpres a b i hi
    · rw [nary_apply_imp c _ hex]; simp

/-- A filling is a maximum of the admissible space when it clears the floor and nothing admissible sits strictly above it. -/
def MaximalAdmissible (c : ∀ i, X i → X i → Option Bool) (imp : Pt X → Pt X → Option Bool) : Prop :=
  NonDegenerate (nary c imp) ∧
    ∀ imp', cLE imp imp' → NonDegenerate (nary c imp') → cLE imp' imp

/-- A total filling is maximal in the information order, so an admissible total filling is a maximum. -/
theorem a_total_admissible_import_is_a_maximum (c : ∀ i, X i → X i → Option Bool)
    (imp : Pt X → Pt X → Option Bool) (ht : isTotal imp)
    (ha : NonDegenerate (nary c imp)) : MaximalAdmissible c imp :=
  ⟨ha, fun imp' h _ => (maximal_iff_total imp).2 ht imp' h⟩

open scoped Classical in
/-- The filling that answers one way at a single named cell and the other way everywhere else. -/
noncomputable def spikeAt (a b : Pt X) : Pt X → Pt X → Option Bool :=
  fun x y => if x = a ∧ y = b then some true else some false

/-- **WHERE THE FLOOR IS VACUOUS AND THE CARRIER HAS TWO POINTS, THERE ARE AT LEAST THREE MAXIMA.** Every total filling is admissible, and three pairwise distinct ones are available as soon as two cells are. -/
theorem a_vacuous_floor_has_at_least_three_maxima (c : ∀ i, X i → X i → Option Bool)
    (hsep : FactorsSeparate c) {a b : Pt X} (hab : a ≠ b) :
    ∃ i1 i2 i3 : Pt X → Pt X → Option Bool,
      MaximalAdmissible c i1 ∧ MaximalAdmissible c i2 ∧ MaximalAdmissible c i3 ∧
        i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 := by
  classical
  refine ⟨fun _ _ => some true, fun _ _ => some false, spikeAt a a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact a_total_admissible_import_is_a_maximum c _ (fun _ _ => by simp)
      (separating_factors_defeat_every_import c hsep _)
  · exact a_total_admissible_import_is_a_maximum c _ (fun _ _ => by simp)
      (separating_factors_defeat_every_import c hsep _)
  · refine a_total_admissible_import_is_a_maximum c _ (fun x y => ?_)
      (separating_factors_defeat_every_import c hsep _)
    by_cases h : x = a ∧ y = a <;> simp [spikeAt, h]
  · intro h; have := congrFun (congrFun h a) a; simp at this
  · intro h; have := congrFun (congrFun h b) b; simp [spikeAt, hab.symm] at this
  · intro h; have := congrFun (congrFun h a) a; simp [spikeAt] at this

/-- **SO A TWO-MAXIMA SHAPE REQUIRES A BITING FLOOR.** Two maxima related by a relabelling cannot occur where the parts separate. -/
theorem the_two_maxima_shape_requires_a_biting_floor (c : ∀ i, X i → X i → Option Bool)
    {a b : Pt X} (hab : a ≠ b)
    (htwo : ∀ i1 i2 i3 : Pt X → Pt X → Option Bool, MaximalAdmissible c i1 →
      MaximalAdmissible c i2 → MaximalAdmissible c i3 → i1 = i2 ∨ i1 = i3 ∨ i2 = i3) :
    ∃ imp, ¬ NonDegenerate (nary c imp) := by
  by_cases hsep : FactorsSeparate c
  · obtain ⟨i1, i2, i3, h1, h2, h3, h12, h13, h23⟩ :=
      a_vacuous_floor_has_at_least_three_maxima c hsep hab
    rcases htwo i1 i2 i3 h1 h2 h3 with h | h | h
    · exact absurd h h12
    · exact absurd h h13
    · exact absurd h h23
  · exact ⟨levelling c, unseparating_factors_admit_a_levelling_import c hsep⟩

/-- Every distinction between rows lives only at the cross: two rows never differ at a column where both of their cells are region cells. -/
def DistinctionsLiveOnlyAtTheCross (c : ∀ i, X i → X i → Option Bool) : Prop :=
  ∀ (imp : Pt X → Pt X → Option Bool) (a b q : Pt X) (i j : Fin n),
    differsInOne a q i → differsInOne b q j → nary c imp a q = nary c imp b q

/-- **THE PARTS FAIL TO SEPARATE EXACTLY WHEN EVERY DISTINCTION LIVES ONLY AT THE CROSS.** Carrier-general, an equivalence, so no particular carrier can make it answer falsely. -/
theorem the_factors_fail_to_separate_iff_distinctions_live_only_at_the_cross
    (c : ∀ i, X i → X i → Option Bool) :
    ¬ FactorsSeparate c ↔ DistinctionsLiveOnlyAtTheCross c := by
  constructor
  · intro h imp a b q i j ha hb
    rw [nary_apply_differ c imp ha, nary_apply_differ c imp hb]
    by_contra hne
    exact h ⟨a, b, q, i, j, ha, hb, hne⟩
  · rintro h ⟨a, b, q, i, j, ha, hb, hne⟩
    have := h (fun _ _ => none) a b q i j ha hb
    rw [nary_apply_differ c _ ha, nary_apply_differ c _ hb] at this
    exact hne this

/-- The filling is LOAD-BEARING when the object's survival depends on it: some filling collapses the whole. -/
def LoadBearing (c : ∀ i, X i → X i → Option Bool) : Prop :=
  ∃ imp, ¬ NonDegenerate (nary c imp)

/-- **LOAD-BEARING IS EXACTLY DISTINCTIONS-LIVING-ONLY-AT-THE-CROSS.** The filling matters to survival precisely when nothing the parts say singly tells two rows apart. -/
theorem the_import_is_load_bearing_iff_distinctions_live_only_at_the_cross
    (c : ∀ i, X i → X i → Option Bool) :
    LoadBearing c ↔ DistinctionsLiveOnlyAtTheCross c := by
  rw [← the_factors_fail_to_separate_iff_distinctions_live_only_at_the_cross c]
  constructor
  · rintro ⟨imp, himp⟩ hsep
    exact himp (separating_factors_defeat_every_import c hsep imp)
  · intro h
    exact ⟨levelling c, unseparating_factors_admit_a_levelling_import c h⟩

omit [∀ i, DecidableEq (X i)] in
/-- **A TOTAL PART AND AN ABSENT PART SEPARATE.** Carrier-general: the two neighbours are built explicitly, one moving in each coordinate, and the verdicts differ because one is present and the other is not. -/
theorem a_total_factor_and_an_absent_factor_separate (c : ∀ i, X i → X i → Option Bool)
    (q0 : Pt X) {i j : Fin n} (hij : i ≠ j)
    (htot : ∀ x y : X i, c i x y ≠ none)
    {s t : X i} (hst : s ≠ t) {u w : X j} (huw : u ≠ w) (habs : c j u w = none) :
    FactorsSeparate c := by
  classical
  set q : Pt X := Function.update (Function.update q0 i t) j w with hq
  have hqi : q i = t := by
    rw [hq, Function.update_of_ne hij, Function.update_self]
  have hqj : q j = w := by rw [hq, Function.update_self]
  refine ⟨Function.update q i s, Function.update q j u, q, i, j, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [Function.update_self, hqi]; exact hst
  · intro k hk; exact Function.update_of_ne hk _ _
  · rw [Function.update_self, hqj]; exact huw
  · intro k hk; exact Function.update_of_ne hk _ _
  · rw [Function.update_self, Function.update_self, hqi, hqj, habs]
    exact htot s t

end Chiralogy
