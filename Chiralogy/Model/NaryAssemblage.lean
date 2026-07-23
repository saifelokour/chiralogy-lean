import Chiralogy.Model.InformationOrder
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.VecNotation

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
def isAssemblageN (A : (∀ i, X i) → (∀ i, X i) → Option Bool) : Prop :=
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

end Chiralogy
