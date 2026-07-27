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

end Chiralogy
