module

public import Formalism.ThetaLogCoordinates.JacobiPathWeights.IndexWeightsDominance
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Sym.Card

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace A3comb

private theorem colHeight_out {n : ℕ} {μ : Fin n → ℤ} {M c : ℤ} (hM : ∀ m, |μ m| ≤ M)
    (hc : c ∉ Finset.Icc (-M) M) : colHeight μ c = if M < c then 0 else n := by
  unfold colHeight; rcases Nat.eq_zero_or_pos n with rfl | _
  · simp
  · rw [Finset.mem_Icc] at hc; split_ifs with hMc
    · exact card_eq_zero.mpr (filter_eq_empty_iff.mpr fun m _ => by have := abs_le.mp (hM m); omega)
    · rw [filter_true_of_mem fun m _ => by have := abs_le.mp (hM m); omega, card_univ, Fintype.card_fin]

theorem idx_empty {n : ℕ} {μ : Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (M : ℤ)
    (hM : ∀ m, |μ m| ≤ M) (c : ℤ) (hc : c ∉ Finset.Icc (-M) M) : I c = ∅ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact eq_empty_of_isEmpty _
  · have : 0 ≤ M := (abs_nonneg _).trans (hM ⟨0, hn⟩)
    rw [← card_eq_zero, hI c, colHeight_out hM hc]; rw [Finset.mem_Icc] at hc; split_ifs <;> omega

theorem exists_bound {n : ℕ} (μ : Fin n → ℤ) : ∃ M : ℤ, ∀ m, |μ m| ≤ M :=
  ⟨∑ m, |μ m|, fun m => single_le_sum (f := fun m => |μ m|) (fun _ _ => abs_nonneg _) (mem_univ m)⟩

private theorem ncard_eq_filter_lemma {n : ℕ} (I : ℤ → Finset (Fin n)) (S : Finset ℤ)
    (hS : ∀ c, c ∉ S → I c = ∅) (m : Fin n) (p : ℤ → Prop) [DecidablePred p] :
    ({c : ℤ | p c ∧ m ∈ I c}.ncard : ℤ) = ((S.filter fun c => p c ∧ m ∈ I c).card : ℤ) := by
  congr 1; rw [← Set.ncard_coe_finset]; congr 1; ext c
  simp only [Set.mem_ofPred_eq, mem_coe, mem_filter]
  exact ⟨fun h => ⟨by by_contra hc; simp [hS c hc] at h, h⟩, fun h => h.2⟩

theorem idxWeight_eq {n : ℕ} (I : ℤ → Finset (Fin n)) (S : Finset ℤ) (hS : ∀ c, c ∉ S → I c = ∅)
    (m : Fin n) :
    idxWeight I m = ∑ c ∈ S, (if m ∈ I c then (if 1 ≤ c then (1 : ℤ) else -1) else 0) := by
  unfold idxWeight
  rw [ncard_eq_filter_lemma I S hS m (1 ≤ ·), ncard_eq_filter_lemma I S hS m (· ≤ 0),
    card_filter, card_filter, Nat.cast_sum, Nat.cast_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun c _ => ?_
  by_cases hm : m ∈ I c <;> by_cases hc : 1 ≤ c <;> simp [hm, hc, show c ≤ 0 ↔ ¬ 1 ≤ c by omega]

end A3comb

open A3comb in
theorem psi_weight : PsiWeight := by
  intro R _ n N isVec _ μ I _ hI
  have hXw (x : ℕ × Fin n) : IsWeightedHomogeneous (torusW isVec)
      (X x : MvPolynomial (ℕ × Fin n) R) (torusW isVec x) := by
    have := isWeightedHomogeneous_monomial (torusW isVec) (Finsupp.single x 1) (1 : R) rfl
    simp only [Finsupp.weight_apply, Finsupp.sum_single_index, zero_smul, one_smul] at this
    exact this
  have key (c : ℤ) (k : ℕ) : ∀ J : Finset (Fin n),
      IsWeightedHomogeneous (torusW isVec)
        (pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) k J)
        (fun a => if a ∈ J then (if 1 ≤ c then (1 : ℤ) else -1) else 0) := by
    induction k with
    | zero =>
      intro J; simp only [pathWord, oneF]; rcases eq_or_ne J ∅ with rfl | hJ
      · convert isWeightedHomogeneous_monomial (torusW isVec) 0 (1 : R) (map_zero _) using 1 <;>
          [simp; (ext; simp)]
      · simp only [hJ, ↓reduceIte, ← mem_weightedHomogeneousSubmodule]; exact Submodule.zero_mem _
    | succ k ih =>
      intro J; simp only [pathWord]
      by_cases hcol : colHeight (μ (k + 1)) c = colHeight (μ k) c
      · simp only [hcol, ↓reduceIte]; exact ih J
      · simp only [hcol, ↓reduceIte, stepF]
        by_cases hup : (isVec k == decide (1 ≤ c)) = true <;> simp only [hup, ↓reduceIte]
        · unfold wedgeF; beta_reduce; rw [← mem_weightedHomogeneousSubmodule]
          refine Submodule.sum_mem _ fun m hm => ?_
          rw [mul_assoc, ← zsmul_eq_mul]
          refine zsmul_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_) _
          convert (ih (J.erase m)).mul (hXw (k, m)) using 1; funext a
          simp only [Pi.add_apply, torusW, ite_apply, mem_erase, Pi.single_apply, Pi.neg_apply]
          by_cases hc : 1 ≤ c <;> simp only [hc, ↓reduceIte, decide_true, decide_false] at hup ⊢ <;>
            cases hv : isVec k <;> by_cases ha : a = m <;> simp_all
        · unfold contrF; beta_reduce; rw [← mem_weightedHomogeneousSubmodule]
          refine Submodule.sum_mem _ fun m hm => ?_
          rw [mul_assoc, ← zsmul_eq_mul]; have hm' := mem_compl.mp hm
          refine zsmul_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_) _
          convert (hXw (k, m)).mul (ih (insert m J)) using 1; funext a
          simp only [Pi.add_apply, torusW, ite_apply, mem_insert, Pi.single_apply, Pi.neg_apply]
          by_cases hc : 1 ≤ c <;> simp only [hc, ↓reduceIte, decide_true, decide_false] at hup ⊢ <;>
            cases hv : isVec k <;> by_cases ha : a = m <;> simp_all
  let T : ℤ := ∑ k ∈ range (N + 1), ∑ m, |μ k m|
  have hb (k : ℕ) (hk : k ≤ N) (m : Fin n) : |μ k m| ≤ T :=
    (single_le_sum (f := fun m' => |μ k m'|) (fun _ _ => abs_nonneg _) (mem_univ m)).trans
      (single_le_sum (f := fun k' => ∑ m', |μ k' m'|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_range.mpr (by omega)))
  have hS (c : ℤ) (hc : c ∉ Icc (-T) T) : I c = ∅ := idx_empty hI T (hb N le_rfl) c hc
  have hone (c : ℤ) (hc : c ∉ Icc (-T) T) (k : ℕ) : k ≤ N →
      pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) k = oneF := by
    induction k with
    | zero => exact fun _ => rfl
    | succ k ih =>
      intro hk; simp only [pathWord]
      rw [colHeight_out (hb _ hk) hc, colHeight_out (hb _ (by omega)) hc]; simpa using ih (by omega)
  have hsupp : Function.mulSupport (fun c => pathWord isVec μ c
      (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)) ⊆ ↑(Icc (-T) T) :=
    fun c hc => by_contra fun hcS => hc (by simp [hone c hcS N le_rfl, hS c hcS, oneF])
  rw [psiPath, finprod_eq_prod_of_mulSupport_subset _ hsupp]
  convert IsWeightedHomogeneous.prod (Icc (-T) T) _ _ (fun c _ => key c N (I c)) using 1
  funext a; simp only [Finset.sum_apply, idxWeight_eq I (Icc (-T) T) hS a]

namespace A3comb

theorem sum_idxWeight {n : ℕ} (I : ℤ → Finset (Fin n)) (S : Finset ℤ) (hS : ∀ c, c ∉ S → I c = ∅)
    (F : Finset (Fin n)) : ∑ m ∈ F, idxWeight I m =
      ∑ c ∈ S, (if 1 ≤ c then (1 : ℤ) else -1) * ((F.filter fun m => m ∈ I c).card : ℤ) := by
  simp_rw [idxWeight_eq I S hS, card_filter, Nat.cast_sum, mul_sum]; rw [sum_comm]
  exact sum_congr rfl fun c _ => sum_congr rfl fun m _ => by by_cases hm : m ∈ I c <;> simp [hm]

private theorem card_lt_lemma (n k : ℕ) :
    (univ.filter fun m : Fin n => m.val < k).card = min k n := by
  rw [← card_map Fin.valEmbedding, ← card_range (min k n)]; congr 1; ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range, lt_min_iff]
  exact ⟨fun ⟨a, ha, e⟩ => ⟨e ▸ ha, e ▸ a.2⟩, fun ⟨h1, h2⟩ => ⟨⟨x, h2⟩, h1, rfl⟩⟩

private theorem lt_colHeight_iff_lemma {n : ℕ} {μ : Fin n → ℤ} (h : Antitone μ) (c : ℤ) (m : Fin n) :
    m.val < colHeight μ c ↔ c ≤ μ m := by
  have hmn := m.2; unfold colHeight; constructor
  · refine fun hm => by_contra fun hc => hm.not_ge ?_
    refine (card_le_card fun m' hm' => ?_).trans_eq ((card_lt_lemma n m.val).trans (min_eq_left hmn.le))
    simp only [mem_filter, mem_univ, true_and] at hm' ⊢
    exact by_contra fun hle => hc ((h (Fin.le_iff_val_le_val.mpr (by omega))).trans' hm')
  · intro hc
    have h1 : m.val + 1 ≤ (univ.filter fun m' : Fin n => c ≤ μ m').card := by
      rw [← min_eq_left (by omega : m.val + 1 ≤ n), ← card_lt_lemma n (m.val + 1)]
      exact card_le_card fun m' hm' => by
        simp only [mem_filter, mem_univ, true_and] at hm' ⊢
        exact hc.trans (h (Fin.le_iff_val_le_val.mpr (by omega)))
    omega

theorem idxWeight_can {n : ℕ} {μ : Fin n → ℤ} (h : Antitone μ) : idxWeight (canIdx μ) = μ := by
  funext m; unfold idxWeight
  have h1 : {c : ℤ | 1 ≤ c ∧ m ∈ canIdx μ c} = ↑(Icc 1 (μ m)) := by
    ext c; simp +contextual [canIdx, lt_colHeight_iff_lemma h]
  have h2 : {c : ℤ | c ≤ 0 ∧ m ∈ canIdx μ c} = ↑(Ioc (μ m) 0) := by
    ext c; simp only [Set.mem_ofPred_eq, canIdx, coe_Ioc, Set.mem_Ioc]
    split_ifs <;> simp only [mem_filter, mem_univ, true_and, ← not_lt, lt_colHeight_iff_lemma h] <;> omega
  rw [h1, h2, Set.ncard_coe_finset, Set.ncard_coe_finset, Int.card_Icc, Int.card_Ioc]; omega

def rowsLt (n j : ℕ) : Finset (Fin n) := univ.filter fun m => m.val < j

private theorem card_rowsLt_lemma (n k : ℕ) : (rowsLt n k).card = min k n := card_lt_lemma n k
private theorem colHeight_le {n : ℕ} (μ : Fin n → ℤ) (c : ℤ) : colHeight μ c ≤ n :=
  (card_filter_le _ _).trans (by simp)

theorem cnt_init {n : ℕ} (J : Finset (Fin n)) (h j : ℕ) (hJ : J.card = (rowsLt n h).card) :
    ((rowsLt n j).filter fun m => m ∈ J).card ≤ ((rowsLt n j).filter fun m => m ∈ rowsLt n h).card := by
  have e : ((rowsLt n j).filter fun m => m ∈ rowsLt n h) = rowsLt n (min j h) := by
    ext m; simp [rowsLt, lt_min_iff]
  have h1 := card_filter_le (rowsLt n j) (· ∈ J)
  have h2 : ((rowsLt n j).filter fun m => m ∈ J).card ≤ J.card := card_le_card fun _ hx => (mem_filter.mp hx).2
  rw [e, card_rowsLt_lemma]; rw [card_rowsLt_lemma] at h1 hJ; omega

theorem card_filter_lt_le_alt {n : ℕ} (J : Finset (Fin n)) (h j : ℕ) (hJ : J.card = ((rowsLt n h)ᶜ).card) :
    ((rowsLt n j).filter fun m => m ∈ (rowsLt n h)ᶜ).card ≤ ((rowsLt n j).filter fun m => m ∈ J).card := by
  rw [filter_mem_eq_inter, filter_mem_eq_inter]
  rcases le_total j h with hjh | hjh
  · rw [show rowsLt n j ∩ (rowsLt n h)ᶜ = ∅ by
      ext m; simp only [rowsLt, mem_inter, mem_compl, mem_filter, mem_univ, true_and, notMem_empty,
        iff_false]; omega, card_empty]
    exact Nat.zero_le _
  · have hu : rowsLt n j ∪ (rowsLt n h)ᶜ = univ := by
      ext m; simp only [rowsLt, mem_union, mem_compl, mem_filter, mem_univ, true_and, iff_true]; omega
    have e1 := card_union_add_card_inter (rowsLt n j) ((rowsLt n h)ᶜ)
    have e2 := card_union_add_card_inter (rowsLt n j) J
    have e3 := card_le_univ (rowsLt n j ∪ J)
    rw [hu, card_univ, Fintype.card_fin] at e1; rw [Fintype.card_fin] at e3; omega

theorem can_pos {n : ℕ} (μ : Fin n → ℤ) {c : ℤ} (hc : 1 ≤ c) : canIdx μ c = rowsLt n (colHeight μ c) := by
  simp [canIdx, rowsLt, hc]

theorem can_neg {n : ℕ} (μ : Fin n → ℤ) {c : ℤ} (hc : ¬ 1 ≤ c) : canIdx μ c = (rowsLt n (colHeight μ c))ᶜ := by
  ext m; simp [canIdx, rowsLt, hc]

theorem col_le {n : ℕ} {μ : Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (c : ℤ) (j : ℕ) :
    (if 1 ≤ c then (1 : ℤ) else -1) * (((rowsLt n j).filter fun m => m ∈ I c).card : ℤ) ≤
      (if 1 ≤ c then (1 : ℤ) else -1) * (((rowsLt n j).filter fun m => m ∈ canIdx μ c).card : ℤ) := by
  have hle := colHeight_le μ c; have key := hI c
  by_cases hc : 1 ≤ c
  · simp only [hc, ↓reduceIte, one_mul, can_pos μ hc, Nat.cast_le] at key ⊢
    exact cnt_init _ _ _ (by rw [key, card_rowsLt_lemma, min_eq_left hle])
  · simp only [hc, ↓reduceIte, neg_one_mul, neg_le_neg_iff, can_neg μ hc, Nat.cast_le] at key ⊢
    exact card_filter_lt_le_alt _ _ _
      (by rw [key, card_compl, Fintype.card_fin, card_rowsLt_lemma, min_eq_left hle])

theorem col_eq {n : ℕ} {μ : Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (c : ℤ)
    (h : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c).card =
      ((rowsLt n (colHeight μ c)).filter fun m => m ∈ canIdx μ c).card) : I c = canIdx μ c := by
  have hle := colHeight_le μ c; have key := hI c
  have hcR : (rowsLt n (colHeight μ c)).card = colHeight μ c := (card_rowsLt_lemma _ _).trans (min_eq_left hle)
  by_cases hc : 1 ≤ c
  · simp only [hc, ↓reduceIte] at key
    have f1 : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c) ⊆ I c := fun _ hx => (mem_filter.mp hx).2
    have f2 : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c) ⊆ rowsLt n (colHeight μ c) := filter_subset _ _
    rw [can_pos μ hc] at h ⊢; rw [filter_true_of_mem fun _ hx => hx] at h
    exact (eq_of_subset_of_card_le f1 (by linarith)).symm.trans
      (eq_of_subset_of_card_le f2 (by linarith))
  · simp only [hc, ↓reduceIte] at key; rw [can_neg μ hc] at h ⊢
    have e : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ (rowsLt n (colHeight μ c))ᶜ) = ∅ := by ext; simp
    rw [e, card_empty, card_eq_zero] at h
    refine eq_of_subset_of_card_le (fun x hx => mem_compl.mpr fun hxR => ?_)
      (by rw [card_compl, Fintype.card_fin, hcR, key])
    exact notMem_empty x (h ▸ mem_filter.mpr ⟨hxR, hx⟩)

end A3comb

open A3comb in
theorem index_weights_dominance : IndexWeightsDominance := by
  intro n μ I hμ hI; obtain ⟨M, hM⟩ := exists_bound μ
  have hcan : IsIndex μ (canIdx μ) := fun c => by
    have hle := colHeight_le μ c; by_cases hc : 1 ≤ c <;> simp only [hc, ↓reduceIte]
    · rw [can_pos μ hc, card_rowsLt_lemma, min_eq_left hle]
    · rw [can_neg μ hc, card_compl, Fintype.card_fin, card_rowsLt_lemma, min_eq_left hle]
  have hS := idx_empty hI M hM; have hS' := idx_empty hcan M hM
  have hRn : (univ : Finset (Fin n)) = rowsLt n n := by ext m; simp [rowsLt]
  refine ⟨⟨?_, fun j => ?_⟩, fun hw => funext fun c => ?_⟩
  · rw [hRn, ← idxWeight_can hμ, sum_idxWeight I _ hS, sum_idxWeight (canIdx μ) _ hS']
    exact sum_congr rfl fun c _ => by simp_rw [← hRn, filter_univ_mem, hI c, hcan c]
  · change ∑ m ∈ rowsLt n j, idxWeight I m ≤ ∑ m ∈ rowsLt n j, μ m
    rw [show (∑ m ∈ rowsLt n j, μ m) = ∑ m ∈ rowsLt n j, idxWeight (canIdx μ) m by rw [idxWeight_can hμ],
      sum_idxWeight I _ hS, sum_idxWeight (canIdx μ) _ hS']
    exact sum_le_sum fun c _ => col_le hI c j
  · by_cases hcS : c ∈ Icc (-M) M
    · refine col_eq hI c ?_
      have hsum0 : ∑ c' ∈ Icc (-M) M, ((if 1 ≤ c' then (1 : ℤ) else -1) *
          (((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c').card : ℤ) -
          (if 1 ≤ c' then (1 : ℤ) else -1) *
          (((rowsLt n (colHeight μ c)).filter fun m => m ∈ canIdx μ c').card : ℤ)) = 0 := by
        rw [sum_sub_distrib, ← sum_idxWeight I _ hS, ← sum_idxWeight (canIdx μ) _ hS',
          idxWeight_can hμ, hw, sub_self]
      have h0 := (sum_eq_zero_iff_of_nonpos
        (fun c' _ => sub_nonpos.mpr (col_le hI c' (colHeight μ c)))).mp hsum0 c hcS
      have h1 : (((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c).card : ℤ) =
          (((rowsLt n (colHeight μ c)).filter fun m => m ∈ canIdx μ c).card : ℤ) := by
        split_ifs at h0 <;> linarith
      exact_mod_cast h1
    · rw [hS c hcS, hS' c hcS]

namespace A3comb

theorem weight_letter {n : ℕ} (i : ℕ) (e : ℕ × Fin n →₀ ℕ) :
    Finsupp.weight (fun x : ℕ × Fin n => if x.1 = i then 1 else 0) e = ∑ a, e (i, a) := by
  refine Finsupp.induction_linear e (by simp)
    (fun f g hf hg => by simp [hf, hg, sum_add_distrib]) fun ⟨x1, x2⟩ k => ?_
  rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]
  by_cases hi : x1 = i <;> simp [hi, Finsupp.single_apply]

def mkMon {n N : ℕ} (d : Fin N → (Fin n →₀ ℕ)) : ℕ × Fin n →₀ ℕ :=
  Finsupp.onFinset (range N ×ˢ univ) (fun x => if h : x.1 < N then d ⟨x.1, h⟩ x.2 else 0) (by
    intro x hx; rw [Finset.mem_product, Finset.mem_range]; refine ⟨?_, Finset.mem_univ _⟩
    by_contra h; exact hx (by simp [h]))

theorem mkMon_apply {n N : ℕ} (d : Fin N → (Fin n →₀ ℕ)) (i : Fin N) (a : Fin n) :
    mkMon d (i.val, a) = d i a := by simp [mkMon]

theorem mkMon_apply_ge {n N : ℕ} (d : Fin N → (Fin n →₀ ℕ)) (i : ℕ) (hi : ¬ i < N) (a : Fin n) :
    mkMon d (i, a) = 0 := by simp [mkMon, hi]

theorem mkMon_inj {n N : ℕ} : Function.Injective (mkMon (n := n) (N := N)) := fun d d' h =>
  funext fun i => Finsupp.ext fun a => by simpa [mkMon_apply] using DFunLike.congr_fun h (i.val, a)

theorem monSet_eq (n N : ℕ) (B : ℕ → ℕ) :
    {e : ℕ × Fin n →₀ ℕ | ∀ i, ∑ a, e (i, a) = if i < N then B i else 0} =
      ↑((Fintype.piFinset fun i : Fin N => (univ : Finset (Fin n)).finsuppAntidiag (B i)).image mkMon) := by
  ext e; simp only [Set.mem_ofPred_eq, coe_image, Set.mem_image, mem_coe, Fintype.mem_piFinset,
    mem_finsuppAntidiag, subset_univ, and_true]; constructor
  · intro he
    refine ⟨fun i => Finsupp.equivFunOnFinite.symm fun a => e (i.val, a),
      fun i => by simpa using he i.val, Finsupp.ext fun ⟨j, a⟩ => ?_⟩
    by_cases hj : j < N
    · exact (mkMon_apply _ ⟨j, hj⟩ a).trans (by simp)
    · have := he j; simp only [hj, ↓reduceIte, sum_eq_zero_iff] at this
      exact (mkMon_apply_ge _ _ hj a).trans (this a (mem_univ a)).symm
  · rintro ⟨d, hd, rfl⟩ i; split_ifs with hi
    · exact (sum_congr rfl fun a _ => mkMon_apply d ⟨i, hi⟩ a).trans (hd ⟨i, hi⟩)
    · exact sum_eq_zero fun a _ => mkMon_apply_ge d i hi a

end A3comb

open A3comb in
theorem polynomial_b_rank : PolBRank := by
  intro n N B
  have hcard (k : ℕ) : ((univ : Finset (Fin n)).finsuppAntidiag k).card = (n + k - 1).choose k := by
    rw [show n + k - 1 = Fintype.card (Fin n) + k - 1 by simp, ← Sym.card_sym_eq_choose, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquiv
      ({ toFun := Finsupp.toMultiset, invFun := Multiset.toFinsupp,
         left_inv := fun _ => by simp, right_inv := fun _ => by simp } : (Fin n →₀ ℕ) ≃ Multiset (Fin n))
      (fun f => by
        simp only [mem_finsuppAntidiag, subset_univ, and_true, Equiv.coe_fn_mk, Finsupp.card_toMultiset]
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]; rfl) : _ ≃ Sym (Fin n) k)
  have hset := monSet_eq n N B
  refine ⟨?_, hset ▸ finite_toSet _, fun R _ => le_antisymm ?_ ?_⟩
  · rw [hset, Set.ncard_coe_finset, card_image_of_injective _ mkMon_inj, Fintype.card_piFinset,
      Fin.prod_univ_eq_prod_range (fun i => ((univ : Finset (Fin n)).finsuppAntidiag (B i)).card) N]
    exact prod_congr rfl fun i _ => hcard (B i)
  · intro p hp; rw [polB, Submodule.mem_iInf] at hp; rw [p.as_sum]
    refine Submodule.sum_mem _ fun e he => ?_
    have heS : ∀ i, ∑ a, e (i, a) = if i < N then B i else 0 := fun i => by
      rw [← weight_letter]; exact ((mem_weightedHomogeneousSubmodule _ _ _ _).mp (hp i)) (mem_support_iff.mp he)
    rw [show monomial e (AddMonoidAlgebra.coeff p e) = AddMonoidAlgebra.coeff p e • monomial e (1 : R)
      by rw [smul_monomial, smul_eq_mul, mul_one]]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_image_of_mem _ heS))
  · rw [Submodule.span_le]; rintro _ ⟨e, he, rfl⟩; rw [polB, SetLike.mem_coe, Submodule.mem_iInf]
    exact fun i => (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
      (isWeightedHomogeneous_monomial _ _ _ ((weight_letter i e).trans (he i)))

namespace A3comb

theorem strip_bound {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip ν μ b) (m : Fin n) :
    μ m ≤ ν m ∧ ν m ≤ μ m + b := by
  obtain ⟨h1, _, h3⟩ := h
  have := single_le_sum (f := fun m' => ν m' - μ m') (fun i _ => sub_nonneg.mpr (h1 i)) (mem_univ m)
  rw [sum_sub_distrib, h3] at this; exact ⟨h1 m, by linarith⟩

theorem path_bound {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) : ∀ i ≤ N, ∀ m, |μ i m| ≤ ((∑ k ∈ range i, B k : ℕ) : ℤ) := by
  intro i; induction i with
  | zero => intro _ m; simp [hp.1]
  | succ i ih =>
    intro hi m; have ih' := abs_le.mp (ih (by omega) m); have hs := hp.2.2 i (by omega)
    rw [sum_range_succ, Nat.cast_add, abs_le]
    split_ifs at hs <;> obtain ⟨h1, h2⟩ := strip_bound hs m <;> constructor <;> linarith

theorem path_bound' {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) (i : ℕ) (hi : i ≤ N) (m : Fin n) :
    |μ i m| ≤ ((∑ k ∈ range N, B k : ℕ) : ℤ) :=
  (path_bound hp i hi m).trans (Nat.cast_le.mpr (sum_le_sum_of_subset (range_mono hi)))

end A3comb

open A3comb in
theorem path_index_finite : PathIdxFinite := by
  intro n N isVec B; let M : ℤ := ((∑ k ∈ range N, B k : ℕ) : ℤ)
  have hb (x : PathIdx n N isVec B) (i : Fin (N + 1)) (m : Fin n) : x.1.1 i m ∈ Icc (-M) M :=
    mem_Icc.mpr (abs_le.mp (path_bound' x.2.1 i.val (Nat.lt_succ_iff.mp i.isLt) m))
  refine Finite.of_injective (fun x : PathIdx n N isVec B =>
    ((fun (i : Fin (N + 1)) (m : Fin n) => (⟨x.1.1 i m, hb x i m⟩ : Icc (-M) M)),
      fun c : Icc (-M) M => x.1.2 c.1)) ?_
  rintro ⟨⟨μ, I⟩, hp, hz, hstd⟩ ⟨⟨μ', I'⟩, hp', hz', hstd'⟩ h
  dsimp only at hp hz hstd hp' hz' hstd' h; obtain ⟨h1, h2⟩ := Prod.mk.inj h
  have hμ : μ = μ' := funext fun i => if hi : i ≤ N then
    funext fun m => congrArg Subtype.val (congrFun (congrFun h1 ⟨i, Nat.lt_succ_of_le hi⟩) m)
  else by rw [hz i (by omega), hz' i (by omega)]
  have hI : I = I' := funext fun c => if hc : c ∈ Icc (-M) M then congrFun h2 ⟨c, hc⟩
  else by rw [idx_empty hstd.1 M (path_bound' hp N le_rfl) c hc,
    idx_empty hstd'.1 M (path_bound' hp' N le_rfl) c hc]
  subst hμ hI; rfl

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
