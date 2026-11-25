module

public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetMinor
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleM
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleD
import Mathlib.Tactic.TypeStar
import Formalism.LocalRingCardinality.Params
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleC

@[expose] public section

noncomputable section

namespace PI.WGL.LTE

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD

theorem pow_memZ {N : ℕ} (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) ℤ)
    (hf : f ∈ dualWeyl ℤ N N ν) (k : ℕ) : f ^ k ∈ dualWeyl ℤ N N (k • ν) :=
  dualWeyl_pow hf k

theorem prod_memZ {N : ℕ} {ι : Type*} (s : Finset ι) (ν : ι → Fin N → ℕ) (f : ι → MvPolynomial (Fin N × Fin N) ℤ)
    (hf : ∀ i ∈ s, f i ∈ dualWeyl ℤ N N (ν i)) :
    ∏ i ∈ s, f i ∈ dualWeyl ℤ N N (∑ i ∈ s, ν i) :=
  dualWeyl_prod s ν f hf

theorem ite_pow_memZ {N s : ℕ} (c : Prop) [Decidable c] (f : MvPolynomial (Fin N × Fin N) ℤ)
    (hf : f ∈ dualWeyl ℤ N N (initW N s)) (e : ℕ) :
    (if c then f ^ e else 1) ∈ dualWeyl ℤ N N ((if c then e else 0) • initW N s) := by
  split_ifs
  · exact pow_memZ _ f hf e
  · simpa using (one_mem_dualWeyl (R := ℤ) (r := N) (n := N))

def colWt {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (L : Finset (Fin K)) : Fin N → ℕ :=
  (∑ i : Fin n, ((if i.1 + 1 = n then (aa h lam sg i).toNat else 0) • initW N (i.1 + 1) +
    (if i.1 = 0 then (bb h lam sg i).toNat else 0) • initW N (i.1 + 1))) +
  ∑ k : Fin K, (if k ∈ L then initW N (sz k + 1) else initW N (sz k))

theorem Mlift_mem_colWt {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ}
    (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K)) (I : ∀ k, Fin (sz k) → Fin n) :
    Mlift h lam sg sz hsz L I ∈ dualWeyl ℤ N N (colWt h lam sg sz L) := by
  have hlp : ∀ (s : ℕ) (hr : s ≤ N) (hc : s ≤ N), lpMinor ℤ s hr hc ∈ dualWeyl ℤ N N (initW N s) :=
    fun s hr hc => initMinor_mem (Fin.castLE hr) hc
  unfold Mlift colWt
  apply dualWeyl_mul
  · unfold C0
    refine prod_memZ Finset.univ _ _ fun i _ => ?_
    exact dualWeyl_mul (ite_pow_memZ _ _ (hlp _ _ _) _) (ite_pow_memZ _ _ (initMinor_mem _ _) _)
  · refine prod_memZ Finset.univ _ _ fun k _ => ?_
    split_ifs
    · unfold lif
      exact initMinor_mem _ _
    · unfold unl
      exact initMinor_mem _ _

theorem lam_natW_val {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (t : ℕ) (ht : t < N) :
    ((lam.natW ⟨t, ht⟩ : ℕ) : ℤ) = lam.w ⟨t, ht⟩ - lam.w ⟨n, by omega⟩ := by
  subst h
  have hds : lam.detShift = lam.w ⟨n, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dite_eq_left (by omega)]
    exact congrArg lam.w (Fin.ext (by simp))
  have hle : lam.w ⟨n, by omega⟩ ≤ lam.w ⟨t, ht⟩ :=
    lam.anti (Fin.le_iff_val_le_val.mpr (by show t ≤ n; omega))
  unfold DomWeight.natW
  rw [hds]
  omega

theorem lam_detShift {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) :
    lam.detShift = lam.w ⟨n, by omega⟩ := by
  subst h
  unfold DomWeight.detShift
  rw [dite_eq_left (by omega)]
  exact congrArg lam.w (Fin.ext (by simp))

theorem sg_detShift {n : ℕ} (sg : DomWeight n) (hn : 0 < n) :
    sg.detShift = sg.w ⟨n - 1, by omega⟩ := by
  unfold DomWeight.detShift
  rw [dite_eq_left hn]

theorem aLast_val {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (hn : 0 < n) :
    (((aa h lam sg ⟨n - 1, by omega⟩).toNat : ℕ) : ℤ) = sg.w ⟨n - 1, by omega⟩ - lam.w ⟨n, by omega⟩ := by
  have h2 := (hI ⟨n - 1, by omega⟩).2
  have e : lam.w ⟨(⟨n - 1, by omega⟩ : Fin n).1 + 1, by omega⟩ = lam.w ⟨n, by omega⟩ :=
    congrArg lam.w (Fin.ext (by simp only; omega))
  unfold aa
  omega

theorem b_val {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (t : ℕ) (ht : t < n) :
    (((bb h lam sg ⟨t, ht⟩).toNat : ℕ) : ℤ) = lam.w ⟨t, by omega⟩ - sg.w ⟨t, ht⟩ := by
  have h1 := (hI ⟨t, ht⟩).1
  have e : lam.w ⟨(⟨t, ht⟩ : Fin n).1, by omega⟩ = lam.w ⟨t, by omega⟩ := rfl
  unfold bb
  omega

theorem colWt_eq {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (hshape : shapeDeg sz = sg.natW) (L : Finset (Fin K))
    (hL : GoodL h lam sg sz L) : colWt h lam sg sz L = lam.natW := by
  classical
  funext t
  obtain ⟨tv, htv⟩ := t
  unfold colWt
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]

  have hP : (∑ i : Fin n, (if i.1 + 1 = n then (aa h lam sg i).toNat else 0) * initW N (i.1 + 1) ⟨tv, htv⟩) =
      if hn : n - 1 < n then (aa h lam sg ⟨n - 1, hn⟩).toNat * initW N (n - 1 + 1) ⟨tv, htv⟩ else 0 := by
    rw [← sum_ite_val (fun i : Fin n => (aa h lam sg i).toNat * initW N (i.1 + 1) ⟨tv, htv⟩) (n - 1)]
    apply Finset.sum_congr rfl
    intro i _
    have := i.2
    by_cases hi : i.1 + 1 = n
    · rw [ite_eq_left hi, ite_eq_left (by omega)]
    · rw [ite_eq_right hi, ite_eq_right (by omega), zero_mul]
  have hQ : (∑ i : Fin n, (if i.1 = 0 then (bb h lam sg i).toNat else 0) * initW N (i.1 + 1) ⟨tv, htv⟩) =
      if hn : 0 < n then (bb h lam sg ⟨0, hn⟩).toNat * initW N (0 + 1) ⟨tv, htv⟩ else 0 := by
    rw [← sum_ite_val (fun i : Fin n => (bb h lam sg i).toNat * initW N (i.1 + 1) ⟨tv, htv⟩) 0]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.1 = 0
    · rw [ite_eq_left hi, ite_eq_left hi]
    · rw [ite_eq_right hi, ite_eq_right hi, zero_mul]

  have hK : (∑ k : Fin K, (if k ∈ L then initW N (sz k + 1) else initW N (sz k)) ⟨tv, htv⟩) =
      (Finset.univ.filter fun k => tv < sz k).card +
        (Finset.univ.filter fun k => k ∈ L ∧ sz k = tv).card := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k ∈ L
    · simp only [hk, ite_true, true_and, initW]
      split_ifs <;> omega
    · simp only [hk, ite_false, false_and, initW]
      split_ifs <;> omega
  rw [hP, hQ, hK]
  by_cases htn : tv < n
  · have hn : 0 < n := by omega
    have h1 := card_lt_sz sg sz hshape ⟨tv, htn⟩
    have h2 := hL.2 ⟨tv, htn⟩
    simp only at h1 h2
    rw [h1, h2, dite_eq_left (by omega), dite_eq_left hn]
    have e1 := natW_sg_val sg ⟨tv, htn⟩
    have e2 := lam_natW_val h lam tv htv
    have e3 := aLast_val h lam sg hI hn
    have e4 := b_val h lam sg hI tv htn
    have hw1 : initW N (n - 1 + 1) ⟨tv, htv⟩ = 1 := by simp only [initW]; rw [ite_eq_left (by simp; omega)]
    rw [hw1, mul_one]
    by_cases ht0 : tv = 0
    · subst ht0
      have hw2 : initW N (0 + 1) ⟨0, htv⟩ = 1 := by simp [initW]
      rw [hw2, mul_one, ite_eq_left rfl]
      have := sg.anti (show (⟨0, htn⟩ : Fin n) ≤ ⟨n - 1, by omega⟩ by rw [Fin.le_def]; simp)
      omega
    · have hw2 : initW N (0 + 1) ⟨tv, htv⟩ = 0 := by simp only [initW]; rw [ite_eq_right (by simp; omega)]
      rw [hw2, mul_zero, ite_eq_right ht0]
      omega
  · have htn' : tv = n := by omega
    subst htn'
    have h1 : (Finset.univ.filter fun k => tv < sz k).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro k _; have := hsz k; omega
    have h2 : (Finset.univ.filter fun k => k ∈ L ∧ sz k = tv).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _ hk
      have := hL.1 k hk.1
      rcases sz_lt sg sz hsz hshape k with h3 | h3 <;> omega
    rw [h1, h2]
    have e2 := lam_natW_val h lam tv htv
    have hz : lam.natW ⟨tv, htv⟩ = 0 := by
      have : (⟨tv, htv⟩ : Fin N) = ⟨tv, by omega⟩ := rfl
      omega
    rw [hz]
    have hw1 : ∀ j, j ≤ tv → initW N j ⟨tv, htv⟩ = 0 := by
      intro j hj; simp only [initW]; rw [ite_eq_right (by simp; omega)]
    split_ifs with ha hb
    · rw [hw1 _ (by omega), hw1 _ (by omega)]; simp
    · rw [hw1 _ (by omega)]; simp
    · rw [hw1 _ (by omega)]; simp
    · simp

end PI.WGL.LTE
