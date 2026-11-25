module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftPhaseRule.ReflectionColumnDualIsotropic
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace PI.QnRT

variable {k r : ℕ}

lemma e_ne_es (l : Fin r) : eI k r l ≠ esI k r l := by
  apply _root_.Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.e_ne_es <;> assumption

private lemma tau_val_lemma (i : Fin (2 * r + k + 1)) :
    (WeylGroupFacts.tau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl

lemma tau_e (l : Fin r) : WeylGroupFacts.tau k r (eI k r l) = esI k r l := by
  apply _root_.Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.tau_e <;> assumption

lemma tau_es (l : Fin r) : WeylGroupFacts.tau k r (esI k r l) = eI k r l := by
  apply _root_.Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.tau_es <;> assumption

lemma sgn_e (l : Fin r) : WeylGroupFacts.sgn k r (eI k r l) = 1 := by
  apply _root_.Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.sgn_e <;> assumption

lemma sgn_es (l : Fin r) : WeylGroupFacts.sgn k r (esI k r l) = 1 := by
  apply _root_.Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.sgn_es <;> assumption

lemma w_col_e (l : Fin r) (a : ℂ) (s : Fin (2 * r + k + 1)) :
    w1 k r l a s (eI k r l) = if s = esI k r l then a else 0 := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold w1
  by_cases h : s = esI k r l
  · subst h
    simp
  · simp [h, hne]

lemma w_col_es (l : Fin r) (a : ℂ) (s : Fin (2 * r + k + 1)) :
    w1 k r l a s (esI k r l) = if s = eI k r l then (star a)⁻¹ else 0 := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold w1
  by_cases h : s = eI k r l
  · subst h
    simp [hne, hne.symm]
  · simp [h, hne.symm]

lemma w_col_other (l : Fin r) (a : ℂ) (s p : Fin (2 * r + k + 1)) (hp1 : p ≠ eI k r l)
    (hp2 : p ≠ esI k r l) : w1 k r l a s p = if s = p then 1 else 0 := by
  apply _root_.Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.reflection_off_support <;> assumption

lemma w_row_other (l : Fin r) (a : ℂ) (s q : Fin (2 * r + k + 1)) (hs1 : s ≠ eI k r l)
    (hs2 : s ≠ esI k r l) : w1 k r l a s q = if s = q then 1 else 0 := by
  apply _root_.Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.reflection_off_support_row <;> assumption

private lemma tau_tau_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.tau k r (WeylGroupFacts.tau k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [tau_val_lemma]
  split_ifs <;> omega

private lemma sgn_tau_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r i) = WeylGroupFacts.sgn k r i := by
  have hi := i.isLt
  unfold WeylGroupFacts.sgn
  simp only [tau_val_lemma]
  split_ifs <;> first | rfl | omega

private lemma sgn_sq_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r i * WeylGroupFacts.sgn k r i = 1 := by
  unfold WeylGroupFacts.sgn
  split_ifs <;> norm_num

private lemma sgn_ne_zero' (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r i ≠ 0 := by
  unfold WeylGroupFacts.sgn
  split_ifs <;> norm_num

private lemma hpk_eq_lemma (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = WeylGroupFacts.tau k r i then WeylGroupFacts.sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk WeylGroupFacts.sgn
  simp only [Fin.ext_iff, tau_val_lemma]
  split_ifs <;> first | rfl | omega

private lemma hpk_col_lemma (x y : Fin (2 * r + k + 1)) :
    Hpk k r x y = if x = WeylGroupFacts.tau k r y then WeylGroupFacts.sgn k r y else 0 := by
  rw [hpk_eq_lemma]
  by_cases h : x = WeylGroupFacts.tau k r y
  · subst h
    simp [tau_tau_lemma, sgn_tau_lemma]
  · rw [ite_eq_right h, ite_eq_right]
    intro h'
    apply h
    rw [h', tau_tau_lemma]

private lemma hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [hpk_eq_lemma, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, tau_tau_lemma, sgn_tau_lemma]
  by_cases h : i = j
  · subst h
    simp [sgn_sq_lemma]
  · simp [h, Ne.symm h]

private lemma conjTranspose_mul_Hpk_mul_apply (A : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (Aᴴ * Hpk k r * A) p q = ∑ y, star (A (WeylGroupFacts.tau k r y) p) * WeylGroupFacts.sgn k r y * A y q := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, hpk_col_lemma, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma w_fix (l : Fin r) (a : ℂ) (x : Fin (2 * r + k + 1)) (h1 : x ≠ eI k r l) (h2 : x ≠ esI k r l) :
    w1 k r l a *ᵥ bvec x = bvec x := by
  funext p
  simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact w_col_other l a p x h1 h2

lemma w_mul_mem (l : Fin r) (a : ℂ) (ha : a ≠ 0) (g₁ : Mx k r) (hg : g₁ ∈ Glev k r l.succ) :
    w1 k r l a * g₁ ∈ Glev k r l.castSucc := by
  apply Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.wg_glev <;> assumption

def dg (l : Fin r) (u v : ℂ) : Mx k r :=
  diagonal (fun p => if p = eI k r l then u else if p = esI k r l then v else 1)

lemma w_mul_dg (l : Fin r) (a u : ℂ) :
    w1 k r l a * dg l u (star u)⁻¹ = w1 k r l (a * u) := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold dg
  ext p q
  rw [Matrix.mul_diagonal]
  by_cases hq1 : q = eI k r l
  · subst hq1
    rw [w_col_e, w_col_e]
    by_cases hp : p = esI k r l <;> simp [hp]
  by_cases hq2 : q = esI k r l
  · subst hq2
    rw [w_col_es, w_col_es]
    by_cases hp : p = eI k r l <;> simp [hp, hne.symm, mul_comm]
  rw [w_col_other l a p q hq1 hq2, w_col_other l (a * u) p q hq1 hq2]
  simp [hq1, hq2]

private lemma apply_eq_ite_of_mulVec_bvec_eq (g : Mx k r) (v : Fin (2 * r + k + 1)) (h : g *ᵥ bvec v = bvec v)
    (q : Fin (2 * r + k + 1)) : g q v = if q = v then 1 else 0 := by
  have h' := congrFun h q
  simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h'
  exact h'

private lemma apply_eq_ite_of_isometry_of_tau_column (g : Mx k r) (hg : gᴴ * Hpk k r * g = Hpk k r) (p : Fin (2 * r + k + 1))
    (h : ∀ q, g q (WeylGroupFacts.tau k r p) = if q = WeylGroupFacts.tau k r p then 1 else 0) (q : Fin (2 * r + k + 1)) :
    g p q = if p = q then 1 else 0 := by
  have e := congrFun (congrFun hg q) (WeylGroupFacts.tau k r p)
  rw [conjTranspose_mul_Hpk_mul_apply, hpk_col_lemma, tau_tau_lemma] at e
  simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, tau_tau_lemma] at e
  have hs := sgn_ne_zero' (k := k) (r := r) (WeylGroupFacts.tau k r p)
  by_cases hpq : p = q
  · subst hpq
    rw [ite_eq_left rfl] at e
    have h1 : star (g p p) = 1 := mul_right_cancel₀ hs (e.trans (one_mul _).symm)
    have h2 := congrArg star h1
    rw [star_star, star_one] at h2
    simp [h2]
  · rw [ite_eq_right (Ne.symm hpq)] at e
    have h1 : star (g p q) = 0 := (mul_eq_zero.mp e).resolve_right hs
    rw [ite_eq_right hpq]
    exact star_eq_zero.mp h1

lemma dg_comm (l : Fin r) (u v : ℂ) (g₁ : Mx k r) (hg : g₁ ∈ Glev k r l.succ) :
    dg l u v * g₁ = g₁ * dg l u v := by
  have hl := l.isLt
  simp only [Glev, Set.mem_setOf_eq] at hg
  obtain ⟨hU, hfix⟩ := hg
  have hU' : g₁ᴴ * Hpk k r * g₁ = Hpk k r := hU
  have hfe := hfix l (by simp)
  have ce := apply_eq_ite_of_mulVec_bvec_eq g₁ _ hfe.1
  have ces := apply_eq_ite_of_mulVec_bvec_eq g₁ _ hfe.2
  have re : ∀ q, g₁ (eI k r l) q = if eI k r l = q then 1 else 0 :=
    apply_eq_ite_of_isometry_of_tau_column g₁ hU' _ (by rw [tau_e]; exact ces)
  have res : ∀ q, g₁ (esI k r l) q = if esI k r l = q then 1 else 0 :=
    apply_eq_ite_of_isometry_of_tau_column g₁ hU' _ (by rw [tau_es]; exact ce)
  unfold dg
  ext p q
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hp1 : p = eI k r l
  · subst hp1
    rw [re q]
    by_cases hq : eI k r l = q
    · subst hq
      simp [mul_comm]
    · simp [hq]
  by_cases hp2 : p = esI k r l
  · subst hp2
    rw [res q]
    by_cases hq : esI k r l = q
    · subst hq
      simp [mul_comm]
    · simp [hq]
  by_cases hq1 : q = eI k r l
  · subst hq1
    rw [ce p]
    simp [hp1]
  by_cases hq2 : q = esI k r l
  · subst hq2
    rw [ces p]
    simp [hp2]
  simp [hp1, hp2, hq1, hq2]

lemma exp_diag2 (l : Fin r) (x y : ℂ) :
    NormedSpace.exp (diagonal (fun p => if p = eI k r l then x else if p = esI k r l then y else 0) : Mx k r) =
      dg l (Complex.exp x) (Complex.exp y) := by
  rw [Matrix.exp_diagonal]
  unfold dg
  congr 1
  funext p
  first
    | simp only [Pi.exp_def]
  split_ifs <;> simp [Complex.exp_eq_exp_ℂ]

end PI.QnRT
