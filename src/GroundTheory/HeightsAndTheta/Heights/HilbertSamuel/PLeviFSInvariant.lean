module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqLevi
public import Mathlib.Analysis.InnerProductSpace.Calculus
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology ComplexConjugate
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi

noncomputable section

namespace LeviFSInvariant

variable {J : Type} [Fintype J]

private def herm (a b : J → ℂ) : ℂ := ∑ p, conj (a p) * b p

private theorem herm_self (a : J → ℂ) : herm a a = (sqSum a : ℂ) := by
  simp only [herm, sqSum, Complex.ofReal_sum, Complex.ofReal_pow]
  exact Finset.sum_congr rfl fun p _ => Complex.conj_mul' (a p)

private theorem herm_swap (a b : J → ℂ) : herm b a = conj (herm a b) := by
  simp only [herm, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

private theorem reInner_sq_add (a b : J → ℂ) :
    ((reInner a b ^ 2 + reInner a (Complex.I • b) ^ 2 : ℝ) : ℂ) = herm a b * herm b a := by
  have hre : (herm a b).re = reInner a b := by
    simp only [herm, Complex.re_sum, reInner_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    exact Finset.sum_congr rfl fun p _ => by ring
  have him : (herm a b).im = -reInner a (Complex.I • b) := by
    simp only [herm, Complex.im_sum, reInner_apply, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [herm_swap a b, Complex.mul_conj, Complex.normSq_apply, hre, him]
  push_cast
  ring

private theorem herm_smul_left (c : ℂ) (a b : J → ℂ) : herm (c • a) b = conj c * herm a b := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun p _ => by ring

private theorem herm_add_right (a b b' : J → ℂ) : herm a (b + b') = herm a b + herm a b' := by
  simp only [herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem herm_add_left (a a' b : J → ℂ) : herm (a + a') b = herm a b + herm a' b := by
  simp only [herm, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

private theorem herm_smul_right (c : ℂ) (a b : J → ℂ) : herm a (c • b) = c * herm a b := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun p _ => by ring

private theorem sqSum_ne_zero {a : J → ℂ} (ha : a ≠ 0) : sqSum a ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  refine ne_of_gt (lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) ?_)
  exact Finset.single_le_sum (f := fun p => ‖a p‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

end LeviFSInvariant


open LeviFSInvariant in
theorem LeviFSInvariant.proof : LeviFSInvariant.Statement := by
  intro M _ a b c μ ha hc
  have hf : (fun u : M → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) = phi := by
    funext u
    simp only [phi, sqSum]
    ring
  have hca : c • a ≠ 0 := smul_ne_zero hc ha
  rw [hf, leviForm_phi (sqSum_ne_zero hca), leviForm_phi (sqSum_ne_zero ha)]
  have hS : sqSum (c • a) = ‖c‖ ^ 2 * sqSum a := by
    apply Complex.ofReal_injective
    rw [← herm_self, herm_smul_left, herm_smul_right, herm_self]
    push_cast
    rw [← Complex.conj_mul']
    ring
  have key : ∀ a b : M → ℂ,
      ((sqSum a * sqSum b - (reInner a b ^ 2 + reInner a (Complex.I • b) ^ 2) : ℝ) : ℂ) =
        herm a a * herm b b - herm a b * herm b a := by
    intro a b
    rw [Complex.ofReal_sub, Complex.ofReal_mul, reInner_sq_add, herm_self, herm_self]
  have hN' : herm (c • a) (c • a) * herm (c • b + μ • a) (c • b + μ • a) -
      herm (c • a) (c • b + μ • a) * herm (c • b + μ • a) (c • a) =
      (((‖c‖ ^ 2) ^ 2 : ℝ) : ℂ) * (herm a a * herm b b - herm a b * herm b a) := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right]
    push_cast
    rw [← Complex.conj_mul']
    ring
  have hN : sqSum (c • a) * sqSum (c • b + μ • a) -
      (reInner (c • a) (c • b + μ • a) ^ 2 + reInner (c • a) (Complex.I • (c • b + μ • a)) ^ 2) =
      (‖c‖ ^ 2) ^ 2 * (sqSum a * sqSum b - (reInner a b ^ 2 + reInner a (Complex.I • b) ^ 2)) := by
    apply Complex.ofReal_injective
    rw [key, Complex.ofReal_mul, key, hN']
  rw [hN, hS]
  have hc2 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  field_simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
