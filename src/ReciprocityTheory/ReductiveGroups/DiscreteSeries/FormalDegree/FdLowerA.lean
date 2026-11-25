module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdUpperA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.CategoryTheory.Countable
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KinstSecondCountable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PBridge
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.AdKMeasurePreserving

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdl_inner_continuous {ε : Fin n → Bool} (lam : Fin n → ℝ) {Λ : Fin n → ℝ} (T : KType ε Λ) (u v : T.V) :
    Continuous (fun z : PCoord ε → ℂ => ⟪u, fF ε lam T (pmat z) v⟫_ℂ) := by
  have hpm : Continuous (fun z : PCoord ε → ℂ => pmat z) := by
    first
    | (refine continuous_pi fun a => continuous_pi fun b => ?_
       unfold pmat
       split_ifs <;> fun_prop)
  have hmk : Continuous fun k : KG ε => toMK k := by
    first
    | fun_prop
  have hM : Continuous fun p : (PCoord ε → ℂ) × KG ε => toMK p.2⁻¹ * pmat p.1 * toMK p.2 :=
    ((hmk.comp continuous_snd.inv).matrix_mul (hpm.comp continuous_fst)).matrix_mul
      (hmk.comp continuous_snd)
  have hPh : Continuous fun p : (PCoord ε → ℂ) × KG ε => Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2) :=
    continuous_potential_comp lam hM (fun p => ⟨adK p.2⁻¹ p.1, conj_pmat_eq_adK p.2 p.1⟩)
  have hop : Continuous fun p : (PCoord ε → ℂ) × KG ε => T.op p.2 :=
    (continuous_subtype_val.comp T.cont).comp continuous_snd
  have hF : Continuous fun p : (PCoord ε → ℂ) × KG ε =>
      ((Real.exp (-Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2)) : ℝ) : ℂ) *
        (⟪T.op p.2 T.w, v⟫_ℂ * ⟪u, T.op p.2 T.w⟫_ℂ) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hPh.neg)).mul
      (((hop.clm_apply continuous_const).inner continuous_const).mul
        (continuous_const.inner (hop.clm_apply continuous_const)))
  have := CompactHaarProbability.dk_isProb ε
  have hI := continuous_parametric_integral_of_continuous (μ := dk ε)
    (f := fun (z : PCoord ε → ℂ) (k : KG ε) =>
      ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) *
        (⟪T.op k T.w, v⟫_ℂ * ⟪u, T.op k T.w⟫_ℂ)) hF isCompact_univ
  simp only [Measure.restrict_univ] at hI
  have he : (fun z : PCoord ε → ℂ => ⟪u, fF ε lam T (pmat z) v⟫_ℂ) = fun z =>
      ((Module.finrank ℂ T.V : ℝ) : ℂ) *
        ∫ k, ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) *
          (⟪T.op k T.w, v⟫_ℂ * ⟪u, T.op k T.w⟫_ℂ) ∂(dk ε) := by
    funext z
    exact inner_fF_eq_integral lam T z u v
  rw [he]
  exact continuous_const.mul hI

theorem fdl_lint_pi_ofReal {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : ∀ i, E i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (h0 : ∀ i x, 0 ≤ f i x) :
    ∫⁻ x, ENNReal.ofReal (∏ i, f i (x i)) ∂(Measure.pi μ) = ∏ i, ENNReal.ofReal (∫ x, f i x ∂(μ i)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hf)
      (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => h0 i (x i)))),
    integral_fintype_prod_eq_prod]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (h0 i))

theorem fdl_cgauss {c : ℝ} (hc : 0 < c) : ∫ z : ℂ, Real.exp (-(c * ‖z‖ ^ 2)) = Real.pi / c := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) hc
  simp only [neg_mul, Complex.finrank_real_complex] at h
  rw [h]
  norm_num

theorem fdl_cgauss_int {c : ℝ} (hc : 0 < c) : Integrable (fun z : ℂ => Real.exp (-(c * ‖z‖ ^ 2))) := by
  apply Integrable.of_integral_ne_zero
  rw [fdl_cgauss hc]
  exact (div_pos Real.pi_pos hc).ne'

theorem fdl_wab_zero_pos {ε : Fin n → Bool} (ab : PCoord ε) : 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := by
  exact ReciprocityTheory.ChartRestriction.DS.fdU_wab_zero_pos ab

theorem fdl_gauss (ε : Fin n → Bool) :
    ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) = ENNReal.ofReal (PiW ε 0) := by
  apply ReciprocityTheory.ChartRestriction.DS.fdU_lintegral_gauss <;> assumption

end ReciprocityTheory.ChartRestriction.DS
