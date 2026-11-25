module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionPullback
public import Mathlib.Analysis.Analytic.Polynomial
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMetricPair

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
  ReciprocityTheory.AnForm.M
open BlockResolutionMetricPair

noncomputable section

namespace ResolutionPullback

theorem normRatio_torus {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n)) (A : HermLine ι)
    (hA : A.a = unitDeg k₀) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ‖eval z (map (Int.castRingHom ℂ) f)‖ / A.h z ^ n = ‖eval z' (map (Int.castRingHom ℂ) f)‖ / A.h z' ^ n := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_torus _ hf, A.smul c z' hc, hA, prod_norm_unitDeg, norm_mul, norm_pow, mul_pow]
  have : ‖c k₀‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hc k₀))
  rw [mul_div_mul_left _ _ this]

theorem exp_weight {t : ℝ} (ht : 0 < t) (n : ℕ) :
    Real.exp (-(n : ℝ) * (2 * Real.log t)) = ((t ^ n) ^ 2)⁻¹ := by
  have h : -(n : ℝ) * (2 * Real.log t) = -Real.log ((t ^ n) ^ 2) := by
    rw [Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [h, Real.exp_neg, Real.exp_log (by positivity)]

theorem proof : ResolutionPullback.Statement := by
  intro D K _ _ ι _ Ω _ _ d
  obtain ⟨r, pt, hcov⟩ := exists_finite_nbhd_cover d.R
  refine ⟨atlas d.R pt hcov, bundle d.R pt hcov d.k₀,
    weight d.R pt hcov d.k₀ d.A d.deg d.semipos.1, smoothVol d.R pt hcov d.dV d.vol,
    refine_compatible _ _ _ _ _,
    weight_isSemipositive d.R pt hcov d.k₀ d.A d.deg d.P0 d.normalForm_baseLattice_le_dualSpan_sup_line d.semipos,
    rfl, fun n f hf => ⟨sec d.R pt hcov (Int.castRingHom ℂ) f,
      sec_mem d.R pt hcov d.k₀ (Int.castRingHom ℂ) hf, fun x => ?_⟩⟩
  unfold ptNormSq
  set i := chartIdx (atlas d.R pt hcov) x
  have hx : x ∈ ((atlas d.R pt hcov).chart i).source := Classical.choose_spec ((atlas d.R pt hcov).cover x)
  have horb : SameOrbit (d.R.lift (pt i) x) (blockPt d x) :=
    d.R.compat _ _ x ⟨mem_atlas_source d.R pt hcov hx, d.R.mem_U x⟩
  rw [← normRatio_torus hf d.A d.deg horb]
  have hpos : 0 < d.A.h (d.R.lift (pt i) x) := d.A.pos _ (lift_mem d.R pt hcov hx).1
  rw [sec_apply_of_mem d.R pt hcov (Int.castRingHom ℂ) f hx]
  show ‖_‖ ^ 2 * Real.exp (-(n : ℝ) * (2 * Real.log (d.A.h (d.R.lift (pt i) x)))) = _
  rw [exp_weight hpos, div_pow]
  field_simp

end ResolutionPullback

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
