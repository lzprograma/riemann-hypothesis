module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMetricPair
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanDensChartSum
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionPotentials
public import Mathlib.Analysis.Analytic.Polynomial
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AInterpSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMetricPair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamStA

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
  ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

theorem ResolutionMetricPair.isSmoothMetric_interp {κ : Type} [Fintype κ] {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (h₀ : IsSmoothMetric m₀) (h₁ : IsSmoothMetric m₁) (t : ℝ) : IsSmoothMetric (interp m₀ m₁ t) := by
  show ContDiffOn ℝ _ (fun z => m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) _
  exact (h₀.rpow_const_of_ne fun z hz => (m₀.pos z hz).ne').mul
    (h₁.rpow_const_of_ne fun z hz => (m₁.pos z hz).ne')

open BlockResolutionMetricPair in
theorem ResolutionMetricPair.proof (h : BergmanDensChartSum.Statement) : ResolutionMetricPair.Statement := by
  intro D Ω _ _ κ _ d m₁ P0₁ hm₁ hP0₁ hsp₁
  obtain ⟨r, pt, hcov⟩ := exists_finite_nbhd_cover d.R
  have hdeg : ∀ m : ConeMetric ℂ (Ix κ), (HermLine.ofCone m).a = unitDeg () := fun _ => by
    funext k; cases k; rfl
  refine ⟨atlas d.R pt hcov, bundle d.R pt hcov (),
    weight d.R pt hcov () (HermLine.ofCone d.m) (hdeg d.m) (gbamix_smoothHerm_ofCone d.smooth),
    weight d.R pt hcov () (HermLine.ofCone m₁) (hdeg m₁) (gbamix_smoothHerm_ofCone hm₁),
    smoothVol d.R pt hcov d.dV d.vol, fun _ b => sec d.R pt hcov (algebraMap ℚ ℂ) b,
    refine_compatible _ _ _ _ _,
    weight_isSemipositive d.R pt hcov () (HermLine.ofCone d.m) (hdeg d.m) d.P0
      d.normalForm_baseLattice_le_dualSpan_sup_line d.semipos,
    weight_isSemipositive d.R pt hcov () (HermLine.ofCone m₁) (hdeg m₁) P0₁ hP0₁ hsp₁, rfl,
    fun n b hb => sec_mem d.R pt hcov () (algebraMap ℚ ℂ) fun m hm k => by
      cases k
      have hdegm := hb (mem_support_iff.1 hm)
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_sigma, blockDeg] using hdegm,
    fun y => ?_, fun s _ g hg => ?_⟩
  · obtain ⟨c, hc, hz⟩ := lift_chartIdx d.R pt hcov y
    have hzc : d.R.lift (pt (chartIdx (atlas d.R pt hcov) y)) y = c () • resPt d y := by
      rw [hz]; funext p; rfl
    have hx : y ∈ ((atlas d.R pt hcov).chart (chartIdx (atlas d.R pt hcov) y)).source :=
      Classical.choose_spec ((atlas d.R pt hcov).cover y)
    refine ⟨c (), hc (), fun n b _ => ?_, ?_, ?_⟩
    · show sec d.R pt hcov (algebraMap ℚ ℂ) b (chartIdx (atlas d.R pt hcov) y) y = _
      rw [sec_apply_of_mem d.R pt hcov (algebraMap ℚ ℂ) b hx, hzc]
    · show 2 * Real.log (d.m.ρ (d.R.lift (pt _) y)) = _
      rw [hzc]
    · show 2 * Real.log (m₁.ρ (d.R.lift (pt _) y)) = _
      rw [hzc]
  · refine bergmanDens_integral_eq d.R pt hcov h () d.dV d.vol _ (resPot d (interp d.m m₁ s))
      (isPotential_resPot d (isSmoothMetric_interp d.smooth hm₁ s)) (fun _ => rfl) (fun j y hy => ?_) g hg
    filter_upwards [((atlas d.R pt hcov).chart j).open_target.mem_nhds hy] with y' hy'
    have hne := gaamix_ne_zero_of_mcPts (d.R.mem (pt j) _ (mem_atlas_target d.R pt hcov hy').2)
    have h0 := d.m.pos _ hne
    have h1 := m₁.pos _ hne
    simp only [Function.comp_apply, Weight.lerp, weight, resPot, HermLine.ofCone]
    rw [interp_rho, Real.log_mul (Real.rpow_pos_of_pos h0 _).ne' (Real.rpow_pos_of_pos h1 _).ne',
      Real.log_rpow h0, Real.log_rpow h1]
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
