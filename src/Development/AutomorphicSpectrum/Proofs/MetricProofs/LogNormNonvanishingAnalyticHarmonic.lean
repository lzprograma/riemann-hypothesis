module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem log_norm_eventually_eq_re_analyticAt :
    ∀ (e : ℕ) (f : (Fin e → ℂ) → ℂ) (z : Fin e → ℂ), AnalyticAt ℂ f z → f z ≠ 0 →
      ∃ Hh : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, Real.log ‖f z'‖ = (Hh z').re := by
  intro e f z hf hz
  refine ⟨fun z' => Complex.log (f z' * (f z)⁻¹) + Complex.log (f z), ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun z' => f z' * (f z)⁻¹) z := hf.mul analyticAt_const
    have h2 : AnalyticAt ℂ Complex.log (f z * (f z)⁻¹) := by
      apply analyticAt_clog
      rw [mul_inv_cancel₀ hz]
      exact Complex.one_mem_slitPlane
    exact (AnalyticAt.comp (f := fun z' => f z' * (f z)⁻¹) (x := z) h2 h1).add analyticAt_const
  · filter_upwards [hf.continuousAt.eventually_ne hz] with z' hz'
    simp only [Complex.add_re, Complex.log_re, norm_mul, norm_inv]
    rw [Real.log_mul (norm_ne_zero_iff.2 hz') (inv_ne_zero (norm_ne_zero_iff.2 hz)), Real.log_inv]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
