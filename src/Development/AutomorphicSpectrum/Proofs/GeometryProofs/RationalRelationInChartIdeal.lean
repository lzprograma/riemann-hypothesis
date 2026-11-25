module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRing
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPC
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartDehom

theorem map_mem_chartIdeal : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ G : MvPolynomial (Σ k, J k) ℚ,
    aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G = (0 : Ω) →
    map (algebraMap ℚ ℂ) G ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by
  apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.ker_le_chart

end GlobalTheory.CompanionTheory.Ar.ChartDehom
