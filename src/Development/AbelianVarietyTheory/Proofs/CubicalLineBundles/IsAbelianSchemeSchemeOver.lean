module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DiagZEqNegAddY
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

theorem GlobalTheory.WeierstrassCurve.isAbelianScheme_schemeOver :
    ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ →
      ∀ [GrpObj (schemeOver W)], IsCommMonObj (schemeOver W) → IsAbelianScheme (schemeOver W) := by
  intro R _ W hΔ _ hc
  have hs := smoothOfRelativeDimension_toSpec_of_isUnit W hΔ
  exact ⟨hc, SmoothOfRelativeDimension.smooth 1 (toSpec W), isProper_toSpec W,
    geometricallyConnected_toSpec W⟩
