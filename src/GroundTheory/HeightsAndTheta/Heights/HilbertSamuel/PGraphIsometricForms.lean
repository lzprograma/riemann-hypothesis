module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphIsometricForms
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphIsometric
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRing
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GraphIsometricForms

theorem proof : GraphIsometricForms.Statement :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hgh hBP ha hh hpl hpr =>
    GraphIsometric.of_forms hP.2.1.1 hgh hBP (GraphChangeOfModel.exists_form_not_mem hP hBP)
      ha hh hpl hpr

end GraphIsometricForms

end GroundTheory.Heights₂.Heights.HilbertSamuel
