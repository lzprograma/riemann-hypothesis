module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt

@[expose] public section



section
noncomputable section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
namespace GlobalTheory.ShareOn
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn
def ModelStatement : Prop := _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x hx ι p _ _ => ∀ i, ModelAt p i (Fm.parT x hx ι).TO
def SharedWeightStatement : Prop := _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ ι p _ _ => ∀ i,
  ShareW p i (1 / (4 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.k) ^ 3))
def BadWeightStatement : Prop := _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ ι p _ _ => ∀ i,
  BadW p i (Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))))
end GlobalTheory.ShareOn
end
end
