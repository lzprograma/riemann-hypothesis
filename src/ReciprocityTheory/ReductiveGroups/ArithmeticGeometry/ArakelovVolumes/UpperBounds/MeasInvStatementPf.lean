module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Lemmata.GeneralBFactForm.Imports
public import Mathlib.RingTheory.Complex
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem measInv_holds : MeasInvStatement (E := E) := GlobalTheory.FrameMeasureClosed.measInv_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
