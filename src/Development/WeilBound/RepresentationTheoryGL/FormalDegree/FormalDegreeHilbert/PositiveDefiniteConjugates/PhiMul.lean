module

import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.PhiMul
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts

@[expose] public section

noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem phiMul : PhiMul := by
  apply _root_.CompanionTheory.RgFd.phiMul

end PositivityTheory.RgFd
