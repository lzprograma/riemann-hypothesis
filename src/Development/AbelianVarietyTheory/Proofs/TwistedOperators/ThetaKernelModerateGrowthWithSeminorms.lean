module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix

namespace GlobalTheory.KernelSeminorm

theorem thetaGrowth_onObjects : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D :=
  fun D => GlobalTheory.KernelSeminorm.thetaGrowth D

end GlobalTheory.KernelSeminorm
