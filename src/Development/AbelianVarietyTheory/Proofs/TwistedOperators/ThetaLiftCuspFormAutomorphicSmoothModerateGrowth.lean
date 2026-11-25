module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RapidDecayLift
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelModerateGrowthWithSeminormsStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

namespace GlobalTheory.Chain.LiftReg

theorem liftProps_obj : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.LiftProps D :=
  fun hP D => liftProps_of_rapidDecay hP D (GlobalTheory.KernelSeminorm.thetaGrowth_onObjects D)

end GlobalTheory.Chain.LiftReg
