module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVSec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVSecSt

@[expose] public section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

export PI.VolStabSW (exists_leftInv_of_linIndep secGram_holds)

end PI.VolStabS
