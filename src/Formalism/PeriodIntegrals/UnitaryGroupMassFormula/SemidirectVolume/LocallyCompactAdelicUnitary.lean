module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAFTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TensTopOf

@[expose] public section

namespace PI.VolSemiDirect.W.Lc

theorem tensor_adele_topology_holds : TensTop := tensTop_of PI.VolStabSW.TopoAF.afTop_holds

end PI.VolSemiDirect.W.Lc
