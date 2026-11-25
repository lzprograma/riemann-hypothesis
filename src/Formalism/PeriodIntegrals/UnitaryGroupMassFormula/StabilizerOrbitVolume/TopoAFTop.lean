module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TensTopOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

@[expose] public section

namespace PI.VolStabSW.TopoAF

theorem afTop_holds : PI.VolSemiDirect.W.Lc.AFTop := fun _ _ _ =>
  ⟨inferInstance, inferInstance, inferInstance⟩

end PI.VolStabSW.TopoAF
