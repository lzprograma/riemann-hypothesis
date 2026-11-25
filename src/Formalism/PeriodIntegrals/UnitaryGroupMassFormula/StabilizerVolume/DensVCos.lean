module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVCos
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVGen
import Aesop.Main
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVCos

@[expose] public section

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Set Filter

export PI.VolStabSW (hasDens_zero hasDens_sum DensCosB IsCOBasis isCompact_cos integrable_cos)

namespace HasDens
export PI.VolStabSW.HasDens (add)
end HasDens

section Cos

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

export PI.VolStabSW (densLC_of_cosB)

end Cos

end PI.VolStabS
