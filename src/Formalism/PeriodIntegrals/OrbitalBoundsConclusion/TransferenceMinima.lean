module

public import Formalism.PeriodIntegrals.Transference
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.KeySmall
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.NumericMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Poisson
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Skeleton

@[expose] public section

theorem transference_successive_minima : PI.TransferenceMinima :=
  PI.Tr.transferenceMinima_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall
