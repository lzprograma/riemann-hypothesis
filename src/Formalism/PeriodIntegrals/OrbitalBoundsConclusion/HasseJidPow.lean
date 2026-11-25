module

public import Formalism.PeriodIntegrals.HasseJidPow
public import Formalism.PeriodIntegrals.HassePresH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseDerivativeFiltration.HasseMemHfr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseJacobsonPowers.SfrMulMemJHfr

@[expose] public section

theorem hasse_jid_power : PI.HasseJidPow := PI.HJP.hasseJidPow_of _root_.PI.UnitaryGroupMassFormula.HassePresH.main
