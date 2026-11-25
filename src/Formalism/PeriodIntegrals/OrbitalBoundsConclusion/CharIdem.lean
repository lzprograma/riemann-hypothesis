module

public import Formalism.PeriodIntegrals.CharIdem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Central
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.CoeffMulCharIdem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Scalar

@[expose] public section

theorem orthogonalCentral : PI.CharIdem.CharIdem :=
  PI.CharIdemW.charIdem_of PI.CharIdemW.central PI.CharIdemW.scalar
    (PI.CharIdemW.mulEq_of PI.CharIdemW.scalar)
