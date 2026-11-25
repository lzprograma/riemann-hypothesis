module

public import Formalism.PeriodIntegrals.QmStar
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerProductCast.OfFnProdIntCast

@[expose] public section

theorem quantum_minor_star : PI.QmStar :=
  PI.UnitaryGroupMassFormula.QmStar.qmStar_of quantum_minor_row_form
