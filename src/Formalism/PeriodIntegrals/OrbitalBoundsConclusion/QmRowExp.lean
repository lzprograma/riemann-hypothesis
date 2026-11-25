module

public import Formalism.PeriodIntegrals.QmRowExp
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowExpansionMinor.FirstColumnSplitBijective

@[expose] public section

theorem quantum_minor_row_expansion : PI.QmRowExp := PI.qmRowExp_of_rowForm quantum_minor_row_form
