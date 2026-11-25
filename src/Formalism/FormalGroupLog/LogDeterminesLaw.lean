module

public import Formalism.FormalGroupLog.Statement
public import Formalism.FormalGroupLog.FormalGroupLogProofs.HomPsSubstMvSubst
import Mathlib.Tactic.Linter.Style

@[expose] public section

namespace Formalism.G

theorem homComp : HomComp := by
  apply Formalism.G.homComp_statement
theorem logIffHomGa : LogIffHomGa := by
  apply Formalism.G.log_iff_hom_additive
alias substInjective := _root_.Formalism.G.substInjective_statement

end Formalism.G
