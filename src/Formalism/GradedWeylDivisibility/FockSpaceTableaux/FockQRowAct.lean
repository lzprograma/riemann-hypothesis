module

public import Formalism.GradedWeylDivisibility.StatementE
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingRowAction

@[expose] public section

namespace Formalism.GradedWeylDivisibility

theorem fock_space_row_action : FockQRowAct := by
  intro r n g P Q
  exact @Formalism.L2.G.Model.TS.fock_pairing_row_action ℚ inferInstance r n g P Q

end Formalism.GradedWeylDivisibility
