module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplitLat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.DenomHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllOfParts

@[expose] public section

noncomputable section

namespace MassDataIdxSteps

open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting

theorem stRed_of_embP {D : D7} (X : HidaSetting D) (p : TypX X) (hE : EmbP X p) : StRed X p :=
  stRed_of_emb X p hE (_root_.MassDataIdxSteps.latBasisAll_holds' X p)

end MassDataIdxSteps
