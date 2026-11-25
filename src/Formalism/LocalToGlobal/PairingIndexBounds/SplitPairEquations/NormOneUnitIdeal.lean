module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdealAlt
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.NormOneUnitIdeal

@[expose] public section

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.BasicNotions

variable (D : D7)

theorem norm_one_unit_ideal : NormOneUnitIdeal D :=
  Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.norm_one_unit_ideal (Formalism.L2.Ker.Car.ofRec D)

theorem detSmul : DetSmul D :=
  Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.detSmul (Formalism.L2.Ker.Car.ofRec D)

end Formalism.L2.PairingIndexBounds.Eq

end
