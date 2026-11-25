module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Formalism.LocalToGlobal.IndefiniteReal.IsWeilDatum

@[expose] public section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField

namespace Formalism.IndefR.InjectiveDecompositionAction

variable {D : D7}

def SuppAtU (D : D7) (e : AE D) (x : (AE D)ˣ) : Prop :=
  (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1

end Formalism.IndefR.InjectiveDecompositionAction

end
