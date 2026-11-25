module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilUnr
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel

@[expose] public section

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Theta

structure AllTied (D : D7) (X : ThetaX D) (A : TH.ProvA) where

  T : ThetaTied D X

  W : WeilTied D X T

  real : RealTied D

end Formalism.L2.Theta

end
