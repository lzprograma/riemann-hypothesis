module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Mi

variable {D : D7}

section Scalar

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def IsEmbHom (ι : A.V →ₗ[D.host.E] B.V) (s : GA D A →* GA D B) : Prop :=
  ∀ h, EmbRel B A ι (s h) h

end Scalar

end Formalism.IndefR.Mi

end
