module

public import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
public import Formalism.LocalToGlobal.Divisibility.HeckeRI
public import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open scoped InnerProductSpace
open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.MiS
open Formalism Formalism.IndefR

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A)

def OpsUnit (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ) : Prop :=
  (∀ e ∈ X.EEl true, V e ∈ X.EEl true ∧ ‖V e‖ = ‖e‖) ∧
    ∀ u x, fnorm ((fc X.zs).Dc.Xc u Bs.v0) ((U u).mulVec x) = fnorm ((fc X.zs).Dc.Xc u Bs.v0) x

variable {X cr cv}

end Gen

end GlobalTheory.MiS

end
