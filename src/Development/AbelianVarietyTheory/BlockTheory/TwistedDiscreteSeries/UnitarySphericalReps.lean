module

public import Mathlib.Basic.Complex.Basic
public import Formalism.LocalRingCardinality.DataHost
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.LFun

def IsPosReal (z : ℂ) : Prop := z.im = 0 ∧ 0 < z.re

variable {D : D7}




end GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps

end
