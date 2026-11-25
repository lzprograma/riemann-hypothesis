module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtSizePtG
public import Formalism.HermitianCurvature.StatementTBB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX_UwTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGCongr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGInt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbGermRateLowBOfParts
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

namespace GLG

def PP (m : ℕ) (h : C.LPt) (x Dv : ℂ) : Option ℂ → C.LPt
  | none => h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * Dv)]
  | some z => h ++ [(m + 2, z)]

end GLG

namespace GLG

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def lam (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (w : List C.Letter) (a : C.LPt) : ℝ :=
  √(TBB.nPt P.k P.r (TBB.TTp p) a) / √(TBB.normC nn w)

end GLG


end

end Formalism.FourierDecayAlt.P.CutBP
