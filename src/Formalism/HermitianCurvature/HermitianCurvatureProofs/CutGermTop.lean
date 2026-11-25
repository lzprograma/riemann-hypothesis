module

public import Formalism.HermitianCurvature.StatementTBB

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def omT (p : KB.Pl P Wp Wq) (N : ℕ) (Q : C.LPt) : ℝ :=
  √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(Top.wPt (TBB.TTp p) P.r Q ^ N)

end place

def epsT (s : ℕ) : ℂ := (-1) ^ (s + 1)

end

end Formalism.FourierDecayAlt.P.CutBP.GT
