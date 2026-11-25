module

public import Formalism.SharpRestriction.Divisibility.PrinLevClass

@[expose] public section

noncomputable section

open NumberField MvPolynomial Finset
open scoped BigOperators

namespace Formalism.MainNotions.LatticeTransfer

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

def wt (Tau : Type) [Fintype Tau] (N : ℕ) : Vm Tau N → ℕ
  | Sum.inl _ => 1
  | Sum.inr (_, k) => k

section One
variable (D : D7) (XD : DivX D)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

end One

end Formalism.MainNotions.LatticeTransfer

end
