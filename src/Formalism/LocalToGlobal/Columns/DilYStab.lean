module

public import Formalism.LocalToGlobal.Columns.DecoratedFrameDiagonalTwistDecoration
public import Formalism.LocalToGlobal.Columns.RecChainYUnfPol

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Pairs

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word} {m2 j : ℕ}


variable (W cst L u m2 j) in
abbrev PtY (b : L.β j) : Type := (cplAt W sel mu cst L u m2 j b).Pts

@[reducible] def ptYAct (b : L.β j) : MulAction ((chFY W sel mu cst L u m2 j).mem b).G (PtY W cst L u m2 j b) := ((chFY W sel mu cst L u m2 j).mem b).actD

attribute [local instance] ptYAct


end Pairs

end Formalism.L2.Col
