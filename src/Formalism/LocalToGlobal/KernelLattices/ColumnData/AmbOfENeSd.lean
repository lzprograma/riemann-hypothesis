module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdOKP

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker.Cd

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Host Formalism.FrobeniusOrbits

alias Base.stdOK := _root_.Formalism.L2.Ker.Cd.IntegralLatticeDensity.SO.stdOK



end Formalism.L2.Ker.Cd
