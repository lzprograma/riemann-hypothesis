module

public import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct InnerProductSpace
open IsDedekindDomain NumberField MeasureTheory

namespace Formalism.IndefR.RecTie

section FromLinks

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end FromLinks

end Formalism.IndefR.RecTie

end
