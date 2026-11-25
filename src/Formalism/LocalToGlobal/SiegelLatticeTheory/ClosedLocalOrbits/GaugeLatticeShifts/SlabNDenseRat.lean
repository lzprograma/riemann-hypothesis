module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipBasis
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ColsDim
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipReal
import Mathlib.Tactic.TypeStar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipRat

@[expose] public section

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section RatEl

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

end RatEl
