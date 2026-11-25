module

import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff
public import Formalism.LocalRingCardinality.DataLevel

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField Formalism.UG

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem isUnit_det_gram0 (sp : Spaces R F E) : IsUnit sp.gram0.det := by
  apply GlobalTheory.OverCompare.gram_matrix_det_unit

end Formalism.L2.G
