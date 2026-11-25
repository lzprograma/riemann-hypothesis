module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

@[expose] public section

noncomputable section

namespace GlobalTheory.NFacts

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem residualIrreducibility_forms_equivalent (D : D7) : SumRepresentations.adm6 D ↔ ResidualIrreducibleRankR D := Iff.rfl

end GlobalTheory.NFacts

end
