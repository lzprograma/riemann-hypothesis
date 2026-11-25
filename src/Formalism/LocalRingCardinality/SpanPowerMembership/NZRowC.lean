module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Formalism.LocalRingCardinality.DataRows

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions

abbrev En (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

end Formalism.BasicNotions.Examples₂.NZ
