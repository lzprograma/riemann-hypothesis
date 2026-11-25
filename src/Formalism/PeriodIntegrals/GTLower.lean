module

public import Formalism.PeriodIntegrals.GTDefs
import Formalism.LocalRingCardinality.Params

@[expose] public section

noncomputable section

namespace PI

open Formalism.BasicNotions MvPolynomial

def GTLower : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg → Branch h lam sg

end PI
