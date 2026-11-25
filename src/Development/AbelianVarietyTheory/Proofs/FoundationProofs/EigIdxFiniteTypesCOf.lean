module

public import Formalism.LocalRingCardinality.DataRRMetric

@[expose] public section

open Formalism.BasicNotions NumberField

namespace GlobalTheory

def eigIdxFiniteTypes (D : D7) (X : DivX D) : EigIdx D X where
  Pi := D.what₂.FT
  fin := D.what₂.instFT
  dec := D.what₂.instFTd
  cOf := id
  lam_const := by
    intro j _ π π' e _ _ h
    have h' : π = π' := h
    rw [h']

end GlobalTheory
