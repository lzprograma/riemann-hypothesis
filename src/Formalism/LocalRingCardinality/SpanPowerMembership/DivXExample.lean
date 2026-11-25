module

public import Formalism.LocalRingCardinality.DataDIV

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

def geoExample (F : Type) [Field F] [NumberField F] [StarRing F] : DV.Geo F where
  Var := Empty
  dim := fun Y => Empty.elim Y
  Fn := fun Y => Empty.elim Y
  fnField := fun Y => Empty.elim Y
  fnAlg := fun Y => Empty.elim Y
  Dv := fun Y => Empty.elim Y
  dvGrp := fun Y => Empty.elim Y
  H0 := fun Y => Empty.elim Y
  Cl := fun Y => Empty.elim Y
  supp := fun Y => Empty.elim Y
  inter := fun Y => Empty.elim Y
  vanishOn := fun Y => Empty.elim Y
  Adl := fun Y => Empty.elim Y
  ofW := fun Y => Empty.elim Y
  twist := fun Y => Empty.elim Y
  arTop := fun Y => Empty.elim Y
  arVol := fun Y => Empty.elim Y
  nefA := fun Y => Empty.elim Y

variable (D : D7)

end Formalism.BasicNotions.Examples₂
