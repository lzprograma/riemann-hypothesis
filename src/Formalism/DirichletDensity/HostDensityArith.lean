module

public import Formalism.DirichletDensity.Statement
public import Formalism.DirichletDensity.DirichletDensityProofs.MQDiscr
public import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr

@[expose] public section

namespace Formalism.HF.Final

alias quadDiscr := _root_.Formalism.HF.quadDiscr
theorem mqDiscr : Formalism.HF.MQDiscr := Formalism.HF.mqDiscr_of quadDiscr

end Formalism.HF.Final
