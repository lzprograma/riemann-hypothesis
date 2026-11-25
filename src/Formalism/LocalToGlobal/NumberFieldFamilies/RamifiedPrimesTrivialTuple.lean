module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.LocalRingCardinality.DataNChoice
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Fam.DivCQ

open Formalism.BasicNotions Formalism.L2.Host

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

theorem unrAt_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt w :=
  fun _ _ => rfl

end Formalism.L2.Fam.DivCQ

end
