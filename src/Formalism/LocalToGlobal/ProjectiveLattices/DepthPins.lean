module

import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.SqrtNegDiscMemCoeffField
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def PiHalf (l : Level H) (D : DepData E) : Prop := Ideal.span {D.pi 0 * D.pi 1} = l.Mb

theorem zeta_mem_of_dvd {l : Level H} (c : Coeff l) {g : ℕ} (hg : g ∣ l.M') (h0 : l.M' ≠ 0) : zeta g ∈ c.F := by
  apply GlobalTheory.HostModel.zeta_mem_coeff_of_dvd <;> assumption

end Formalism.L2.Pj
