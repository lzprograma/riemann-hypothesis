module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnitHmE
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegLaw

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem relab_rt_iff (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (τ' : E →+* ℂ) :
    relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0 := by
  apply ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_rt <;> assumption

theorem conjEmb_conjEmb (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ :=
  RingHom.ext fun z => Complex.conj_conj (τ z)

end Formalism.L2.Pj
