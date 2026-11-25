module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.ZeroInjectionMemFourthPower
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColDatK

@[expose] public section

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Eq.J

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Th1.H

export Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J (putL putL_mem)

theorem lat0IsLat {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Ker.Base D cc δ}
    (hS : B.StdOK) (N N' : ℕ) :
    IsLat (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ)
      (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) :=
  Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J.lat0IsLat (B := B.toCar) hS N N'

end Formalism.L2.PairingIndexBounds.Eq.J

end
