module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DetIdealsKernelNormOne

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Matrix

theorem relative_determinant_norm_one (D : D7) : DetIdealsKernelNormOne D :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one (Formalism.L2.Ker.Car.ofRec D)

theorem character_unit_on_determinant (D : D7) (χ : IdE D → ℂ) (hχ : IsChi D χ) : ChiUnitDet D χ :=
  chi_unit_of_det_norm_one D (relative_determinant_norm_one D) χ hχ

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
