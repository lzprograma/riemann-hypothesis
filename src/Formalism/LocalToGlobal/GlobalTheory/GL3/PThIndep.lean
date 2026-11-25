module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.PSelfDual
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ThIndep

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem hermitian_form_integral_values : HfIntRec :=
  fun D => Formalism.L2.Ker.Cd.IntegralLatticeDensity.hermitian_form_integral_values (Formalism.L2.Ker.Car.ofRec D)

theorem theta_operator_isometry : ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ,
    IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IopIso D (tor0 D cc δ) :=
  IopIso_of_parts hermitian_form_integral_values self_dual_lattice

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
