module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.KernelAwayPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

@[expose] public section

noncomputable section

namespace GlobalTheory.LiftTypePrime

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

def StdAt (D : D7) (g : ℕ) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∃ L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E), (∀ x, x ∈ L₀ ↔ ∀ k, IsIntegral ℤ (x k)) ∧ EqAt D g L L₀


end GlobalTheory.LiftTypePrime

end
