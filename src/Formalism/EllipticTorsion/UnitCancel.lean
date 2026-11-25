module

public import Formalism.EllipticTorsion.Statement
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

def UnitCancel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K]
    [NormedAlgebra ℚ_[p] K] (σ : Type) (G : MvPowerSeries σ K) (b : ℤ_[p]), IsUnit b →
      InN (algebraMap ℚ_[p] K (b : ℚ_[p]) • G) → InN G

end Formalism.ELL
