module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def ProjOp : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)],
    ∀ W : Submodule ℂ (PX m n), FiniteDimensional ℂ W → (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) →
      ∃ (ν : Measure (KR n)) (κ : KR n → ℂ), IsFiniteMeasure ν ∧ Continuous κ ∧
        (∀ Q ∈ W, ∀ y : GR n, ∫ k, κ k * sL Q (y * (k : GR n)) ∂ν = sL Q y) ∧
        ∀ (w : ℂ) (f : GR n → ℂ), Continuous f →
          (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → f (y * g) = (hLoc y : ℂ) ^ w * F0 p q e y * f g) →
          ∃ Q ∈ W, ∀ y : GR n, ∫ k, κ k * f (y * (k : GR n)) ∂ν = (hLoc y : ℂ) ^ w * sL Q y

end PositivityTheory.Rg.Sw.AbsSt
