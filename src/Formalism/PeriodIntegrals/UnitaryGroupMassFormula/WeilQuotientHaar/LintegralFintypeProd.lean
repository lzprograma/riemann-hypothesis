module

import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotMeas
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.TypeStar
public import Mathlib.MeasureTheory.Integral.Marginal

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QPK


theorem lintegral_fintype_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  apply Formalism.L2.SG.Pf.Carrier.JointQuot.lintegral_fintype_prod <;> assumption

end QPK
