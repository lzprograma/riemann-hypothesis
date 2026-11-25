module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData

@[expose] public section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory
open scoped ENNReal Pointwise

variable {G : Type} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

theorem inv_invariant_of_bi_invariant [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure] [SigmaFinite μ]
    (f : G → ℝ) (hf : Continuous f) (hi : Integrable f μ) (h1 : 0 < f 1) : μ.IsInvInvariant := by
  let U : Set G := {h | f 1 / 2 < f h}
  have ho : IsOpen U := isOpen_lt continuous_const hf
  have h1U : (1 : G) ∈ U := show f 1 / 2 < f 1 from half_lt_self h1
  have h₀ : μ (U ∩ U⁻¹) ≠ 0 :=
    (ho.inter ho.inv).measure_ne_zero μ ⟨1, h1U, by simpa only [Set.mem_inv, inv_one] using h1U⟩
  have hfin : μ (U ∩ U⁻¹) ≠ ⊤ := by
    refine (lt_of_le_of_lt (measure_mono ?_) (hi.measure_norm_ge_lt_top (half_pos h1))).ne
    intro x hx
    change f 1 / 2 ≤ ‖f x‖
    rw [Real.norm_eq_abs]
    exact (show f 1 / 2 < f x from hx.1).le.trans (le_abs_self _)
  refine ⟨?_⟩
  simpa only [Measure.inv_apply, show (U ∩ U⁻¹)⁻¹ = U ∩ U⁻¹ by
    rw [Set.inter_inv, inv_inv, Set.inter_comm], ENNReal.div_self h₀ hfin, one_smul] using
    (measure_eq_div_smul μ.inv μ h₀ hfin)

end Formalism.MainNotions.BridgeLemma

end
