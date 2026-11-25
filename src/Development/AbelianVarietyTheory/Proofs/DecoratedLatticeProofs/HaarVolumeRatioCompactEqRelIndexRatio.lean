module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMulMatrixVolumeOpenSubgroupIntegralGL
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge
open scoped Pointwise ENNReal

namespace GlobalTheory.VolRatio

theorem relIndex_mul_measure_sub {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  apply GlobalTheory.IndexVolume.relIndex_mul_measure_subgroup <;> assumption

theorem vol_ratio : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (A B : Subgroup G), IsOpen ((A ⊓ B : Subgroup G) : Set G) → IsCompact (A : Set G) → IsCompact (B : Set G) → (μ (A : Set G)).toReal / (μ (B : Set G)).toReal = (B.relIndex A : ℝ) / (A.relIndex B : ℝ) := by
  intro G _ _ _ _ _ μ _ A B hC hA hB
  have hCA : A ⊓ B ≤ A := inf_le_left
  have hCB : A ⊓ B ≤ B := inf_le_right
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  haveI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  haveI : ((A ⊓ B).subgroupOf A).FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen ((A ⊓ B).subgroupOf A)
      (hC.preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  haveI : ((A ⊓ B).subgroupOf B).FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen ((A ⊓ B).subgroupOf B)
      (hC.preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  have hCm : MeasurableSet ((A ⊓ B : Subgroup G) : Set G) := hC.measurableSet
  have h1 := relIndex_mul_measure_sub (A ⊓ B) A hCA hCm μ
  have h2 := relIndex_mul_measure_sub (A ⊓ B) B hCB hCm μ
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.inf_relIndex_right] at h2
  have hpos : 0 < μ ((A ⊓ B : Subgroup G) : Set G) := hC.measure_pos μ ⟨1, (A ⊓ B).one_mem⟩
  have hfin : μ ((A ⊓ B : Subgroup G) : Set G) < ⊤ :=
    lt_of_le_of_lt (measure_mono hCA) hA.measure_lt_top
  have hr : 0 < (μ ((A ⊓ B : Subgroup G) : Set G)).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  rw [← h1, ← h2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, mul_div_mul_right _ _ hr.ne']

end GlobalTheory.VolRatio
