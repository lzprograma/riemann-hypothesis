module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsPosDensMeasurable
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsPosDensMeasurable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsSumMeasurableA
import Mathlib.Topology.Separation.CompletelyRegular
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsPosDensMeasurable.proof : PtsPosDensMeasurable.Statement := by
  intro K _ ι _ P e Ψ L g hP hΨ hL hg hdeg
  classical
  have hd1 : IsDegZeroSmooth (fun _ : (Σ k, ι k) → ℂ => (1 : ℝ)) := ⟨contDiffOn_const, fun _ _ _ => rfl⟩
  have hind := sheetIndep K ι P e Ψ L _ 1 hP hΨ hL (PtsPosDens.isSmoothHerm_ofWeight hd1)
    (PtsPosDens.isSectionOn_ofWeight_one hP hd1)
  rw [PtsPosDens.logNorm_ofWeight_one hd1] at hind
  simp only [one_mul] at hind
  refine (PtsSumMeasurable.aestronglyMeasurable_finsum (g := g) (φ := (max · 0))
    hP hΨ (measurable_id.max measurable_const) (max_self 0)
    (fun B γ hBo hγc _ => ⟨fun y => g (B.piecewise γ 0 y),
      hg.comp (hγc.measurable_piecewise continuousOn_const hBo.measurableSet),
      fun y hy => by simp [Set.piecewise_eq_of_mem _ _ _ hy]⟩) ?_).aemeasurable
  filter_upwards [hind] with y hy w γ₁ γ₂ h₁ h₂
  rw [hy w γ₁ γ₂ h₁ h₂]
  choose i0 hi0 using h₁.2.self_of_nhds.2.1.1
  have hs : segre (γ₁ y) = segre (γ₂ y) := h₁.1.trans h₂.1.symm
  obtain ⟨hc', hrel⟩ := eq_bsmul_of_segre_eq i0 hi0 hs
  have hgy : g (γ₂ y) = g (γ₁ y) := by
    rw [hrel]
    exact hdeg _ _ fun k => div_ne_zero (hc' k) (hi0 k)
  rw [hgy]

end GroundTheory.Heights₂.Heights
