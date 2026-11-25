module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem aemeasurable_chart_of_locally_continuous {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (e : OpenPartialHomeomorph Y (V n)) {S : Set Y} {d : Y → ℝ} (hS : IsOpen S)
    (h : ∀ y ∈ S, y ∈ e.source →
      ∃ g : V n → ℝ, ContinuousAt g (e y) ∧ ∀ᶠ z in 𝓝 y, d z = g (e z)) :
    AEMeasurable (fun v => d (e.symm v)) (volume.restrict (e.target ∩ e.symm ⁻¹' S)) := by
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' S) := e.isOpen_inter_preimage_symm hS
  refine ContinuousOn.aemeasurable (fun v hv => ContinuousAt.continuousWithinAt ?_) hO.measurableSet
  obtain ⟨hvt, hvS⟩ := hv
  obtain ⟨g, hg, hev⟩ := h _ hvS (e.map_target hvt)
  rw [e.right_inv hvt] at hg
  refine hg.congr ?_
  have h1 := (e.continuousAt_symm hvt).eventually hev
  filter_upwards [h1, e.open_target.mem_nhds hvt] with w hw hwt
  rw [hw, e.right_inv hwt]

end GlobalTheory.GoodTop
