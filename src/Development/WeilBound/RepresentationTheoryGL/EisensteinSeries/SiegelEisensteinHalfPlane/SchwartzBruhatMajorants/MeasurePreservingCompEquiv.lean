module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompMulVec
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
import GroundTheory.AutomorphicForms.ReductionMeasure

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.LtrFourier.Hd

open MeasureTheory in
theorem measurePreserving_comp_equiv {ι κ : Type} [Fintype ι] [Fintype κ] {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (e : κ ≃ ι) :
    MeasurePreserving (fun x : ι → α ↦ x ∘ e) (Measure.pi fun _ ↦ μ)
      (Measure.pi fun _ ↦ μ) := by
  have hm : Measurable (fun x : ι → α ↦ x ∘ e) :=
    Measurable.of_eval fun k ↦ measurable_pi_apply (e k)
  refine ⟨hm, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : ι → α ↦ x ∘ e) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i ↦ s (e.symm i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
    exact ⟨fun h i ↦ by simpa using h (e.symm i), fun h k ↦ by simpa using h (e k)⟩
  rw [hpre, Measure.pi_pi]
  exact Fintype.prod_equiv e.symm _ _ fun _ ↦ rfl

noncomputable section

theorem adelicFourierPi_ltr : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ), adelicFourierPi k (ltr A F) =
      (((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ : ℂ) •
        ltr (tInv A) (adelicFourierPi k F) := by
  apply GlobalTheory.CompanionTheory.LtrFourier.adelicFourierPi_ltr

end

end GlobalTheory.CompanionTheory.LtrFourier.Hd
