module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeFibres
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeSheetCore

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace ModelFibreSumAlmostEverywhere

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem exists_sheet (L : HermLine ι) (r : ℝ) (E : Set M.Xc) (hP : IsArithVar P (e + 1))
    (hL : IsSmoothHerm L) (x : M.Xc) (hx : x ∉ modelBad M Ψ E) :
    ∃ γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ, IsSheet P Ψ (modelQ M Ψ x) (modelW M Ψ x) γ ∧
      maDensity (fun (_ : Fin e) y' => r * Real.log (L.h (γ y'))) (modelQ M Ψ x) =
        pushDens M.atlas (fun _ => modelPot M L r) (modelQ M Ψ) x := by
  have hj : x ∈ (M.atlas.chart (chartIdx M.atlas x)).source := Classical.choose_spec (M.atlas.cover x)
  have hsu : (M.atlas.chart (chartIdx M.atlas x)).symm (M.atlas.chart (chartIdx M.atlas x) x) = x :=
    (M.atlas.chart (chartIdx M.atlas x)).left_inv hj
  have huU : M.atlas.chart (chartIdx M.atlas x) x ∈
      (M.atlas.chart (chartIdx M.atlas x)).target ∩
        (M.atlas.chart (chartIdx M.atlas x)).symm ⁻¹' modelU M x :=
    ⟨(M.atlas.chart (chartIdx M.atlas x)).map_source hj,
      by rw [Set.mem_preimage, hsu]; exact mem_modelU M x⟩
  obtain ⟨hQa, hQd⟩ := modelQ_good_of_notMem M Ψ E x hx _ hj
  obtain ⟨γ, hsh, -, hmd⟩ :=
    HilbertSamuel.AnResBridge.exists_sheet_of_atlas (P := P) Ψ M.atlas (modelQ M Ψ) (modelU M x)
      (modelLift M x) (fun _ => L) (fun _ => r) hP (fun _ => hL) x (modelU_isOpen M x)
      (mem_modelU M x) (fun x' hx' => ((modelLift_spec M x).1 x' hx').1) hQa hQd
      (analyticAt_lift_chart M x _ huU) (analyticAt_segre_lift M Ψ x _ huU)
      (psi_zero_ne_of_not_mem_bad M Ψ hx) (fun _ hx' => modelQ_eq_local M Ψ hx')
  refine ⟨γ, hsh, ?_⟩
  rw [hmd]
  unfold pushDens locDens
  rw [hsu]
  rfl

end ModelFibreSumAlmostEverywhere

end GroundTheory.Heights₂.Heights.LowerBoundFree
