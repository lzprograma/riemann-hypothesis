module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsSumMeasurableA
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsSumMeasurable.aestronglyMeasurable_finsum {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι}
    {g : ((Σ k, ι k) → ℂ) → ℝ} {φ : ℝ → ℝ} (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    (hφm : Measurable φ) (hφ0 : φ 0 = 0)
    (hg_meas : ∀ (B : Set (Fin e → ℂ)) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ),
      IsOpen B → ContinuousOn γ B → Set.MapsTo γ B {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} →
      ∃ a : (Fin e → ℂ) → ℝ, Measurable a ∧ ∀ y ∈ B, a y = g (γ y))
    (hind : ∀ᵐ y : Fin e → ℂ, ∀ w γ₁ γ₂, IsSheet P Ψ y w γ₁ → IsSheet P Ψ y w γ₂ →
      g (γ₁ y) * maDensity (fun j y' => pot L j (γ₁ y')) y =
        g (γ₂ y) * maDensity (fun j y' => pot L j (γ₂ y')) y) :
    AEStronglyMeasurable
      (fun y => ∑ᶠ w ∈ fibre P Ψ y, φ (sheetDensity P Ψ (pot L) g y w)) := by
  classical
  have hfin := fibreFinite K ι P e Ψ hP hΨ
  obtain ⟨B, γ, hBo, hlift, hcov⟩ := PtsSumMeasurable.exists_lift_family (P := P) (Ψ := Ψ) hfin
  have hγc : ∀ m, ContinuousOn (γ m) (B m) := fun m y hy =>
    (hlift m y hy).1.continuousAt.continuousWithinAt
  have hO : ∀ m, Set.MapsTo (γ m) (B m) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun m y hy =>
    (hlift m y hy).2.1.1
  choose a ham haB using fun m => hg_meas (B m) (γ m) (hBo m) (hγc m) (hO m)
  exact PtsSumMeasurable.aestronglyMeasurable_fibreSum_of_lifts (pot L) g φ hφm hφ0 hfin B γ hBo
    hlift hcov (fun m y => a m y * maDensity (fun j y' => pot L j (γ m y')) y)
    (fun m => (ham m).mul (PtsSumMeasurable.measurable_maDensity _))
    (fun m y hy => by rw [haB m y hy]) hind

theorem PtsSumMeasurable.proof : PtsSumMeasurable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  classical
  refine PtsSumMeasurable.aestronglyMeasurable_finsum (g := logNorm A s) (φ := id)
    hP hΨ measurable_id rfl (fun B γ hBo hγc hO => ?_) (sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs)
  refine ⟨fun y => Real.log (B.piecewise (fun y => ‖eval (γ y) (map (Int.castRingHom ℂ) s)‖) 0 y /
      B.piecewise (fun y => A.h (γ y)) 1 y), ?_, fun y hy => ?_⟩
  · exact Real.measurable_log.comp
      ((((continuous_norm.comp (MvPolynomial.continuous_eval _)).comp_continuousOn
          hγc).measurable_piecewise continuousOn_const hBo.measurableSet).div
        (((ContDiffOn.continuousOn hA).comp hγc hO).measurable_piecewise
          continuousOn_const hBo.measurableSet))
  · simp only [Set.piecewise_eq_of_mem _ _ _ hy, logNorm]

end GroundTheory.Heights₂.Heights
