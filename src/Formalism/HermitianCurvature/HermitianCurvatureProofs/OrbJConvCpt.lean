module

public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialMapProper
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx3
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.CV

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem conv0 (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ)
    (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (c₁ : ℕ)
    (hPP : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), C2.Std k r z z' → C2.PosPt k r z z' γ →
      C2.IsMonomial (Zhat k r z z' γ) → ∃ C : ℝ,
        (∀ σ ∈ C2.Sg k r z z' γ, ∀ s' ∈ Sset k r z',
          B.gN σ + B.gN s' ≤ C * B.gN (σ⁻¹ * γ * s') ^ (c₁ * (r + 1) ^ 2)) ∧
        (∀ s ∈ Sset k r z, ∀ σ' ∈ C2.Sg' k r z z' γ,
          B.gN s + B.gN σ' ≤ C * B.gN (s⁻¹ * γ * σ') ^ (c₁ * (r + 1) ^ 2)))
    (hγ : γ ∈ B.GV k r) (hd : ∀ a, d a ≠ 0) (hZ : Zhat k r D.z D.z' γ = C2.monoP w d)
    (hpos : 0 < Gf k r D.z D.z' γ)
    (hA : 16 * ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A)
    (hFc : ContinuousOn F (B.GV k r)) (sharpFunctionalExponent : ℝ) (hb : ∀ g ∈ B.GV k r, B.gN g ^ A * ‖F g‖ ≤ sharpFunctionalExponent) :
    ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ (Formalism.FourierDecayAlt.D.muR D γ w) θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS :=
  Dx3.conv0 D γ w d A F c₁ hPP hγ hd hZ hpos hA hFc sharpFunctionalExponent hb

theorem cpt_bound (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef D F) (A : ℝ)
    (hA : 0 ≤ A) : ∃ c : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖F g‖ ≤ c := by
  obtain ⟨hCk, ⟨R, hR⟩, -⟩ := hF
  have hFc : ContinuousOn F (B.GV k r) := P.B5.ckOn_continuousOn hCk
  set K : Set (B.Mat k r) := B.GV k r ∩ {g | B.gN g ≤ R} with hK
  have hgNc : Continuous (fun g : B.Mat k r => B.gN g) := by
    unfold B.gN
    refine Real.continuous_sqrt.comp ?_
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))
  have hKc : IsCompact K := by
    have hbox : IsCompact (Set.univ.pi fun _ : Fin (2 * r + k + 1) =>
        Set.univ.pi fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) (max R 0)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    refine hbox.of_isClosed_subset ((P.unitary_group_closed k r).closed.inter
      (isClosed_le hgNc continuous_const)) ?_
    intro g hg
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact (entry_le_gN g i j).trans (hg.2.trans (le_max_left _ _))
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hFc.mono Set.inter_subset_left)
  refine ⟨(max R 1) ^ A * max C 0, fun g hg => ?_⟩
  by_cases hF0 : F g = 0
  · rw [hF0, norm_zero, mul_zero]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (le_max_right _ _)
  · have hgR := hR g hg hF0
    have hg1 : 1 ≤ B.gN g := P.BetaSesquilinearity.gN_ge_one hg
    have h1 : B.gN g ^ A ≤ (max R 1) ^ A :=
      Real.rpow_le_rpow (by linarith) (hgR.trans (le_max_left _ _)) hA
    have h2 : ‖F g‖ ≤ max C 0 := (hC g ⟨hg, hgR⟩).trans (le_max_left _ _)
    exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)

theorem orbJConv_cpt (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
    (d : Fin (r + 1) → ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hγ : γ ∈ B.GV k r) (hrel : C6.IsRelevant S γ)
    (hd : ∀ a, d a ≠ 0) (hZ : Zhat k r S.z S.z' γ = C2.monoP w d) (hpos : 0 < Gf k r S.z S.z' γ)
    (hF : KB.CptCoef S F) :
    ∃ θ, D.IsNormCut S γ (D.muR S γ w) θ ∧ Integrable (fun p => θ p • D.orbIntegrand S γ F p) S.μSS := by
  obtain ⟨c₁, hPP⟩ := Formalism.FourierDecayAlt.P.polynomial_map_proper
  set A : ℝ := 16 * ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) with hAdef
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨c, hc⟩ := cpt_bound S F hF A hA0
  exact conv0 S γ w d A F c₁ hPP hγ hd hZ hpos le_rfl (P.B5.ckOn_continuousOn hF.1) c hc

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.CV
