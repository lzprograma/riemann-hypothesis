module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmBpAtEqOfShiftR
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousHsInner
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBP

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 MeasureTheory

noncomputable section

section swap

variable {k r : ℕ} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']

theorem isDFrame_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ γ : B.Mat k r) :
    D.IsDFrame Ds' ν' m₀ γ ↔ D.IsDFrame Ds ν' m₀ γ := by
  simp only [D.IsDFrame, D.cofR, D.cofL, hz, hz']

theorem muR_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (_hz' : Ds'.z' = Ds.z') (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1))) :
    D.muR Ds' γ w = D.muR Ds γ w := by
  unfold D.muR D.rhoOfU
  rw [hz]

theorem inSS_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (q : B.SS k r) : Ds'.inSS q ↔ Ds.inSS q := by
  simp only [B.RealPlaceData.inSS, hz, hz']

theorem isNormCut_congr (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (γ : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ) :
    D.IsNormCut Ds' γ μR θ ↔ D.IsNormCut Ds γ μR θ := by
  simp only [D.IsNormCut, inSS_swap Ds Ds' hz hz']

theorem isRelevant_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (γ : B.Mat k r) : C6.IsRelevant Ds' γ ↔ C6.IsRelevant Ds γ := by
  simp only [C6.IsRelevant, hz, hz']

theorem muSS_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hW : Ds'.μW = Ds.μW)
    (hN : Ds'.μN = Ds.μN) (hW' : Ds'.μW' = Ds.μW') : Ds'.μSS = Ds.μSS := by
  simp only [B.RealPlaceData.μSS, hW, hN, hW']

theorem orbIntegrand_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (hπ : Ds'.π = Ds.π) (A : B.Mat k r → (Wq' →L[ℂ] Wq))
    (hA : WigEquiv Ds.z Ds.z' Ds.π' Ds'.π' A) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r)
    (hγ : γ ∈ B.GV k r) (hGγ : 0 < Gf k r Ds.z Ds.z' γ) (q : B.SS k r) (hq : Ds.inSS q) :
    D.orbIntegrand Ds' γ (fun g => (f g).comp (A g)) q = (D.orbIntegrand Ds γ f q).comp (A γ) := by
  obtain ⟨h1m, n1m, h2m, n2m⟩ := hq
  have o1 : ∀ w : Fin (2 * r + k + 1) → ℂ, Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ UWset k r w := by
    intro w
    rw [Matrix.of.apply_symm_apply]
    exact PBO.one_mem_UWset w
  have hq1 : Ds.inSS ((Matrix.of.symm (1 : B.Mat k r), q.1.2), (Matrix.of.symm (1 : B.Mat k r), q.2.2)) :=
    ⟨o1 Ds.z, n1m, o1 Ds.z', n2m⟩
  have hq0 : Ds.inSS ((q.1.1, q.1.2), (Matrix.of.symm (1 : B.Mat k r), q.2.2)) :=
    ⟨h1m, n1m, o1 Ds.z', n2m⟩
  have e1 : B.sgs ((Matrix.of.symm (1 : B.Mat k r), q.1.2), (Matrix.of.symm (1 : B.Mat k r), q.2.2)) γ
      = (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 := by
    simp only [B.sgs, Matrix.of.apply_symm_apply, inv_one, one_mul, mul_one]
  have e0 : B.sgs ((q.1.1, q.1.2), (Matrix.of.symm (1 : B.Mat k r), q.2.2)) γ
      = (Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 := by
    simp only [B.sgs, Matrix.of.apply_symm_apply, mul_one]
  have g1GV : (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 ∈ B.GV k r :=
    Dx2.DF.mul_UH (Dx2.DF.mul_UH (WeylGroupFacts.uh_inv (B6.Nset_sub k r n1m)) hγ) (B6.Nset_sub k r n2m)
  have g0GV : (Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 ∈ B.GV k r := by
    have := Dx2.DF.mul_UH (WeylGroupFacts.uh_inv (B6.UWset_sub k r Ds.z h1m)) g1GV
    simpa only [mul_assoc] using this
  have hG1 : 0 < Gf k r Ds.z Ds.z' ((Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2) := by
    rw [← e1, TBBx2.Gf_sgs Ds _ hq1]
    exact hGγ
  have hG0 : 0 < Gf k r Ds.z Ds.z' ((Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2) := by
    rw [← e0, TBBx2.Gf_sgs Ds _ hq0]
    exact hGγ
  have hAs : A (B.sgs q γ)
      = Ds.π' (Matrix.of q.2.1)⁻¹ ∘SL A γ ∘SL Ds'.π' (Matrix.of q.2.1) := by
    have s1 : B.sgs q γ
        = (Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 * Matrix.of q.2.1 := rfl
    rw [s1, hA.2.2 _ g0GV hG0 _ h2m]
    have s2 : (Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2
        = (Matrix.of q.1.1)⁻¹ * ((Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2) := by
      simp only [mul_assoc]
    rw [s2, hA.2.1 _ g1GV hG1 _ (WeylGroupFacts.uw_inv h1m),
      hA.1 γ hγ hGγ _ (WeylGroupFacts.mem_n_inv n1m) _ n2m]
  have h2m' : Matrix.of q.2.1 ∈ UWset k r Ds'.z' := by
    rw [hz']
    exact h2m
  have hcanc : Ds'.π' (Matrix.of q.2.1) ∘SL Ds'.π' (Matrix.of q.2.1)⁻¹ = 1 := by
    rw [← Ds'.π'_rep.2 _ h2m' _ (WeylGroupFacts.uw_inv h2m'), NFRadRedS.uw_mul_inv h2m', Ds'.π'_rep.1]
  have hxi : B.xiTau Ds' (1, 1) q = B.xiTau Ds (1, 1) q := by
    simp only [B.xiTau, hz, hz']
  simp only [D.orbIntegrand, B.rho, hxi, hπ]
  ext v
  have hv := congrArg (fun T => (T : Wq' →L[ℂ] Wq') v) hcanc
  have hv2 := congrArg (fun T => (T : Wq' →L[ℂ] Wq) ((Ds'.π' (Matrix.of q.2.1)⁻¹) v)) hAs
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at hv hv2
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [hv2, hv]

theorem orbJ_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (hπ : Ds'.π = Ds.π) (hW : Ds'.μW = Ds.μW) (hN : Ds'.μN = Ds.μN)
    (hW' : Ds'.μW' = Ds.μW') (A : B.Mat k r → (Wq' →L[ℂ] Wq)) (hA : WigEquiv Ds.z Ds.z' Ds.π' Ds'.π' A)
    (f : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (hγ : γ ∈ B.GV k r) (hGγ : 0 < Gf k r Ds.z Ds.z' γ)
    (μR : Measure (Mt k r)) (hrel : C6.IsRelevant Ds γ)
    (hH : B.IsHaarOn (C6.Rset γ) μR) (θ : B.SS k r → ℝ) (hθ : D.IsNormCut Ds γ μR θ)
    (hi : Integrable (fun q => θ q • D.orbIntegrand Ds γ f q) Ds.μSS) :
    D.orbJ Ds' γ μR (fun g => (f g).comp (A g)) = (D.orbJ Ds γ μR f).comp (A γ) := by
  set F' : B.Mat k r → Wq' →L[ℂ] Wp := fun g => (f g).comp (A g) with hF'
  have hθ' : D.IsNormCut Ds' γ μR θ := (isNormCut_congr Ds Ds' hz hz' γ μR θ).2 hθ
  have hrel' : C6.IsRelevant Ds' γ := (isRelevant_swap Ds Ds' hz hz' γ).2 hrel
  have hμ : Ds'.μSS = Ds.μSS := muSS_swap Ds Ds' hW hN hW'
  let L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq' →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq' Wq Wp).flip (A γ)
  have hL : ∀ X, L X = X.comp (A γ) := fun X => rfl
  have hae : ∀ᵐ q ∂Ds.μSS,
      θ q • D.orbIntegrand Ds' γ F' q = L (θ q • D.orbIntegrand Ds γ f q) := by
    filter_upwards [TBBx2.ae_inSS Ds] with q hq
    rw [hL, ContinuousLinearMap.smul_comp, orbIntegrand_swap Ds Ds' hz hz' hπ A hA f γ hγ hGγ q hq]
  have hi' : Integrable (fun q => θ q • D.orbIntegrand Ds' γ F' q) Ds'.μSS := by
    rw [hμ]
    exact (L.integrable_comp hi).congr (hae.mono fun q hq => hq.symm)
  have hex' : ∃ θ' : B.SS k r → ℝ, D.IsNormCut Ds' γ μR θ' ∧
      Integrable (fun p => θ' p • D.orbIntegrand Ds' γ F' p) Ds'.μSS := ⟨θ, hθ', hi'⟩
  have hex : ∃ θ' : B.SS k r → ℝ, D.IsNormCut Ds γ μR θ' ∧
      Integrable (fun p => θ' p • D.orbIntegrand Ds γ f p) Ds.μSS := ⟨θ, hθ, hi⟩
  unfold D.orbJ
  rw [dite_eq_left hex', dite_eq_left hex]
  rw [P.orbital_integral_indep_choice k r Wp Wq' Ds' γ μR hrel' hH F' _ θ hex'.choose_spec.1 hθ'
      hex'.choose_spec.2 hi',
    P.orbital_integral_indep_choice k r Wp Wq Ds γ μR hrel hH f _ θ hex.choose_spec.1 hθ hex.choose_spec.2 hi]
  rw [hμ, integral_congr_ae hae]
  exact L.integral_comp_comm hi

end swap

end

end Formalism.FourierDecayAlt.P.CutBPEq
