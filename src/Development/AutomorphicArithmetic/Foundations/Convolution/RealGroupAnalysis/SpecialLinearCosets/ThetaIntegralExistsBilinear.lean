module

import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatLin
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierAdelicPi
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.I.WL

variable {F : Type} [Field F] [NumberField F]

private theorem normOneIntegral_add (M : Meas F) {u u' : G1 F → ℂ} (hu : Integrable (iw u) M.ν)
    (hu' : Integrable (iw u') M.ν) : M.I0 (fun g => u g + u' g) = M.I0 u + M.I0 u' := by
  unfold Meas.I0
  rw [← integral_add hu hu']
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp [iw, mul_add]

private theorem normOneIntegral_const_mul (M : Meas F) (c : ℂ) (u : G1 F → ℂ) :
    M.I0 (fun g => c * u g) = c * M.I0 u := by
  unfold Meas.I0
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [iw]
  ring

end UpperTheory.ConvolutionTheory.R2.I.WL

end

open UpperTheory.ConvolutionTheory.R2.I.WL in
theorem UpperTheory.ConvolutionTheory.R2.I.thetaIntegral_exists_bilinear :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (h : GL (Fin 2) (A E)),
      ∃ B : π.V →ₗ[ℂ] Fock (F := F) D.δ →ₗ[ℂ] ℂ, ∀ f φ, B f φ = W1 W M f.1.1 φ.1 h := by
  intro F E _ _ _ _ _ _ _ D W M π h
  have hint : ∀ (f : π.V) (φ : Fock (F := F) D.δ), Integrable (iw (w1 W f.1.1 φ.1 h)) M.ν :=
    fun f φ => (UpperTheory.ConvolutionTheory.R2.conv F E D W M π f.1 f.2 φ.1 φ.2 h).2.2.2.2
  have hL : ∀ f : π.V, Pp.Lf f.1.1 := fun f => (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f.1 f.2).1
  have hwf := UpperTheory.ConvolutionTheory.R2.Pp.wfBasic F
  refine ⟨LinearMap.mk₂ ℂ (fun f φ => W1 W M f.1.1 φ.1 h) ?_ ?_ ?_ ?_, fun f φ => rfl⟩
  · intro f f' φ
    have e : w1 W (f + f').1.1 φ.1 h = fun g => w1 W f.1.1 φ.1 h g + w1 W f'.1.1 φ.1 h g := by
      funext g
      have := (hwf f.1.1 (hL f)).2.2.2.2 f'.1.1 (hL f') (gl g * dM (nu F h))
      simp only [w1]
      rw [← add_mul, ← this]
      rfl
    simp only [W1]
    rw [e]
    exact normOneIntegral_add M (hint f φ) (hint f' φ)
  · intro c f φ
    have e : w1 W (c • f).1.1 φ.1 h = fun g => c * w1 W f.1.1 φ.1 h g := by
      funext g
      have := (hwf f.1.1 (hL f)).2.2.2.1 c (gl g * dM (nu F h))
      simp only [w1]
      rw [← mul_assoc, ← this]
      rfl
    simp only [W1]
    rw [e]
    exact normOneIntegral_const_mul M c _
  · intro f φ φ'
    have e : w1 W f.1.1 (φ + φ').1 h = fun g => w1 W f.1.1 φ.1 h g + w1 W f.1.1 φ'.1 h g := by
      funext g
      simp only [w1]
      rw [← mul_add, ← G.hat_add (W.Om g (W.L h φ.1)) (W.Om g (W.L h φ'.1))]
      congr 2
      simp [map_add (f := _)]
    simp only [W1]
    rw [e]
    exact normOneIntegral_add M (hint f φ) (hint f φ')
  · intro c f φ
    have e : w1 W f.1.1 (c • φ).1 h = fun g => c * w1 W f.1.1 φ.1 h g := by
      funext g
      simp only [w1]
      have e' : (W.Om g (W.L h (c • φ).1)).1 = c • (W.Om g (W.L h φ.1)).1 := by
        simp [map_smul]
      rw [e', G.hat_smul]
      ring
    simp only [W1]
    rw [e]
    exact normOneIntegral_const_mul M c _
