module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions : ∀ D : D7, FlatLaw D → ∀ (ψ : AddChar (AF D.host.F) ℂ), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) Ψ, IsThetaFunO ψ B.V J.W Ψ → IsThetaFunO ψ B.V₀ J.W₀ (flatBF s Ψ)) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) Ψ, IsThetaFunO ψ J.W B.V Ψ → IsThetaFunO ψ J.W₀ B.V₀ (flatFB s Ψ) := by
  first | exact @GlobalTheory.Unf.FlatTheta.flat_isThetaFun
