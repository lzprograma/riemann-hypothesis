module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumNormLePolynomialScale
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace PositivityTheory.ThKF0.LatSum

open mixedEmbedding

noncomputable abbrev latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Submodule ℤ (κ → mixedSpace F) :=
  Submodule.span ℤ (Set.range (Pi.basis (fun _ : κ => latticeBasis F)))

end PositivityTheory.ThKF0.LatSum

namespace PositivityTheory.ThKF0.LatSum

open mixedEmbedding

theorem thetaSum_norm_le_pow :
    ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (N₀ k : ℕ) (C : ℝ), ∀ (A : ℝ) (m : ℕ) (Ψ : (κ → AF F) → ℂ), 1 ≤ m →
    (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A) →
    (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)) →
    ‖thetaSum F Ψ‖ ≤ C * A * (m : ℝ) ^ k := by
  apply GlobalTheory.LatScaleSum.thetaSum_norm_le_pow

end PositivityTheory.ThKF0.LatSum
