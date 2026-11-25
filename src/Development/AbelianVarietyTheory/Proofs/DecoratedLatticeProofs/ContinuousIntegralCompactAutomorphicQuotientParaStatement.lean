module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientPara

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param : ∀ (D : D7) (V : HSp D), CoCpt V → ∀ (v : Vol V) (P : Type) [TopologicalSpace P] (K : GA D V → P → ℂ), Continuous (Function.uncurry K) → (∀ γ ∈ GQ V, ∀ g p, K (γ * g) p = K g p) → (∀ p, IntegrableOn (fun g => K g p) v.𝓕 v.μ) ∧ (Continuous fun p => ∫ g in v.𝓕, K g p ∂v.μ) ∧ ∀ p₀, ∃ C : ℝ, ∀ᶠ p in nhds p₀, ∀ g, ‖K g p‖ ≤ C := by
  first | exact @GlobalTheory.CocompactParam.continuous_integral_param
