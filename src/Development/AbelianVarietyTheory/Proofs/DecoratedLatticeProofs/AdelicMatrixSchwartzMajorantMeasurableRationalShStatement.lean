module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ (m n : ℕ) (K : Set (Mx D m n)), IsCompact K → IsClosed {x | InBox K x} ∧ Continuous (realSize θ : Mx D m n → ℝ) ∧ (∀ N, Measurable (maj θ K N)) ∧ ∀ R : ℝ, IsCompact {x | InBox K x ∧ realSize θ x ≤ R}) ∧ ∀ (m n k : ℕ) (x : Matrix (Fin m) (Fin n) D.host.E), LinearIndependent D.host.E x.transpose → ∀ K : Set (Mx D m k), IsCompact K → ∃ K' : Set (Mx D n k), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ u : Mx D n k, maj θ K N ((rat x : Mx D m n) ⬝ u) ≤ C * maj θ K' N u := by
  first | exact @GlobalTheory.Unf.maj_measurable_rat
