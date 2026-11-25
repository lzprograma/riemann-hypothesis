module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMajorantCoordinateCosetMeasure
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.integrable_majorant_coordinate_coset_measure : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (P : Fin m → Fin n → Prop) (a : Mx D m n) (μ : Measure (Mx D m n)), IsFiniteMeasureOnCompacts μ → (∀ᵐ x ∂μ, ∀ i j, ¬ P i j → x i j = a i j) → (∀ t : Mx D m n, (∀ i j, ¬ P i j → t i j = 0) → Measure.map (fun x => x + t) μ = μ) → ∃ N : ℕ, ∀ K : Set (Mx D m n), IsCompact K → Integrable (maj θ K N) μ := by
  first | exact @GlobalTheory.Unf.MajInt.maj_integrable
