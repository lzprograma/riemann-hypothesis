module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesConvergent
public import Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatSectionGrowthBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightContinuousPos
public import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximal
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.Khead

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem hgt_mul_right {n : ℕ} {Y : Spc F E n} {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (h : IsHgt K a) (x c : G2 σ Y) :
    ∃ k ∈ K, a (x * c) = a x * a (k * c) := by
  obtain ⟨p, t, hp, k, hk, rfl⟩ := h.iwa x
  refine ⟨k, hk, ?_⟩
  rw [mul_assoc, h.mul hp, h.val p t hp k hk]

end PositivityTheory.SiegelWeilFormula.Khead
