module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarChartIntegralComparison
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivative, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivativeStatement

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivative =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivative", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend\npublic import Mathlib.Analysis.LocallyConvex.AbsConvexOpen\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarChartIntegralComparison\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\npublic import Mathlib.Analysis.Calculus.Deriv.Prod\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA

noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.ExpCurve

section Entries

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_entry {n : ℕ} (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n) i j)
      ((NormedSpace.exp (t • X) * X : Mat n) i j) t := by
  haveI : FiniteDimensional ℝ (Mat n) := inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ))
  haveI : CompleteSpace (Mat n) := FiniteDimensional.complete ℝ (Mat n)
  have h : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n))
      (NormedSpace.exp (t • X) * X : Mat n) t := hasDerivAt_exp_smul_const X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt t h

end Entries

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_exp {n : ℕ} (X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  exact hasDerivAt_exp_entry X t i j

theorem expC_continuous_hasDerivAt :
    ∀ (n : ℕ) (X : Mat n), Continuous (expC X) ∧
      ∀ t : ℝ, HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  intro n X
  refine ⟨?_, hasDerivAt_exp X⟩
  refine (GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG (n := n)).isInducing.continuous_iff.2 ?_
  exact continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp X t).continuousAt

end GlobalTheory.CompanionTheory.PresSobA.ExpCurve
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivative =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivativeStatement =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivativeStatement", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend\npublic import Mathlib.Analysis.LocallyConvex.AbsConvexOpen\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivative\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
noncomputable section

theorem _root_.GlobalTheory.T.matrix_exp_curve_derivative : ∀ (n : ℕ) (X : Mat n), Continuous (expC X) ∧ ∀ t : ℝ, HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.ExpCurve.expC_continuous_hasDerivAt
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivativeStatement =====
