module

public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.UnitHermitianSpace
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtInt
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsEigenvalueGLOneEqCuspidalLabelGen

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsEigenvalueGLOneEqCuspidalLabelGen =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsEigenvalueGLOneEqCuspidalLabelGen", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.UnitHermitianSpace\npublic import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj\npublic import Development.WeilBound.ThetaLifts.LatticeBasics.HgtInt\npublic import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE\npublic import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable\npublic import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


omit [NumberField F] [NumberField E] in
theorem eps_one {n : ℕ} (hn : 1 ≤ n) (hc : ∀ z : E, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) {b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} {ε : ℤˣ}
    (hb : bᵀ * dbl J * b.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) : ((ε : ℤ) : E) = 1 := by
  have hD : ((dbl J).map σ)ᵀ = dbl J := by
    ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks, hJ]
  set G := bᵀ * dbl J * b.map σ with hG
  have hs : (G.map σ)ᵀ = G := by
    rw [hG, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.map_map]
    have e : (⇑σ ∘ ⇑σ) = id := funext hc
    rw [e, Matrix.map_id, hD, show (bᵀ.map σ)ᵀ = b.map σ by rw [Matrix.transpose_map, Matrix.transpose_transpose], Matrix.mul_assoc]
  have := congrFun (congrFun hs (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
  rw [hb] at this
  simpa [Matrix.fromBlocks] using this

theorem eps_unit {ε : ℤˣ} (h : ((ε : ℤ) : E) = 1) : ε = 1 := by
  rcases Int.units_eq_one_or ε with e | e
  · exact e
  · exfalso
    rw [e] at h
    have : (2 : E) = 0 := by
      have h' : ((-1 : ℤ) : E) = 1 := by exact_mod_cast h
      push_cast at h'
      linear_combination -h'
    exact two_ne_zero this

end PositivityTheory.SiegelWeilFormula.Ldexb

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsEigenvalueGLOneEqCuspidalLabelGen =====
