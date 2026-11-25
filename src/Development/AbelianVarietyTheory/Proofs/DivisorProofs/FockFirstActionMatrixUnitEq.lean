module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CommuteRowOpRightMixedOp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqZeroOfPartialSumsNonneg
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.Capelli GlobalTheory.Harm

namespace GlobalTheory.CompactHarm

variable {m k l : ℕ}

theorem omE_pp {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = true) (hv : linePos v = true)
    (P : Pol p q r s) :
    omE u v P = X u * pderiv v P + (if u = v then (1 / 2 : ℂ) else 0) • P := by
  simp only [omE, raiB, lowB, hu, hv, ite_true]
  split_ifs <;> simp

theorem omE_nn {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = false) (hv : linePos v = false)
    (P : Pol p q r s) :
    omE u v P = -(X v * pderiv u P) - (if u = v then (1 / 2 : ℂ) else 0) • P := by
  have : omE u v P = -(pderiv u (X v * P)) + (if u = v then (1 / 2 : ℂ) else 0) • P := by
    simp only [omE, raiB, lowB, hu, hv, Bool.false_eq_true, ite_false]
    split_ifs <;> simp
  rw [this, pderiv_X_mul']
  split_ifs
  · module
  · simp

end GlobalTheory.CompactHarm
