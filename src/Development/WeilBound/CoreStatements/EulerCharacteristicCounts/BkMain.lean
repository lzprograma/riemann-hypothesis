module

public import Formalism.WeaklyAdmissibleFiltrations.StatementTor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

theorem le_of_growth {q a b C : ℕ} (hq : 2 ≤ q) (h : ∀ r : ℕ, q ^ (r * a) ≤ C * q ^ (r * b)) :
    a ≤ b := by
  by_contra hab
  have hba : b + 1 ≤ a := by omega
  have hq0 : 0 < q := by omega
  have h1 := h C
  have h2 : q ^ (C * (b + 1)) ≤ q ^ (C * a) :=
    Nat.pow_le_pow_right hq0 (Nat.mul_le_mul_left _ hba)
  have h3 : q ^ (C * b) * q ^ C ≤ q ^ (C * b) * C := by
    calc q ^ (C * b) * q ^ C = q ^ (C * (b + 1)) := by rw [Nat.mul_add, Nat.mul_one, pow_add]
      _ ≤ C * q ^ (C * b) := h2.trans h1
      _ = q ^ (C * b) * C := by ring
  have h4 : q ^ C ≤ C := Nat.le_of_mul_le_mul_left h3 (pow_pos hq0 _)
  have h5 : C < q ^ C := Nat.lt_pow_self (by omega)
  omega


end PositivityTheory.LocalTateOrthogonality.Bk
