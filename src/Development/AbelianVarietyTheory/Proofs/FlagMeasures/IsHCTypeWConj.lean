module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
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
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LinMulti

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.ConjTypeW

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

variable {k : ℕ}

theorem lowK_allPos (lam : Fin k → ℝ) (a : Fin k) :
    Formalism.QuantumDeterminants.lowK (allPos k) lam a = lam a - (((k : ℝ) - 1) / 2 - (a : ℕ)) := by
  have h1 : (Finset.univ.filter fun b : Fin k => a < b) = Finset.Ioi a := by ext b; simp
  have h2 : (Finset.univ.filter fun b : Fin k => b < a) = Finset.Iio a := by ext b; simp
  have h3 : (a : ℕ) + 1 ≤ k := a.2
  simp only [allPos, Formalism.QuantumDeterminants.lowK, Formalism.REAL.rhoN, Formalism.REAL.rhoC, Pi.sub_apply, Pi.add_apply, ne_eq, not_true_eq_false,
    and_false, and_true, Finset.filter_false, Finset.card_empty, h1, h2, Fin.card_Ioi, Fin.card_Iio]
  rw [show k - 1 - (a : ℕ) = k - ((a : ℕ) + 1) by omega, Nat.cast_sub h3]
  push_cast; ring

theorem lowK_neg_rev (u : Fin k → ℝ) :
    Formalism.QuantumDeterminants.lowK (allPos k) (fun i => -u (Fin.rev i)) = fun a => -Formalism.QuantumDeterminants.lowK (allPos k) u (Fin.rev a) := by
  funext a
  rw [lowK_allPos, lowK_allPos, Fin.val_rev, Nat.cast_sub a.2]
  push_cast
  ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end GlobalTheory.ConjTypeW
