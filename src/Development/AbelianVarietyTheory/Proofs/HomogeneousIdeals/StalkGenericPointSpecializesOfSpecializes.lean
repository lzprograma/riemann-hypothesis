module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Scheme
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
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.PowerSeries.Evaluation
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace GlobalTheory

section ThetaShiftProofs

open PowerSeries

theorem exists_algHom_powerSeries_apply_X_of_isAdicComplete {O : Type*} [CommRing O] (I : Ideal O)
    [h : IsAdicComplete I O] {π : O} (hπ : π ∈ I) : ∃ ev : O⟦X⟧ →ₐ[O] O, ev X = π := by
  let : WithIdeal O := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨h1, h2⟩ := hI.isAdicComplete_iff.mp h
  have ha : PowerSeries.HasEval π := WithIdeal.isTopologicallyNilpotent_of_mem hπ
  refine ⟨PowerSeries.aeval ha, ?_⟩
  rw [← Polynomial.coe_X, PowerSeries.aeval_coe, Polynomial.aeval_X]

variable {Z : Scheme.{u}} {η ξ : Z} [IsDomain (Z.presheaf.stalk η)]
  [IsDiscreteValuationRing (Z.presheaf.stalk η)]
  {O : Type u} [CommRing O] [IsDomain O] [IsLocalRing O]

end ThetaShiftProofs

end GlobalTheory
