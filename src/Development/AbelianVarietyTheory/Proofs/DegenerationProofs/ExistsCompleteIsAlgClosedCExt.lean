module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem exists_complete_isAlgClosed_cExt :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (K : Type) [Field K] [Algebra (FractionRing W) K] [Algebra.IsAlgebraic (FractionRing W) K], ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (gam : K →+* C), (∀ x, gam (algebraMap (FractionRing W) K x) = algebraMap (FractionRing W) C x) ∧ CExt W (IsLocalRing.maximalIdeal W) C := by
  intro W _ _ _ K _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hmax : IsLocalRing.maximalIdeal W = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπm : π ∈ IsLocalRing.maximalIdeal W := hmax ▸ Ideal.mem_span_singleton_self π
  obtain ⟨C, i1, i2, i3, i4, i5, h1, h2⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing W (FractionRing W) hπ.ne_zero hπm
      (r := 1 / 2) (by norm_num) (by norm_num)
  have hle : ∀ r : W, ‖algebraMap (FractionRing W) C (algebraMap W _ r)‖ ≤ 1 :=
    fun r => (h1 _).2 ⟨r, rfl⟩
  let g : K →ₐ[FractionRing W] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨C, i1, i2, i3, i4, i5, g.toRingHom, fun x => g.commutes x, hle, fun r hr => ?_⟩
  rw [hmax, Ideal.mem_span_singleton] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [map_mul, map_mul, norm_mul, h2]
  have := hle s
  linarith

end GlobalTheory.Ex
