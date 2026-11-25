module

public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj

namespace GlobalTheory.ValClosure

theorem vV_eq_of_hasVal {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {x : FractionRing V} {n : ℤ} (h : ReciprocityTheory.ChartRestriction.G.DVR.HasVal ϖ x n) : vV V x = n := by
  obtain ⟨u, rfl⟩ := h
  have h1 : valV V (algebraMap V (FractionRing V) ϖ) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq
  have hle : ∀ w : V, valV V (algebraMap V (FractionRing V) w) ≤ 1 := fun w =>
    HeightOneSpectrum.valuation_le_one _ w
  have h2 : valV V (algebraMap V (FractionRing V) (u : V)) = 1 := by
    refine le_antisymm (hle _) ?_
    have h3 : valV V (algebraMap V (FractionRing V) (u : V)) *
        valV V (algebraMap V (FractionRing V) ((u⁻¹ : Vˣ) : V)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ valV V (algebraMap V (FractionRing V) (u : V)) * 1 := mul_le_mul' le_rfl (hle _)
      _ = _ := _root_.mul_one _
  rw [vV, map_mul, h2, _root_.mul_one, map_zpow₀, h1, WithZero.log_zpow, WithZero.log_exp]
  simp

theorem exists_valuation_closure : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∃ v : AddValuation (AlgebraicClosure (FractionRing V)) (WithTop ℚ), ValOver ϖ (AlgebraicClosure (FractionRing V)) v ∧ ∀ x : FractionRing V, x ≠ 0 → v (algebraMap _ _ x) = (((vV V x : ℤ) : ℚ) : WithTop ℚ) := by
  intro V _ _ _ ϖ hϖ
  obtain ⟨v, hv⟩ := GlobalTheory.exists_valOver_of_isAlgebraic hϖ (AlgebraicClosure (FractionRing V))
  refine ⟨v, hv, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ hx
  rw [vV_eq_of_hasVal hϖ hn]
  exact hv x n hn

end GlobalTheory.ValClosure
