module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Northcott

theorem isIntegral_eig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsIntegral ℤ M) {w : ℂ}
    {x : Fin n → ℂ} (hx : x ≠ 0) (hMx : M *ᵥ x = w • x) : IsIntegral ℤ w := by
  obtain ⟨q, hq, hqM⟩ := hM
  refine ⟨q, hq, ?_⟩
  have hv : Module.End.HasEigenvector (Matrix.toLin' M) w x :=
    ⟨Module.End.mem_eigenspace_iff.2 (by simpa [Matrix.toLin'_apply] using hMx), hx⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q.map (algebraMap ℤ ℂ)) hv
  have h2 : Polynomial.aeval (Matrix.toLin' M) (q.map (algebraMap ℤ ℂ)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    have e := Polynomial.aeval_algHom_apply
      ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] _).toAlgHom.restrictScalars ℤ) M q
    have e2 : Polynomial.aeval M q = 0 := hqM
    rw [e2, map_zero] at e
    exact e
  rw [h2, LinearMap.zero_apply] at h1
  have h3 := (smul_eq_zero.1 h1.symm).resolve_right hx
  rwa [Polynomial.eval_map] at h3

theorem norm_le_of_isIntegral_inv (w : ℂ) (c : ℚ) (N : ℕ) (hN : 0 < N) (hw : ‖w‖ ^ 2 = (c : ℝ))
    (hc : (c : ℝ) ≠ 0) (hI : IsIntegral ℤ ((N : ℂ) * w⁻¹)) : ‖w‖ ≤ N := by
  have hcpos : (0 : ℝ) < c := lt_of_le_of_ne (hw ▸ sq_nonneg _) (Ne.symm hc)
  have hconj : IsIntegral ℤ (starRingEnd ℂ ((N : ℂ) * w⁻¹)) := hI.map (starRingEnd ℂ).toIntAlgHom
  have hprod := hI.mul hconj
  have e : (N : ℂ) * w⁻¹ * starRingEnd ℂ ((N : ℂ) * w⁻¹) = (((N : ℚ) ^ 2 / c : ℚ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, norm_inv, mul_pow, inv_pow, hw,
      Complex.norm_natCast]
    push_cast
    ring
  rw [e] at hprod
  have hq : IsIntegral ℤ ((N : ℚ) ^ 2 / c) := by
    refine (isIntegral_algHom_iff ((algebraMap ℚ ℂ).toIntAlgHom) (algebraMap ℚ ℂ).injective
      (x := (N : ℚ) ^ 2 / c)).1 ?_
    simpa using hprod
  obtain ⟨k, hk⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hq
  have hcq : (0 : ℚ) < c := by exact_mod_cast hcpos
  have hpos : (0 : ℚ) < (N : ℚ) ^ 2 / c := by positivity
  have hk1 : (1 : ℚ) ≤ (N : ℚ) ^ 2 / c := by
    rw [← hk] at hpos ⊢
    rw [algebraMap_int_eq, eq_intCast] at hpos ⊢
    have : (0 : ℤ) < k := by exact_mod_cast hpos
    have : (1 : ℤ) ≤ k := this
    exact_mod_cast this
  have hcN : (c : ℚ) ≤ (N : ℚ) ^ 2 := by rwa [le_div_iff₀ hcq, one_mul] at hk1
  have hcN' : (c : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hcN
  rw [← hw] at hcN'
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Nat.cast_nonneg _) two_ne_zero).1 hcN'

end GlobalTheory.LKMid.Northcott
