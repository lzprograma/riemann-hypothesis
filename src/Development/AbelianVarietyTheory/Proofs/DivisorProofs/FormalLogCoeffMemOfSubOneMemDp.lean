module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesCoeffsInIdealPowEqFactorialMul
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius

@[expose] public section

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
  GlobalTheory.FormalCalc

namespace GlobalTheory.DPLog

theorem finsum_mem_addSubmonoid {M ι : Type*} [AddCommMonoid M] (S : AddSubmonoid M)
    {f : ι → M} (hf : ∀ i, f i ∈ S) : ∑ᶠ i, f i ∈ S := by
  classical
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum f h]; exact S.sum_mem fun i _ => hf i
  · rw [finsum_of_infinite_support h]; exact S.zero_mem

theorem formalLog_in_of_sub_one_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B]
    [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ →
    ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ : Type) (h : MvPowerSeries σ B),
    constantCoeff h = 1 → (∀ α, coeff α (h - 1) ∈ J) →
    In J (formalLog (map (algebraMap B Q) h)) := by
  intro p _ B O Q _ _ _ _ _ θ hF J hJ σ h h1 hJh
  let S : AddSubmonoid Q := J.toAddSubmonoid.map (algebraMap B Q).toAddMonoidHom
  have hS : ∀ q, q ∈ S ↔ ∃ b ∈ J, q = algebraMap B Q b := fun q =>
    AddSubmonoid.mem_map.trans
      ⟨fun ⟨b, hb, e⟩ => ⟨b, hb, e.symm⟩, fun ⟨b, hb, e⟩ => ⟨b, hb, e.symm⟩⟩
  have hww : map (algebraMap B Q) h - 1 = map (algebraMap B Q) (h - 1) := by
    rw [map_sub, map_one]
  have hsub : PowerSeries.HasSubst (map (algebraMap B Q) h - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp [h1])
  intro α
  refine (hS _).1 ?_
  rw [formalLog, PowerSeries.coeff_subst hsub]
  refine finsum_mem_addSubmonoid S fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [S.zero_mem]
  obtain ⟨y, hy, hwy⟩ :=
    DPSeries.pow_eq_factorial_mul p B O Q θ hF J hJ σ (h - 1) hJh d hd
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  refine (hS _).2 ⟨((-1 : B) ^ (k + 2) * (k.factorial : B)) * coeff α y,
    J.mul_mem_left _ (hy α), ?_⟩
  rw [hww, ← map_pow, hwy, coeff_map, ← map_natCast (C (σ := σ) (R := B)), coeff_C_mul,
    PowerSeries.coeff_log, ite_eq_right (Nat.succ_ne_zero k), smul_eq_mul]
  have e : algebraMap ℚ Q ((k + 1 : ℕ) : ℚ)⁻¹ * ((k + 1 : ℕ) : Q) = 1 := by
    rw [← map_natCast (algebraMap ℚ Q), ← map_mul, inv_mul_cancel₀ (by positivity), map_one]
  rw [div_eq_mul_inv, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_neg, map_neg,
    map_one, map_one, map_natCast, map_natCast, Nat.factorial_succ, Nat.cast_mul]
  linear_combination ((-1 : Q) ^ (k + 2) * (k.factorial : Q) * algebraMap B Q (coeff α y)) * e

end GlobalTheory.DPLog
