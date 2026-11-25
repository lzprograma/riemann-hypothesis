module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersOfGenerators
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

open PowerSeries Finset

variable {B : Type} [CommRing B]

def ser (g : ℕ → B) (a : B) : B⟦X⟧ := PowerSeries.mk fun n ↦ a ^ n * g n

theorem ser_zero {g : ℕ → B} (h0 : g 0 = 1) : ser g 0 = 1 := by
  ext n
  rcases n with _ | n <;> simp [ser, h0, coeff_one]

theorem ser_add {g : ℕ → B} (hmul : ∀ m n, g m * g n = ((m + n).choose m : B) * g (m + n)) (a b : B) :
    ser g (a + b) = ser g a * ser g b := by
  ext n
  simp only [ser, coeff_mul, coeff_mk, (Commute.all a b).add_pow', Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have := hmul p.1 p.2
  rw [e] at this
  rw [nsmul_eq_mul]
  linear_combination (-(a ^ p.1 * b ^ p.2)) * this

theorem ser_mul (g : ℕ → B) (a b : B) : ser g (a * b) = rescale a (ser g b) := by
  ext n
  simp only [ser, coeff_rescale, coeff_mk, mul_pow, mul_assoc]

def IsExp (f : B⟦X⟧) : Prop := ∀ m n, coeff m f * coeff n f = ((m + n).choose m : B) * coeff (m + n) f

theorem IsExp.mul {f g : B⟦X⟧} (hf : IsExp f) (hg : IsExp g) : IsExp (f * g) := by
  intro m n
  simp only [coeff_mul]
  have e : ((m + n).choose m : B) * ∑ p ∈ HasAntidiagonal.antidiagonal (m + n), coeff p.1 f * coeff p.2 g =
      ∑ i ∈ HasAntidiagonal.antidiagonal m, ∑ p ∈ HasAntidiagonal.antidiagonal (m + n),
        (p.1.choose i.1 : B) * (p.2.choose i.2 : B) * (coeff p.1 f * coeff p.2 g) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, Nat.add_choose_eq, ← Finset.sum_mul]
    push_cast
    rfl
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.HasAntidiagonal.mem_antidiagonal.1 hi
  rw [Finset.mul_sum]
  refine Finset.sum_of_injOn (fun k : ℕ × ℕ ↦ (i.1 + k.1, i.2 + k.2)) ?_ ?_ ?_ ?_
  · intro k _ l _ h
    simp only [Prod.mk.injEq, add_right_inj] at h
    exact Prod.ext h.1 h.2
  · intro k hk
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hk
    exact Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp only; omega)
  · intro p hp hn
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h1 : p.1 < i.1
    · simp [Nat.choose_eq_zero_of_lt h1]
    by_cases h2 : p.2 < i.2
    · simp [Nat.choose_eq_zero_of_lt h2]
    refine absurd ⟨(p.1 - i.1, p.2 - i.2), Finset.mem_coe.2 (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp only; omega)), ?_⟩ hn
    exact Prod.ext (by simp only; omega) (by simp only; omega)
  · intro k _
    have a := hf i.1 k.1
    have b := hg i.2 k.2
    simp only
    linear_combination (coeff i.2 g * coeff k.2 g) * a + (((i.1 + k.1).choose i.1 : B) * coeff (i.1 + k.1) f) * b

theorem pre_of_gens (B ι : Type) [CommRing B] (x : ι → B) (g : ι → ℕ → B) (h0 : ∀ i, g i 0 = 1)
    (h1 : ∀ i, g i 1 = x i) (hm : ∀ i n, n ≠ 0 → g i n ∈ Ideal.span (Set.range x))
    (hmul : ∀ i m n, g i m * g i n = ((m + n).choose m : B) * g i (m + n))
    (hrel : ∀ c : ι →₀ B, (c.sum fun i a ↦ a * x i) = 0 →
      (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * g i n) = 1) :
    ∃ γ : ℕ → B → B, IsPreDP (Ideal.span (Set.range x)) γ ∧ ∀ i n, γ n (x i) = g i n := by
  apply GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ <;> assumption

end FubiniStudyChowHeightFormula₂.Adr
