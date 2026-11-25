module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.TowerValuationBounds.HermitianSumValuationBound, Formalism.TowerValuationBounds.TowerValuationProofs.SumAdditiveCharacterEqZero

-- ===== clump member: Formalism.TowerValuationBounds.HermitianSumValuationBound =====
-- clump-header: {"m": "Formalism.TowerValuationBounds.HermitianSumValuationBound", "h": "module\n\npublic import Mathlib.Analysis.SpecialFunctions.Log.PosLog\npublic import Mathlib.RingTheory.Valuation.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.ValuationGridEstimates

open Finset

def AbsValuationSumBound : Prop :=
  ∀ (W E : Type) [Fintype E] (lam val δ : W → ℝ) (absx : E → ℝ) (Wx : Finset W) (Bδ : ℝ),
    (∀ w, 0 ≤ lam w) → (∀ w, w ∉ Wx → val w = 0) →
    ∑ w ∈ Wx, lam w * val w = (∑ σ, Real.log (absx σ)) / Fintype.card E →
    (∑ w ∈ Wx, lam w * |val w| =
        (∑ σ, Real.log (absx σ)) / Fintype.card E + 2 * ∑ w ∈ Wx, lam w * max 0 (-val w)) ∧
    (∑ w ∈ Wx, lam w * |val w| ≤
        (∑ σ, Real.posLog (absx σ)) / Fintype.card E + 2 * ∑ w ∈ Wx, lam w * max 0 (-val w)) ∧
    ((∀ w, 0 ≤ δ w) → (∀ w, -(3 * δ w) ≤ val w) → (∀ F : Finset W, ∑ w ∈ F, lam w * δ w ≤ Bδ) →
      ∀ F : Finset W, ∑ w ∈ F, lam w * |val w| ≤
        (∑ σ, Real.posLog (absx σ)) / Fintype.card E + 6 * Bδ)

def PrimeLogSquareSumLtOne : Prop :=
  ∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) → ∑ l ∈ P, Real.log l / (l : ℝ) ^ 2 < 1

def PrimeLogBudget : Prop :=
  ∀ (N0 : ℕ → ℝ) (BN0 : ℝ),
    (∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) → ∑ l ∈ P, N0 l * Real.log l ≤ BN0) →
    ∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) →
      ∑ l ∈ P, (N0 l + ((l : ℝ) ^ 2)⁻¹) * Real.log l ≤ BN0 + 1

end Formalism.ValuationGridEstimates
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.TowerValuationBounds.HermitianSumValuationBound =====

-- ===== clump member: Formalism.TowerValuationBounds.TowerValuationProofs.SumAdditiveCharacterEqZero =====
-- clump-header: {"m": "Formalism.TowerValuationBounds.TowerValuationProofs.SumAdditiveCharacterEqZero", "h": "module\n\npublic import Formalism.TowerValuationBounds.HermitianSumValuationBound\npublic import Mathlib.NumberTheory.Padics.PadicVal.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.CStarAlgebra.Classes\npublic import Mathlib.Analysis.Complex.ExponentialBounds\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Presheaf\n\n"}
section -- clump:auto
@[expose] public section
noncomputable section
namespace Formalism.ValuationGridEstimates
open Finset

theorem height_bound_alt : AbsValuationSumBound := by
  intro W E _ lam val δ absx Wx Bδ hlam hsupp hpf
  classical
  have h1 : ∑ w ∈ Wx, lam w * |val w| =
      (∑ σ, Real.log (absx σ)) / Fintype.card E + 2 * ∑ w ∈ Wx, lam w * max 0 (-val w) := by
    rw [← hpf, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun w _ => ?_
    rcases le_total 0 (val w) with h | h
    · rw [abs_of_nonneg h, max_eq_left (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_right (by linarith)]; ring
  have hmean : (∑ σ, Real.log (absx σ)) / Fintype.card E ≤
      (∑ σ, Real.posLog (absx σ)) / Fintype.card E := div_le_div_of_nonneg_right
    (sum_le_sum fun σ _ => by rw [Real.posLog_def]; exact le_max_right _ _) (Nat.cast_nonneg _)
  refine ⟨h1, by linarith, fun hδ hden hB F => ?_⟩
  have h2 : ∑ w ∈ F, lam w * |val w| ≤ ∑ w ∈ Wx, lam w * |val w| :=
    (sum_le_sum_of_subset_of_nonneg subset_union_left fun w _ _ =>
      mul_nonneg (hlam w) (abs_nonneg _)).trans_eq
      (sum_subset subset_union_right fun w _ hw => by simp [hsupp w hw]).symm
  have h3 : ∑ w ∈ Wx, lam w * max 0 (-val w) ≤ 3 * Bδ := by
    refine (sum_le_sum fun w _ => show lam w * max 0 (-val w) ≤ 3 * (lam w * δ w) from ?_).trans
      (by rw [← mul_sum]; linarith [hB Wx])
    have hw : max 0 (-val w) ≤ 3 * δ w := max_le (by linarith [hδ w]) (by linarith [hden w])
    exact (mul_le_mul_of_nonneg_left hw (hlam w)).trans_eq (by ring)
  linarith

lemma log_div_sq_le_difference (m : ℕ) (hm : 4 ≤ m) :
    Real.log ((m + 1 : ℕ) : ℝ) / (((m + 1 : ℕ) : ℝ)) ^ 2 ≤
      (1 + Real.log m) / m - (1 + Real.log ((m + 1 : ℕ) : ℝ)) / ((m + 1 : ℕ) : ℝ) := by
  have hx : (4 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast; set x : ℝ := (m : ℝ)
  let L1 := Real.log (x + 1); let L0 := Real.log x
  have hdiff : L1 - L0 ≤ 1 / x := by
    have h2 := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    rw [Real.log_div (by positivity) (by positivity),
      show (x + 1) / x - 1 = 1 / x by field_simp; ring] at h2; exact h2
  have hbig : (5 : ℝ) / 4 ≤ L1 := by
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ x + 1),
      show Real.log (4 : ℝ) = 2 * Real.log 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num, Real.log_two_gt_d9]
  have hcomb : (1 + L0) / x - (1 + L1) / (x + 1) - L1 / (x + 1) ^ 2 =
      (L1 * x - x - 1) / (x ^ 2 * (x + 1) ^ 2) + (L0 - L1 + 1 / x) / x := by field_simp; ring
  linarith [div_nonneg (by linarith [mul_le_mul_of_nonneg_right hbig (by linarith : (0 : ℝ) ≤ x)] : 0 ≤ L1 * x - x - 1)
      (by positivity : 0 ≤ x ^ 2 * (x + 1) ^ 2),
    div_nonneg (by linarith : 0 ≤ L0 - L1 + 1 / x) (by positivity : 0 ≤ x)]

lemma sum_log_div_sq_telescoping (M : ℕ) (hM : 4 ≤ M) :
    ∑ n ∈ Icc 5 M, Real.log n / (n : ℝ) ^ 2 ≤ (1 + Real.log 4) / 4 - (1 + Real.log M) / M := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih => rw [sum_Icc_succ_top (by omega)]; linarith [log_div_sq_le_difference M hM]

theorem prime_sum_bound : PrimeLogSquareSumLtOne := by
  intro P hP; let M : ℕ := max (P.sup id) 4
  have hsub : P ⊆ {2, 3} ∪ Icc 5 M := fun l hl => by
    have hp := hP l hl; have := hp.two_le
    have : l ≤ M := (le_sup (f := id) hl).trans (le_max_left _ _)
    have : l ≠ 4 := by rintro rfl; exact absurd hp (by decide)
    simp only [mem_union, mem_insert, mem_singleton, mem_Icc]; omega
  have h1 := sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
    div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg (n : ℝ))
  rw [sum_union (disjoint_left.mpr fun _ a b => by
      simp only [mem_insert, mem_singleton, mem_Icc] at a b; omega),
    sum_pair (by decide)] at h1; push_cast at h1
  linarith [sum_log_div_sq_telescoping M (le_max_right _ _),
    div_nonneg (by linarith [Real.log_natCast_nonneg M] : 0 ≤ 1 + Real.log M) (Nat.cast_nonneg M),
    show Real.log (4 : ℝ) = 2 * Real.log 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num,
    Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 4), Real.log_two_lt_d9]

theorem prime_budget_bound : PrimeLogBudget := fun N0 BN0 h P hP => by
  simp only [add_mul, sum_add_distrib, inv_mul_eq_div]
  linarith [h P hP, prime_sum_bound P hP]

end Formalism.ValuationGridEstimates
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.TowerValuationBounds.TowerValuationProofs.SumAdditiveCharacterEqZero =====
