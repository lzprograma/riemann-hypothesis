module

public import Formalism.EisensteinCokernelLengths.ExponentChainBound
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.RingTheory.Ideal.BigOperators
public import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt
public import Formalism.WindowSums.PowerSeriesRelationList
public import Formalism.JumpKernelCokernel.Statement
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Formalism.JumpKernelCokernel.KerCokerEq
public import Formalism.JumpKernelCokernel.LemmaDJoint
public import Formalism.JumpKernelCokernel.JumpShiftProofs.KerCoker
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Formalism.TruncatedSeriesCounting.LengthQuotientLeOfPowSMul
public import Formalism.JumpKernelCokernel.JumpShiftProofs.InvConst
public import Formalism.JumpKernelCokernel.JumpShiftProofs.TorsKerSum
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColChain
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.FirstSigmaValuationBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.HCoefficientBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.KappaSecondExponentBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGIdeal
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGVal
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.RamifiedValuationInequality
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubSmulOneInjective
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ExpBound
import Formalism.JumpKernelCokernel.JumpShiftProofs.DetLen
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColAssembly
import Formalism.JumpKernelCokernel.JumpShiftProofs.LenSplit
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubGen
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.EisensteinCokernelLengths.FactorialValuationBounds.DistinguishedPowMemSpanOfTrichotomy, Formalism.JumpKernelCokernel.JumpShiftProofs.HCoefLim, Formalism.JumpKernelCokernel.JumpShiftProofs.IdealPowerSumMem, Formalism.JumpKernelCokernel.JumpShiftProofs.KerCokerEq, Formalism.JumpKernelCokernel.JumpShiftProofs.PdFacts, Formalism.JumpKernelCokernel.JumpShiftProofs.PowBinom, Formalism.JumpKernelCokernel.JumpShiftProofs.RowDJoint, Formalism.JumpKernelCokernel.JumpShiftProofs.ThickA, Formalism.JumpKernelCokernel.JumpShiftProofs.ThickB, Formalism.JumpKernelCokernel.JumpShiftProofs.TorsKer, Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier

-- ===== clump member: Formalism.EisensteinCokernelLengths.FactorialValuationBounds.DistinguishedPowMemSpanOfTrichotomy =====
-- clump-header: {"m": "Formalism.EisensteinCokernelLengths.FactorialValuationBounds.DistinguishedPowMemSpanOfTrichotomy", "h": "module\n\npublic import Formalism.EisensteinCokernelLengths.ExponentChainBound\nimport Mathlib.Algebra.Order.Floor.Extended\npublic import Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.RingTheory.Ideal.BigOperators\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

section Key

variable {A : Type} [CommRing A]

theorem rel_mem_of_le {X l : A} {M η E : ℕ} (c a i : ℕ) (h : E ≤ c) :
    l ^ c * X ^ a * (X + l) ^ i ∈ Ideal.span {l ^ E, X ^ M * (X + l) ^ η} := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have e : l ^ (E + d) * X ^ a * (X + l) ^ i = (l ^ d * X ^ a * (X + l) ^ i) * l ^ E := by ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))

theorem rel_mem_of_ge {X l : A} {M η E : ℕ} (c a i : ℕ) (ha : M ≤ a) (hi : η ≤ i) :
    l ^ c * X ^ a * (X + l) ^ i ∈ Ideal.span {l ^ E, X ^ M * (X + l) ^ η} := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le hi
  have e : l ^ c * X ^ (M + a') * (X + l) ^ (η + i') =
      (l ^ c * X ^ a' * (X + l) ^ i') * (X ^ M * (X + l) ^ η) := by ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem rel_key_high (X l : A) (M η E : ℕ) :
    ∀ j c i : ℕ, (E ≤ c ∨ η ≤ i ∨ E + η ≤ c + j + i + 1) →
      l ^ c * X ^ (M + j) * (X + l) ^ i ∈ Ideal.span {l ^ E, X ^ M * (X + l) ^ η} := by
  intro j
  induction j with
  | zero =>
    intro c i h
    by_cases hc : E ≤ c
    · exact rel_mem_of_le c _ i hc
    by_cases hi : η ≤ i
    · exact rel_mem_of_ge c _ i (Nat.le_add_right M 0) hi
    exfalso
    omega
  | succ j ih =>
    intro c i h
    by_cases hc : E ≤ c
    · exact rel_mem_of_le c _ i hc
    by_cases hi : η ≤ i
    · exact rel_mem_of_ge c _ i (Nat.le_add_right M (j + 1)) hi
    have e : l ^ c * X ^ (M + (j + 1)) * (X + l) ^ i =
        l ^ c * X ^ (M + j) * (X + l) ^ (i + 1) - l ^ (c + 1) * X ^ (M + j) * (X + l) ^ i := by
      ring
    rw [e]
    exact Ideal.sub_mem _ (ih c (i + 1) (by omega)) (ih (c + 1) i (by omega))

theorem rel_key (X l : A) (M η E : ℕ) :
    ∀ i a c : ℕ, (E ≤ c ∨ (M ≤ a ∧ η ≤ i) ∨ E + η + M ≤ c + a + i + 1) →
      l ^ c * X ^ a * (X + l) ^ i ∈ Ideal.span {l ^ E, X ^ M * (X + l) ^ η} := by
  intro i
  induction i with
  | zero =>
    intro a c h
    by_cases ha : M ≤ a
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ha
      exact rel_key_high X l M η E j c 0 (by omega)
    · exact rel_mem_of_le c a 0 (by omega)
  | succ i ih =>
    intro a c h
    by_cases ha : M ≤ a
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ha
      exact rel_key_high X l M η E j c (i + 1) (by omega)
    have e : l ^ c * X ^ a * (X + l) ^ (i + 1) =
        l ^ c * X ^ (a + 1) * (X + l) ^ i + l ^ (c + 1) * X ^ a * (X + l) ^ i := by ring
    rw [e]
    exact Ideal.add_mem _ (ih (a + 1) c (by omega)) (ih a (c + 1) (by omega))

end Key

theorem rel_ceil_le (m r K : ℕ) (hm : 1 ≤ m) (h : r * (m + 1) ≤ K * m) :
    ⌈(r : ℝ) * ((m + 1 : ℕ) : ℝ) / (m : ℝ)⌉₊ ≤ K := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  rw [Nat.ceil_le, div_le_iff₀ hm']
  exact_mod_cast h

theorem le_div_add_one_or_add_le (m r T L : ℕ) (hm : 1 ≤ m) (hL : ∀ K, r * (m + 1) ≤ K * m → L ≤ K) :
    L ≤ T / m + 1 ∨ L + T ≤ T / m + 1 + (m * r + r) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  by_cases h : L ≤ T / (n + 1) + 1
  · exact Or.inl h
  right
  have hT := Nat.div_add_mod T (n + 1)
  have ht := Nat.mod_lt T (show n + 1 > 0 by omega)
  set q := T / (n + 1) with hq0
  set t := T % (n + 1) with ht0
  have hq : (q + 1) * (n + 1) + 1 ≤ r * (n + 1 + 1) := by
    by_contra hc
    have := hL (q + 1) (by omega)
    omega
  have hK := Nat.div_add_mod (r * (n + 1 + 1) + n) (n + 1)
  have hKm := Nat.mod_lt (r * (n + 1 + 1) + n) (show n + 1 > 0 by omega)
  set K := (r * (n + 1 + 1) + n) / (n + 1) with hK0
  set ρ := (r * (n + 1 + 1) + n) % (n + 1) with hρ0
  have hLK : L ≤ K := hL K (by nlinarith)
  have a1 := Nat.mul_le_mul_left (n + 1) hLK
  have a2 := Nat.mul_le_mul_left (n + 1) (show t ≤ n by omega)
  have a3 := Nat.mul_le_mul_left n hq
  have a4 : (n + 1) * T = (n + 1) * ((n + 1) * q + t) := by rw [hT]
  apply le_of_mul_le_mul_left _ (show 0 < n + 1 by omega)
  nlinarith [a1, a2, a3, a4, hK]

theorem linearFactorPowMemSpanXPow : FirstRelationModule := by
  intro A _ ℓ _ hℓ X u M η r hM
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  have hcast : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  have hfl : ⌊((M : ℝ) + η) / (m : ℝ)⌋₊ = (M + η) / m := by
    have := Nat.floor_div_eq_div (K := ℝ) (M + η) m
    push_cast at this
    exact this
  rw [hcast, hfl]
  simp only [Nat.add_sub_cancel]
  set L := ⌈(r : ℝ) * ((m + 1 : ℕ) : ℝ) / (m : ℝ)⌉₊ with hLdef
  have hL : ∀ K, r * (m + 1) ≤ K * m → L ≤ K := fun K h => rel_ceil_le m r K (by omega) h
  have e : ((m + 1 : ℕ) : A) ^ ((M + η) / m + 1) * (u * X * (X + ((m + 1 : ℕ) : A)) ^ m) ^ r =
      u ^ r * (((m + 1 : ℕ) : A) ^ ((M + η) / m + 1) * X ^ r *
        (X + ((m + 1 : ℕ) : A)) ^ (m * r)) := by
    rw [pow_mul]; ring
  rw [e]
  apply Ideal.mul_mem_left
  apply rel_key X _ M η L (m * r) r ((M + η) / m + 1)
  have := le_div_add_one_or_add_le m r (M + η) L (by omega) hL
  omega

end Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.EisensteinCokernelLengths.FactorialValuationBounds.DistinguishedPowMemSpanOfTrichotomy =====

-- ===== clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.HCoefLim =====
-- clump-header: {"m": "Formalism.JumpKernelCokernel.JumpShiftProofs.HCoefLim", "h": "module\n\npublic import Formalism.JumpKernelCokernel.Statement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.KernelCokernelLengths.CoefficientHeightLimitLemmas

def P (s : ℝ) : ℝ := 25 + 57 * s + 40 * s ^ 2 + 8 * s ^ 3

lemma P_ge {s : ℝ} (hs : 0 ≤ s) : 25 ≤ P s := by
  unfold P
  nlinarith [pow_nonneg hs 2, pow_nonneg hs 3]

end Formalism.KernelCokernelLengths.CoefficientHeightLimitLemmas

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.HCoefLim =====

-- ===== clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.IdealPowerSumMem =====
-- clump-header: {"m": "Formalism.JumpKernelCokernel.JumpShiftProofs.IdealPowerSumMem", "h": "module\n\npublic import Formalism.JumpKernelCokernel.Statement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.KernelCokernelLengths.IdealPowerSumLemmas

theorem add_pow_mem_span_pow_pow (R : Type) [CommRing R] (π₀ ℓ : R) (A r : ℕ) :
    (π₀ + ℓ) ^ (A + r - 1) ∈ Ideal.span {π₀ ^ A, ℓ ^ r} := by
  have hπ : π₀ ^ A ∈ Ideal.span {π₀ ^ A, ℓ ^ r} := Ideal.subset_span (Set.mem_insert _ _)
  have hℓ : ℓ ^ r ∈ Ideal.span {π₀ ^ A, ℓ ^ r} :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rw [add_pow]
  refine Ideal.sum_mem _ fun i hi => ?_
  have hi' : i ≤ A + r - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hA : A ≤ i
  · have e : π₀ ^ i = π₀ ^ A * π₀ ^ (i - A) := by rw [← pow_add, Nat.add_sub_cancel' hA]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hπ))
  · have hr : r ≤ A + r - 1 - i := by omega
    have e : ℓ ^ (A + r - 1 - i) = ℓ ^ r * ℓ ^ (A + r - 1 - i - r) := by
      rw [← pow_add, Nat.add_sub_cancel' hr]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hℓ))

end Formalism.KernelCokernelLengths.IdealPowerSumLemmas

theorem Formalism.KernelCokernelLengths.ideal_power_sum_mem : Formalism.KernelCokernelLengths.QPow := by
  intro R _ π₀ ℓ A r
  exact Formalism.KernelCokernelLengths.IdealPowerSumLemmas.add_pow_mem_span_pow_pow R π₀ ℓ A r
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.IdealPowerSumMem =====

-- ===== clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.KerCokerEq =====
-- clump-header: {"m": "Formalism.JumpKernelCokernel.JumpShiftProofs.KerCokerEq", "h": "module\n\npublic import Formalism.JumpKernelCokernel.KerCokerEq\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.KernelCokernelLengths.KernelCokernelEqualityLemmas

theorem main (O : Type) [Ring O] (M : Type) [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (f : Module.End O M) :
    Module.length O (LinearMap.ker f) = Module.length O (M ⧸ LinearMap.range f) := by
  have h1 : Module.length O M =
      Module.length O (LinearMap.ker f) + Module.length O (M ⧸ LinearMap.ker f) :=
    Module.length_eq_add_of_exact _ _ (LinearMap.ker f).injective_subtype
      (LinearMap.ker f).mkQ_surjective (LinearMap.exact_subtype_mkQ _)
  have h2 : Module.length O (M ⧸ LinearMap.ker f) = Module.length O (LinearMap.range f) :=
    (f.quotKerEquivRange).length_eq
  have h3 : Module.length O M =
      Module.length O (LinearMap.range f) + Module.length O (M ⧸ LinearMap.range f) :=
    Module.length_eq_add_of_exact _ _ (LinearMap.range f).injective_subtype
      (LinearMap.range f).mkQ_surjective (LinearMap.exact_subtype_mkQ _)
  rw [h2] at h1
  have hr : Module.length O (LinearMap.range f) ≠ ⊤ := by
    intro h
    exact hM (h3.trans (by rw [h, top_add]))
  exact ENat.add_left_injective_of_ne_top hr (h1.symm.trans (h3.trans (add_comm _ _)))

theorem coker (O : Type) [Ring O] (M M' : Type) [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] (f : Module.End O M) (f' : Module.End O M')
    (g : M →ₗ[O] M') (hg : Function.Surjective g) (hc : g ∘ₗ f = f' ∘ₗ g) :
    Module.length O (M' ⧸ LinearMap.range f') ≤ Module.length O (M ⧸ LinearMap.range f) := by
  have hle : LinearMap.range f ≤ (LinearMap.range f').comap g := by
    rintro _ ⟨m, rfl⟩
    exact ⟨g m, (LinearMap.congr_fun hc m).symm⟩
  have hs : Function.Surjective (Submodule.mapQ (LinearMap.range f) (LinearMap.range f') g hle) := by
    rw [← LinearMap.range_eq_top, Submodule.range_mapQ, LinearMap.range_eq_top.mpr hg,
      Submodule.map_top, LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)]
  exact Module.length_le_of_surjective _ hs

end Formalism.KernelCokernelLengths.KernelCokernelEqualityLemmas

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.KerCokerEq =====

-- ===== clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.PdFacts =====
-- clump-header: {"m": "Formalism.JumpKernelCokernel.JumpShiftProofs.PdFacts", "h": "module\n\npublic import Formalism.JumpKernelCokernel.Statement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.KernelCokernelLengths.PolynomialDegreeLemmas

open Polynomial

variable {O : Type} [CommRing O] {V : Type} [AddCommGroup V] [Module O V]

theorem decomp (d : Module.End O V) (P : O[X]) (v : V) :
    aeval d P v = P.eval 0 • v + aeval d P.divX (d v) := by
  conv_lhs => rw [← Polynomial.divX_mul_X_add P]
  rw [map_add (f := _), map_mul, aeval_X, aeval_C, LinearMap.add_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, ← Polynomial.coeff_zero_eq_eval_zero, add_comm]

theorem aeval_mem (d : Module.End O V) (M : Submodule O V) (hM : M.map d ≤ M) :
    ∀ (Q : O[X]) (v : V), v ∈ M → aeval d Q v ∈ M := by
  have hd : ∀ v ∈ M, d v ∈ M := fun v hv => hM (Submodule.mem_map_of_mem hv)
  have hpow : ∀ (n : ℕ) (v : V), v ∈ M → (d ^ n) v ∈ M := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hd v hv)
  intro Q
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    intro v hv
    rw [map_add (f := _), LinearMap.add_apply]
    exact M.add_mem (hp v hv) (hq v hv)
  | monomial n a =>
    intro v hv
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact M.smul_mem a (hpow n v hv)

end Formalism.KernelCokernelLengths.PolynomialDegreeLemmas

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.PdFacts =====

-- ===== clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.PowBinom =====
-- clump-header: {"m": "Formalism.JumpKernelCokernel.JumpShiftProofs.PowBinom", "h": "module\n\npublic import Formalism.JumpKernelCokernel.Statement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.KernelCokernelLengths

theorem power_binomial_bound : PowBinom := by
  intro A _ ℓ u ε q b Y hℓ hY
  set k := (Y - 1) / ℓ with hk
  set I : Ideal A := Ideal.span {(ℓ : A), q ^ ℓ} with hI
  have hYle : Y ≤ ℓ * (k + 1) := by
    have h := Nat.lt_mul_div_succ (Y - 1) (show 0 < ℓ by omega)
    rw [← hk] at h
    omega
  have hmem : (u * q ^ ℓ + (ℓ : A) * ε) ^ b ∈
      Ideal.span {(ℓ : A) ^ (b - k)} ⊔ Ideal.span {q ^ Y} * I ^ (b - k - 1) := by
    rw [add_pow]
    refine Ideal.sum_mem _ (fun m hm => ?_)
    rw [Finset.mem_range] at hm
    by_cases hmk : m ≤ k
    · apply Ideal.mem_sup_left
      rw [Ideal.mem_span_singleton]
      have h1 : (ℓ : A) ^ (b - k) ∣ ((ℓ : A) * ε) ^ (b - m) := by
        rw [mul_pow]; exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h1 _) _
    · apply Ideal.mem_sup_right
      obtain ⟨e, rfl⟩ : ∃ e, m = k + 1 + e := ⟨m - (k + 1), by omega⟩
      have hℓI : (ℓ : A) ∈ I := Ideal.subset_span (by simp)
      have hqI : q ^ ℓ ∈ I := Ideal.subset_span (by simp)
      have hin : (q ^ ℓ) ^ e * (ℓ : A) ^ (b - (k + 1 + e)) ∈ I ^ (b - k - 1) := by
        have := Ideal.mul_mem_mul (Ideal.pow_mem_pow hqI e)
          (Ideal.pow_mem_pow hℓI (b - (k + 1 + e)))
        rw [← pow_add] at this
        exact Ideal.pow_le_pow_right (by omega) this
      have hp : q ^ (ℓ * (k + 1)) = q ^ Y * q ^ (ℓ * (k + 1) - Y) := by
        rw [← pow_add]; congr 1; omega
      have heq : (u * q ^ ℓ) ^ (k + 1 + e) * ((ℓ : A) * ε) ^ (b - (k + 1 + e)) *
            (b.choose (k + 1 + e) : A) =
          q ^ Y * ((q ^ ℓ) ^ e * (ℓ : A) ^ (b - (k + 1 + e)) *
            (u ^ (k + 1 + e) * q ^ (ℓ * (k + 1) - Y) * ε ^ (b - (k + 1 + e)) *
              (b.choose (k + 1 + e) : A))) := by
        have hq : (q ^ ℓ) ^ (k + 1 + e) = q ^ Y * q ^ (ℓ * (k + 1) - Y) * (q ^ ℓ) ^ e := by
          rw [pow_add, ← pow_mul, hp]
        rw [mul_pow, mul_pow, hq]
        ring
      rw [heq]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_right _ _ hin)
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨α, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨β, hβ, rfl⟩ := Ideal.mem_span_singleton_mul.mp hc
  exact ⟨α, β, by rw [← hac]; ring, hβ⟩

end Formalism.KernelCokernelLengths
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.PowBinom =====

-- ===== clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.RowDJoint =====
-- clump-header: {"m": "Formalism.JumpKernelCokernel.JumpShiftProofs.RowDJoint", "h": "module\n\npublic import Formalism.JumpKernelCokernel.LemmaDJoint\npublic import Formalism.JumpKernelCokernel.Statement\npublic import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ExpBound\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\npublic import Mathlib.Analysis.Complex.ExponentialBounds\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.KernelCokernelLengths.RowDegreeJointLemmas

end Formalism.KernelCokernelLengths.RowDegreeJointLemmas

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.RowDJoint =====

-- ===== clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.ThickA =====
-- clump-header: {"m": "Formalism.JumpKernelCokernel.JumpShiftProofs.ThickA", "h": "module\n\npublic import Formalism.JumpKernelCokernel.Statement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\npublic import Mathlib.Analysis.Complex.ExponentialBounds\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.KernelCokernelLengths.ThicknessFirstBoundLogLemmas

open Filter

lemma coef_le (x : ℝ) (hx : 11 ≤ x) : (2 * x - 1) / (x - 1) ^ 2 ≤ 21 / 100 := by
  rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < (x - 1) ^ 2)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by linarith : (0 : ℝ) ≤ x - 11 / 21)]

lemma coef_nonneg (x : ℝ) (hx : 11 ≤ x) : 0 ≤ (2 * x - 1) / (x - 1) ^ 2 := by
  exact div_nonneg (by linarith) (sq_nonneg _)

lemma one_le_log (x : ℝ) (hx : 11 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

end Formalism.KernelCokernelLengths.ThicknessFirstBoundLogLemmas

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.ThickA =====

-- ===== clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.ThickB =====
-- clump-header: {"m": "Formalism.JumpKernelCokernel.JumpShiftProofs.ThickB", "h": "module\n\npublic import Formalism.JumpKernelCokernel.Statement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\npublic import Mathlib.Analysis.Complex.ExponentialBounds\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.KernelCokernelLengths.ThicknessSecondBoundLogLemmas

lemma coef_le (ℓ : ℕ) (hℓ : 11 ≤ ℓ) :
    (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤ 21 / 100 := by
  have h : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hpos : 0 < ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hpos (by norm_num)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : (0 : ℝ) ≤ 21 * ℓ - 11)]

lemma one_le_log (ℓ : ℕ) (hℓ : 11 ≤ ℓ) : 1 ≤ Real.log (ℓ : ℝ) := by
  have h : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

end Formalism.KernelCokernelLengths.ThicknessSecondBoundLogLemmas

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.ThickB =====

-- ===== clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.TorsKer =====
-- clump-header: {"m": "Formalism.JumpKernelCokernel.JumpShiftProofs.TorsKer", "h": "module\n\npublic import Formalism.JumpKernelCokernel.Statement\npublic import Mathlib.RingTheory.PowerSeries.Trunc\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.Order.CompletePartialOrder\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.KernelCokernelLengths.TorsionKernelLengthLemmas

open PowerSeries

variable {O : Type} [CommRing O] (ℓ : O) (n k : ℕ)

abbrev J : Ideal (PowerSeries O) := Ideal.span {(X : PowerSeries O) ^ n, C (ℓ ^ k)}

noncomputable abbrev ψ : Polynomial O →+* (PowerSeries O ⧸ J ℓ n k) :=
  Polynomial.eval₂RingHom (algebraMap O (PowerSeries O ⧸ J ℓ n k)) (Ideal.Quotient.mk (J ℓ n k) X)

theorem psi_apply (P : Polynomial O) :
    ψ ℓ n k P = P.eval₂ (algebraMap O (PowerSeries O ⧸ J ℓ n k)) (Ideal.Quotient.mk (J ℓ n k) X) := rfl

theorem alg_eq (a : O) :
    algebraMap O (PowerSeries O ⧸ J ℓ n k) a = Ideal.Quotient.mk (J ℓ n k) (C a) := rfl

theorem psi_eq (P : Polynomial O) : ψ ℓ n k P = Ideal.Quotient.mk (J ℓ n k) (P : PowerSeries O) := by
  have h : ψ ℓ n k = (Ideal.Quotient.mk (J ℓ n k)).comp (Polynomial.coeToPowerSeries.ringHom) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [alg_eq]
    · simp
  rw [h]
  rfl

end Formalism.KernelCokernelLengths.TorsionKernelLengthLemmas

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.JumpKernelCokernel.JumpShiftProofs.TorsKer =====

-- ===== clump member: Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier =====
-- clump-header: {"m": "Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier", "h": "module\n\npublic import Formalism.EisensteinCokernelLengths.ExponentChainBound\npublic import Formalism.JumpKernelCokernel.KerCokerEq\npublic import Formalism.JumpKernelCokernel.LemmaDJoint\npublic import Formalism.JumpKernelCokernel.Statement\npublic import Formalism.TruncatedSeriesCounting.LengthQuotientLeOfPowSMul\npublic import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.DistinguishedPowMemSpanOfTrichotomy\npublic import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt\npublic import Formalism.WindowSums.PowerSeriesRelationList\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Algebra.AffineMonoid.UniqueSums\nimport Mathlib.Algebra.Module.StablyFree.Basic\npublic import Mathlib.LinearAlgebra.Charpoly.BaseChange\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Order.CompletePartialOrder\nimport Formalism.JumpKernelCokernel.JumpShiftProofs.DetLen\npublic import Formalism.JumpKernelCokernel.JumpShiftProofs.HCoefLim\npublic import Formalism.JumpKernelCokernel.JumpShiftProofs.IdealPowerSumMem\npublic import Formalism.JumpKernelCokernel.JumpShiftProofs.InvConst\npublic import Formalism.JumpKernelCokernel.JumpShiftProofs.KerCoker\npublic import Formalism.JumpKernelCokernel.JumpShiftProofs.KerCokerEq\nimport Formalism.JumpKernelCokernel.JumpShiftProofs.LenSplit\npublic import Formalism.JumpKernelCokernel.JumpShiftProofs.PdFacts\npublic import Formalism.JumpKernelCokernel.JumpShiftProofs.PowBinom\npublic import Formalism.JumpKernelCokernel.JumpShiftProofs.RowDJoint\npublic import Formalism.JumpKernelCokernel.JumpShiftProofs.ThickA\npublic import Formalism.JumpKernelCokernel.JumpShiftProofs.ThickB\npublic import Formalism.JumpKernelCokernel.JumpShiftProofs.TorsKer\npublic import Formalism.JumpKernelCokernel.JumpShiftProofs.TorsKerSum\nimport Mathlib.RingTheory.PowerSeries.NoZeroDivisors\nimport Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColAssembly\npublic import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColChain\nimport Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ExpBound\npublic import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.FirstSigmaValuationBound\npublic import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.HCoefficientBound\npublic import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.KappaSecondExponentBound\npublic import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGIdeal\npublic import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGVal\npublic import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.RamifiedValuationInequality\nimport Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubGen\npublic import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubSmulOneInjective\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.KernelCokernelLengths

end Formalism.KernelCokernelLengths
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier =====
