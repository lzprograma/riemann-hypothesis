module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Mathlib.Tactic.NormNum.LegendreSymbol

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonZeroDivisorOfDenseOfStrict, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsComplNonZeroDivisor

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonZeroDivisorOfDenseOfStrict =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonZeroDivisorOfDenseOfStrict", "h": "module\n\npublic import Mathlib.RingTheory.AdicCompletion.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory.CompanionTheory.ComplReg

theorem nonZeroDivisor_of_dense_of_strict {B T : Type} [CommRing B] [CommRing T] (π : B)
    (g : B →+* T) (hH : IsHausdorff (Ideal.span {g π}) T)
    (hd : ∀ (M : ℕ) (y : T), ∃ x, y - g x ∈ Ideal.span {g π ^ M})
    (hk : ∀ (M : ℕ) (x : B), g x ∈ Ideal.span {g π ^ M} → x ∈ Ideal.span {π ^ M})
    (hπ : π ∈ nonZeroDivisors B) : g π ∈ nonZeroDivisors T := by
  have key : ∀ t : T, t * g π = 0 → ∀ M : ℕ, t ∈ Ideal.span {g π ^ M} := by
    intro t ht M
    obtain ⟨x, hx⟩ := hd M t
    rw [Ideal.mem_span_singleton] at hx
    obtain ⟨d, hd'⟩ := hx
    have hxπ : x * π ∈ Ideal.span {π ^ (M + 1)} := by
      apply hk (M + 1) (x * π)
      rw [Ideal.mem_span_singleton]
      exact ⟨-d, by rw [map_mul]; linear_combination ht - g π * hd'⟩
    rw [Ideal.mem_span_singleton] at hxπ
    obtain ⟨c, hc⟩ := hxπ
    have h0 : (x - π ^ M * c) * π = 0 := by
      rw [sub_mul, hc]
      ring
    have hxeq : x = π ^ M * c := sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hπ).2 _ h0)
    have hgx : g x = g π ^ M * g c := by
      rw [hxeq, map_mul, map_pow]
    rw [Ideal.mem_span_singleton]
    exact ⟨d + g c, by linear_combination hd' + hgx⟩
  have main : ∀ t : T, t * g π = 0 → t = 0 := by
    intro t ht
    refine IsHausdorff.haus hH t (fun n => ?_)
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact key t ht n
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun t ht => main t (by rwa [mul_comm] at ht), main⟩

end GlobalTheory.CompanionTheory.ComplReg
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonZeroDivisorOfDenseOfStrict =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsComplNonZeroDivisor =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsComplNonZeroDivisor", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonZeroDivisorOfDenseOfStrict\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.ComplReg

theorem isCompl_nonZeroDivisor : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T),
    IsCompl π g → π ∈ nonZeroDivisors B → g π ∈ nonZeroDivisors T := by
  intro B _ T _ π g hC hπ
  exact nonZeroDivisor_of_dense_of_strict π g hC.compl.toIsHausdorff hC.surj hC.inj hπ

end GlobalTheory.CompanionTheory.ComplReg
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsComplNonZeroDivisor =====
