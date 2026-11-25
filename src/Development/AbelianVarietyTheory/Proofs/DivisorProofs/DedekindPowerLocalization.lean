module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLocalContinuousCongruenceSection, Development.AbelianVarietyTheory.Proofs.DivisorProofs.DedekindPowerLocalization

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLocalContinuousCongruenceSection =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLocalContinuousCongruenceSection", "h": "module\n\npublic import Mathlib.RingTheory.DedekindDomain.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.RingTheory.DedekindDomain.Ideal.Basic\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory

theorem dedekind_pow_maximal_mul_mem_span (B : Type) [CommRing B] [IsDedekindDomain B] (f : B)
    (hf : f ≠ 0) (P : Ideal B) (hP : P.IsMaximal) :
    ∃ N : ℕ, ∀ b ∈ P ^ N, ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  classical
  have hI0 : Ideal.span {f} ≠ (0 : Ideal B) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hf
  have hPu : ¬ IsUnit P := by
    rw [Ideal.isUnit_iff]; exact hP.ne_top
  have hfin : FiniteMultiplicity P (Ideal.span {f}) := FiniteMultiplicity.of_not_isUnit hPu hI0
  have key : ¬ P ^ (multiplicity P (Ideal.span {f}) + 1) ∣ Ideal.span {f} :=
    hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  have hdvd : P ^ (multiplicity P (Ideal.span {f})) ∣ Ideal.span {f} := pow_multiplicity_dvd P _
  generalize multiplicity P (Ideal.span {f}) = m at key hdvd
  obtain ⟨J, hJ⟩ := hdvd
  refine ⟨m, ?_⟩
  have hJP : ¬ J ≤ P := by
    intro hle
    have hd : P ∣ J := Ideal.dvd_iff_le.mpr hle
    apply key
    rw [hJ, pow_succ]
    exact mul_dvd_mul_left _ hd
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.mp hJP
  intro b hb
  refine ⟨s, hsP, ?_⟩
  have hmem : b * s ∈ P ^ m * J := Ideal.mul_mem_mul hb hsJ
  rw [← hJ] at hmem
  rw [mul_comm]
  exact hmem

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLocalContinuousCongruenceSection =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DedekindPowerLocalization =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.DedekindPowerLocalization", "h": "module\n\npublic import Mathlib.RingTheory.DedekindDomain.Basic\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLocalContinuousCongruenceSection\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section


end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DedekindPowerLocalization =====
