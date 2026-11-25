module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfSpanAndTaylorClauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PchernOfStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSpanDeRhamHomologyRankTwoGStatement

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodComparisonHolds

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodComparisonHolds =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodComparisonHolds", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfSpanAndTaylorClauses\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PchernOfStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSpanDeRhamHomologyRankTwoGStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

theorem GlobalTheory.PeriodFamily.periodComparison_holds : GlobalTheory.Published.PeriodComparison :=
  ⟨-1, fun A _ g hA hg L hL u ↦ by
    obtain ⟨P, hP⟩ := GlobalTheory.AnPer.pHom A g hA L u
    have hS := GlobalTheory.T.periods_span_deRhamHomology_rank_two_g A g hA hg L u P hP
    exact ⟨P, hS.1, hS.2, GlobalTheory.T.integrationOverCycles_lifts_lieLattice A g hA hg L u P hP,
      fun α _ M ↦ GlobalTheory.T.periodHom_push_end' A g hA L u P hP α M,
      fun H χ ψ ↦ GlobalTheory.T.pChern_neg_one A g hA L u P hP L u hL rfl H χ ψ⟩⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodComparisonHolds =====
