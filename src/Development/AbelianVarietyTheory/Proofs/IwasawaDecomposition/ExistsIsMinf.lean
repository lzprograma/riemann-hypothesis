module

public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinfOfDensity, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinf

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinfOfDensity =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinfOfDensity", "h": "module\n\npublic import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply\npublic import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR MeasureTheory
open scoped ENNReal NNReal

namespace GlobalTheory.MinfMeasure

theorem exists_isMinf_of_density {p q : ℕ} (μ : Measure (UpqT p q)) (hμ : μ.IsHaarMeasure) (c : ℝ≥0∞)
    (h0 : c ≠ 0) (ht : c ≠ ⊤) (hc : OmegaDensity μ c) : ∃ m : Measure (UpqT p q), Lev.IsMinf m := by
  haveI : IsTopologicalGroup (UpqT p q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq p q))
  haveI : BorelSpace (UpqT p q) := ⟨rfl⟩
  have hm0 : minfDensity (p + q) ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top (by simp))
  have hmt : minfDensity (p + q) ≠ ⊤ := ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)
  have hne0 : minfDensity (p + q) / c ≠ 0 := ENNReal.div_ne_zero.2 ⟨hm0, ht⟩
  have hnet : minfDensity (p + q) / c ≠ ⊤ := ENNReal.div_ne_top hmt h0
  lift minfDensity (p + q) / c to ℝ≥0 using hnet with t htc
  refine ⟨t • μ, Measure.IsHaarMeasure.nnreal_smul μ (by exact_mod_cast hne0), ?_⟩
  have h := GlobalTheory.CompactDualUnique.omegaDensity_smul t hc
  rwa [htc, ENNReal.div_mul_cancel h0 ht] at h

theorem exists_isMinf_of_cd (h : Nonempty CDHaar) (p q : ℕ) : ∃ m : Measure (UpqT p q), Lev.IsMinf m := by
  obtain ⟨cd⟩ := h
  obtain ⟨c, h0, ht, hc, -⟩ := cd.trick p q
  exact exists_isMinf_of_density _ (cd.haar p q) c h0 ht hc

end GlobalTheory.MinfMeasure
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinfOfDensity =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinf =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinf", "h": "module\n\npublic import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply\npublic import Formalism.LocalRingCardinality.DataCD\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinfOfDensity\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.IndefR MeasureTheory

namespace GlobalTheory.MinfMeasure

theorem exists_isMinf : ∀ p q : ℕ, ∃ m : Measure (UpqT p q), Lev.IsMinf m :=
  exists_isMinf_of_cd _root_.GlobalTheory.CompactDualExists.nonempty_cdHaar

end GlobalTheory.MinfMeasure
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinf =====
