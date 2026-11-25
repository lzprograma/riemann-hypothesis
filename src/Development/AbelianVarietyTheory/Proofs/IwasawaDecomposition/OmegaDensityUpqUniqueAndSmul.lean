module

public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaLebUnique, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDensityUpqUniqueAndSmul

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaLebUnique =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaLebUnique", "h": "module\n\npublic import Formalism.LocalRingCardinality.DataCD\npublic import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.OmegaLebUnique

theorem omegaLeb_unique :
    ∀ (P Q : ℕ) (l l' : Measure (lieU P Q)), IsOmegaLeb l → IsOmegaLeb l' → l = l' :=
  fun _ _ _ _ h h' => GlobalTheory.CompactDualUnique.isOmegaLeb_unique h h'

end GlobalTheory.OmegaLebUnique
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaLebUnique =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDensityUpqUniqueAndSmul =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDensityUpqUniqueAndSmul", "h": "module\n\npublic import Formalism.LocalRingCardinality.DataCD\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaLebUnique\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.OmegaDensityScale

theorem omegaDensity_unique {P Q : ℕ} {μ : Measure (UpqT P Q)} {c c' : ENNReal}
    (h : OmegaDensity μ c) (h' : OmegaDensity μ c') : c' = c := by
  exact (GlobalTheory.CompactDualUnique.omegaDensity_unique h h').symm

theorem omegaDensity_smul {P Q : ℕ} {μ : Measure (UpqT P Q)} {c : ENNReal}
    (h : OmegaDensity μ c) (a : NNReal) : OmegaDensity ((a : ENNReal) • μ) (a * c) := by
  obtain ⟨l, hl, ht⟩ := h
  refine ⟨l, hl, ?_⟩
  have h2 := ENNReal.Tendsto.const_mul (a := (a : ENNReal)) ht (Or.inr ENNReal.coe_ne_top)
  refine h2.congr fun r => ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

theorem omegaDensity_unique_and_smul : ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)) (c : ENNReal),
    OmegaDensity μ c → (∀ c', OmegaDensity μ c' → c' = c) ∧
      ∀ a : NNReal, OmegaDensity ((a : ENNReal) • μ) (a * c) :=
  fun _ _ _ _ h => ⟨fun _ h' => omegaDensity_unique h h', fun a => omegaDensity_smul h a⟩

end GlobalTheory.OmegaDensityScale
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDensityUpqUniqueAndSmul =====
