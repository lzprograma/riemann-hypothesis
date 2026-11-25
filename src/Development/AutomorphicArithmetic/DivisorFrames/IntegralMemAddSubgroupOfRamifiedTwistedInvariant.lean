module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
public import Formalism.DoubleCosetMeasures.StatementZ
public import Formalism.DoubleCosetMeasures.Statement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanAntitone
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralShellsVanishBeyondPeriodRamified
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Algebra.Order.Star.Real
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Mathlib.RingTheory.SimpleRing.Principal
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.Style
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Tactic.Linter.HaveILetI
import Aesop.Main
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Order.CompletePartialOrder

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableHaarVolOfLintegral, Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAbsPowIntegersFinite, Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAffineAbsPowBound, Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMatrixFirstRowColumn, Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralDetPowIntegerMatricesFinite, Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableDetPowIndicatorIntegerGl, Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableZetaIntegralMatrixSchwartz, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzero, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellSumEquivariantNonzero, Development.AutomorphicArithmetic.DivisorFrames.SetIntegralMemAddSubgroupOfOpenSubgroupInvariant, Development.AutomorphicArithmetic.DivisorFrames.IntegralMemAddSubgroupOfRamifiedTwistedInvariant

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableHaarVolOfLintegral =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableHaarVolOfLintegral", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB\nimport Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization\nimport Formalism.DoubleCosetMeasures.StatementZ\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Algebra.Group.Matrix\nimport Mathlib.Topology.LocallyConstant.Algebra\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.DoubleCosetMeasures.Statement\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical

noncomputable section
namespace GlobalTheory.GJTransfer

theorem det_mem_integer {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (X : Matrix (Fin n) (Fin n) k)
    (hX : X ∈ intM k (Fin n) (Fin n)) : valuation k X.det ≤ 1 := by
  let Y : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨X i j, hX i j⟩
  have e : X.det = (𝒪[k].subtype.mapMatrix Y).det := rfl
  rw [e, ← RingHom.map_det]
  exact (Y.det).2

theorem integrable_volGL_of_lintegral {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure]
    (n : ℕ) (σ s : ℝ) (hs : s ≤ σ - n)
    (hI : ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
      (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤) :
    Integrable (fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val *
      nabs k (gdet g) ^ σ) (volGL μ (Fin n)) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have hE := Model.measurableEmbedding_val (k := k) (Fin n)
  have hd := continuous_density_volGL (k := k) (n := Fin n)
  have hn : IsLocallyConstant fun g : GL (Fin n) k => nabs k (GeneralLinearGroup.det g) :=
    (isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det
  have hO : IsClopen (intM k (Fin n) (Fin n)) := ⟨isCompact_intMatrix.isClosed, isOpen_intMatrix⟩
  have hind : IsLocallyConstant fun g : GL (Fin n) k =>
      (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val :=
    (LocallyConstant.indicator (1 : LocallyConstant _ ℝ) hO).isLocallyConstant.comp_continuous
      Units.continuous_val
  set F : GL (Fin n) k → ℝ := fun g => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val *
      nabs k (gdet g) ^ σ with hF
  have hFc : Continuous F :=
    hind.continuous.mul (hn.comp fun r : ℝ => r ^ σ).continuous
  refine ⟨hFc.aestronglyMeasurable, ?_⟩
  set I : Matrix (Fin n) (Fin n) k → ENNReal := (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
      (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) with hIdef
  have hpt : ∀ g : GL (Fin n) k, ENNReal.ofReal (nabs k (GeneralLinearGroup.det g) ^ (-(Fintype.card (Fin n) : ℝ)))
      * ‖F g‖ₑ ≤ I g.val := by
    intro g
    have hp := nabs_pos' (GeneralLinearGroup.det g)
    set a := nabs k (GeneralLinearGroup.det g) with ha
    by_cases hg : g.val ∈ intM k (Fin n) (Fin n)
    · have h0 : (g.val).det ≠ 0 := g.det_ne_zero
      have hu : Units.mk0 (g.val).det h0 = GeneralLinearGroup.det g := Units.ext rfl
      have hle : a ≤ 1 := by
        rw [ha, ← hu]
        exact Model.nabs_le_one _ (det_mem_integer _ hg)
      rw [hIdef, Set.indicator_of_mem hg, dite_eq_right h0, hu, ← ha, ENNReal.ofReal_rpow_of_pos hp]
      have hFg : F g = a ^ σ := by
        rw [hF]; simp only [Set.indicator_of_mem hg, one_mul]; rfl
      rw [hFg, Real.enorm_of_nonneg (Real.rpow_nonneg hp.le _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hp.le _), ← Real.rpow_add hp, Fintype.card_fin]
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hp hle ?_)
      linarith
    · have hFg : F g = 0 := by
        rw [hF]; simp only [Set.indicator_of_notMem hg, zero_mul]
      rw [hFg]; simp
  unfold HasFiniteIntegral volGL
  erw [lintegral_withDensity_eq_lintegral_mul _ hd.measurable hFc.enorm.measurable]
  calc _ ≤ ∫⁻ g : GL (Fin n) k, I g.val ∂((volM μ (Fin n) (Fin n)).comap fun g : GL (Fin n) k => g.val) :=
        lintegral_mono fun g => hpt g
    _ = ∫⁻ X, I X ∂(((volM μ (Fin n) (Fin n)).comap fun g : GL (Fin n) k => g.val).map
          fun g : GL (Fin n) k => g.val) := (hE.lintegral_map I).symm
    _ = ∫⁻ X, I X ∂((volM μ (Fin n) (Fin n)).restrict (Set.range fun g : GL (Fin n) k => g.val)) := by
        erw [hE.map_comap]
    _ ≤ ∫⁻ X, I X ∂(volM μ (Fin n) (Fin n)) := lintegral_mono' Measure.restrict_le_self le_rfl
    _ < ⊤ := hI


end GlobalTheory.GJTransfer
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableHaarVolOfLintegral =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAbsPowIntegersFinite =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAbsPowIntegersFinite", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

noncomputable section
namespace GlobalTheory.IntShell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Meas
variable [MeasurableSpace k] [BorelSpace k]

end Meas

section Main
variable [MeasurableSpace k] [BorelSpace k]

end Main

end GlobalTheory.IntShell
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAbsPowIntegersFinite =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAffineAbsPowBound =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAffineAbsPowBound", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.KSplit

section OneVar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end OneVar

end GlobalTheory.KSplit
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAffineAbsPowBound =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMatrixFirstRowColumn =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMatrixFirstRowColumn", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.KSplit.CornerFubini

end GlobalTheory.KSplit.CornerFubini
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMatrixFirstRowColumn =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralDetPowIntegerMatricesFinite =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralDetPowIntegerMatricesFinite", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAffineAbsPowBound\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMatrixFirstRowColumn\nimport Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField\nimport Formalism.DoubleCosetMeasures.StatementZ\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.GJInt

end GlobalTheory.GJInt
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralDetPowIntegerMatricesFinite =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableDetPowIndicatorIntegerGl =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableDetPowIndicatorIntegerGl", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableHaarVolOfLintegral\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralDetPowIntegerMatricesFinite\nimport Formalism.DoubleCosetMeasures.Statement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical


noncomputable section
namespace GlobalTheory.GJTransfer

end GlobalTheory.GJTransfer
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableDetPowIndicatorIntegerGl =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableZetaIntegralMatrixSchwartz =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableZetaIntegralMatrixSchwartz", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableDetPowIndicatorIntegerGl\nimport Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization\nimport Formalism.DoubleCosetMeasures.StatementZ\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Algebra.Group.Matrix\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJIntegrable


variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.GJIntegrable
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableZetaIntegralMatrixSchwartz =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzero =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzero", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableZetaIntegralMatrixSchwartz\nimport Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField\nimport Formalism.DoubleCosetMeasures.StatementZ\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Algebra.Group.Matrix\nimport Mathlib.Topology.LocallyConstant.Algebra\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJForm


variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

end GlobalTheory.GJForm
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzero =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellSumEquivariantNonzero =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellSumEquivariantNonzero", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB\npublic import Formalism.DoubleCosetMeasures.StatementZ\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanAntitone\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzero\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralShellsVanishBeyondPeriodRamified\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand\nimport Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix\nimport Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.LocallyConstant.Algebra\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit


noncomputable section
namespace GlobalTheory.ShellSumEqv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unique_shell {ϖ : kˣ} (hϖ : IsUnif ϖ) {a : ℕ} (g : GL (Fin a) k) :
    ∃! m : {m : Fin a → ℤ // Antitone m}, g ∈ shellSet ϖ m.1 := by
  obtain ⟨m, hm, x, hx, y, hy, e⟩ := GlobalTheory.SortedCartan.cartan_antitone k a ϖ hϖ g
  have ht : ∀ m : Fin a → ℤ, GlobalTheory.GLDoubling.torusElt k (Fin a) ϖ m = diagGL fun i => ϖ ^ m i :=
    fun m => Units.ext (by rw [GlobalTheory.GLDoubling.val_torusElt, diagGL_val]; simp [Units.val_zpow_eq_zpow_val])
  refine ⟨⟨m, hm⟩, mem_shellSet.2 ⟨x, hx, y, hy, by rw [e, ht]⟩, ?_⟩
  rintro ⟨m', hm'⟩ hmem
  obtain ⟨x', hx', y', hy', e'⟩ := mem_shellSet.1 hmem
  have E : (x'⁻¹ * x) * diagGL (fun i => ϖ ^ m i) * (y * y'⁻¹) = diagGL fun i => ϖ ^ m' i := by
    have h1 : x * diagGL (fun i => ϖ ^ m i) * y = x' * diagGL (fun i => ϖ ^ m' i) * y' := by
      rw [← ht, ← e]; exact e'
    calc _ = x'⁻¹ * (x * diagGL (fun i => ϖ ^ m i) * y) * y'⁻¹ := by group
      _ = _ := by rw [h1]; group
  have E' := congrArg Units.val E
  simp only [Units.val_mul, diagGL_val, Units.val_zpow_eq_zpow_val] at E'
  exact Subtype.ext (Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
    (hϖ ▸ uniformizer_lt_one) m m' hm hm' (x'⁻¹ * x) (mul_mem (inv_mem hx') hx) (y * y'⁻¹)
    (mul_mem hy (inv_mem hy')) (by simpa only [Units.val_mul] using E')).symm

theorem isOpen_shellSet (ϖ : kˣ) {a : ℕ} (m : Fin a → ℤ) : IsOpen (shellSet ϖ m : Set (GL (Fin a) k)) := by
  have : shellSet ϖ m = ⋃ x ∈ (KO k (Fin a) : Set (GL (Fin a) k)),
      (fun g => (x * diagGL (fun i => ϖ ^ m i))⁻¹ * g) ⁻¹' (KO k (Fin a) : Set _) := by
    ext g
    simp only [mem_shellSet, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, hx, by simpa [mul_assoc] using hy⟩
    · rintro ⟨x, hx, hy⟩
      exact ⟨x, hx, _, hy, by group⟩
  rw [this]
  exact isOpen_biUnion fun x _ => isOpen_KO.preimage (continuous_const.mul continuous_id)

variable [MeasurableSpace k] [BorelSpace k]

section Shells
variable {ϖ : kˣ} {ν : kˣ →* ℂˣ} {e : ℕ}

end Shells

section Main
variable {ϖ : kˣ} {ν : kˣ →* ℂˣ} {e : ℕ}

end Main

end GlobalTheory.ShellSumEqv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellSumEquivariantNonzero =====

-- ===== clump member: Development.AutomorphicArithmetic.DivisorFrames.SetIntegralMemAddSubgroupOfOpenSubgroupInvariant =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.DivisorFrames.SetIntegralMemAddSubgroupOfOpenSubgroupInvariant", "h": "module\n\npublic import Mathlib.Analysis.InnerProductSpace.Basic\npublic import Mathlib.MeasureTheory.Integral.Bochner.Basic\nimport Aesop.Main\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.CStarAlgebra.Classes\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.Order.CompletePartialOrder\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup\nimport Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace\npublic import Mathlib.MeasureTheory.Integral.Bochner.Set\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

theorem UpperTheory.setIntegral_mem_addSubgroup_of_openSubgroup_invariant :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulRightInvariant] (J : Subgroup G), IsOpen (J : Set G) → μ (J : Set G) = 1 → ∀ S : Set G, IsCompact S → (∀ j ∈ J, ∀ g ∈ S, j * g ∈ S) → ∀ f : G → ℂ, (∀ j ∈ J, ∀ g, f (j * g) = f g) → ∀ M : AddSubgroup ℂ, (∀ g ∈ S, f g ∈ M) → ∫ g in S, f g ∂μ ∈ M := by
  intro G _ _ _ _ _ μ _ J hJ hμ S hS hSJ f hf M hM
  classical
  let C : G → Set G := fun a => (fun x => x * a⁻¹) ⁻¹' (J : Set G)
  have hCo : ∀ a, IsOpen (C a) := fun a => hJ.preimage (continuous_id.mul continuous_const)
  have hCμ : ∀ a, μ (C a) = 1 := fun a => by
    simp only [C]; rw [measure_preimage_mul_right, hμ]
  have hCf : ∀ a, Set.EqOn f (fun _ => f a) (C a) := fun a x hx => by
    have := hf (x * a⁻¹) hx a
    rw [inv_mul_cancel_right] at this
    exact this
  have hCi : ∀ a, IntegrableOn f (C a) μ := fun a => by
    refine IntegrableOn.congr_fun ?_ (hCf a).symm (hCo a).measurableSet
    exact integrableOn_const (by rw [hCμ]; simp)
  have hCint : ∀ a, ∫ g in C a, f g ∂μ = f a := fun a => by
    rw [setIntegral_congr_fun (hCo a).measurableSet (hCf a), setIntegral_const]
    simp [Measure.real, hCμ]
  have key : ∀ t : Finset G, (∀ g ∈ t, f g ∈ M) →
      IntegrableOn f (⋃ g ∈ t, C g) μ ∧ ∫ g in ⋃ g ∈ t, C g, f g ∂μ ∈ M := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp
    | insert a t ha ih =>
      intro h
      obtain ⟨h1, h2⟩ := ih fun g hg => h g (Finset.mem_insert_of_mem hg)
      rw [Finset.set_biUnion_insert]
      refine ⟨(hCi a).union h1, ?_⟩
      by_cases hd : Disjoint (C a) (⋃ g ∈ t, C g)
      · rw [setIntegral_union hd
          (isOpen_biUnion fun g _ => hCo g).measurableSet (hCi a) h1, hCint]
        exact M.add_mem (h a (Finset.mem_insert_self _ _)) h2
      · rw [Set.not_disjoint_iff] at hd
        obtain ⟨x, hx1, hx2⟩ := hd
        simp only [Set.mem_iUnion] at hx2
        obtain ⟨b, hb, hxb⟩ := hx2
        have hsub : C a ⊆ ⋃ g ∈ t, C g := by
          intro y hy
          simp only [Set.mem_iUnion]
          refine ⟨b, hb, ?_⟩
          have := J.mul_mem (J.mul_mem hy (J.inv_mem hx1)) hxb
          show y * b⁻¹ ∈ (J : Set G)
          simpa [mul_assoc] using this
        rw [Set.union_eq_self_of_subset_left hsub]
        exact h2
  obtain ⟨t, ht, hcov⟩ := hS.elim_nhds_subcover C (fun x _ => (hCo x).mem_nhds (by
    show x * x⁻¹ ∈ (J : Set G)
    simp))
  have hEq : S = ⋃ g ∈ t, C g := by
    refine Set.Subset.antisymm hcov ?_
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨b, hb, hyb⟩ := hy
    have := hSJ _ hyb b (ht b hb)
    simpa using this
  rw [hEq]
  exact (key t fun g hg => hM g (ht g hg)).2
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.DivisorFrames.SetIntegralMemAddSubgroupOfOpenSubgroupInvariant =====

-- ===== clump member: Development.AutomorphicArithmetic.DivisorFrames.IntegralMemAddSubgroupOfRamifiedTwistedInvariant =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.DivisorFrames.IntegralMemAddSubgroupOfRamifiedTwistedInvariant", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellSumEquivariantNonzero\npublic import Development.AutomorphicArithmetic.DivisorFrames.SetIntegralMemAddSubgroupOfOpenSubgroupInvariant\nimport Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralShellsVanishBeyondPeriodRamified\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise


section SlopeTestRemainingChoices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem isCompact_scaledInt (ϖ : kˣ) (n : ℕ) (m : ℤ) :
    IsCompact (GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.scaledInt ϖ n m) := by
  have h := (isCompact_intMatrix (k := k) (m := Fin n) (n := Fin n)).image
    (f := fun A : Matrix (Fin n) (Fin n) k => ((ϖ ^ m : kˣ) : k) • A) (by fun_prop)
  convert h using 1
  have h0 : valuation k ((ϖ ^ m : kˣ) : k) ≠ 0 := (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
  ext Z
  constructor
  · intro hZ
    refine ⟨(((ϖ ^ m)⁻¹ : kˣ) : k) • Z, fun i j => ?_, ?_⟩
    · rw [Valuation.mem_integer_iff, Matrix.smul_apply, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_mul_le_one_of_le₀ (hZ i j) zero_le
    · simp only [smul_smul, Units.mul_inv, one_smul]
  · rintro ⟨A, hA, rfl⟩ i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hA i j))

private theorem mem_SB_of_periodic (ϖ : kˣ) {n : ℕ} (m : ℤ) (φ : Matrix (Fin n) (Fin n) k → ℂ)
    (hS : Function.support φ ⊆ GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.scaledInt ϖ n m) (hP : GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.IsPeriodic ϖ 0 φ) :
    φ ∈ SB (Matrix (Fin n) (Fin n) k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun X => ?_,
    HasCompactSupport.intro (isCompact_scaledInt ϖ n m) fun x hx => ?_⟩
  · have hn : (fun Y => Y - X) ⁻¹' {A : Matrix (Fin n) (Fin n) k | ∀ i j, A i j ∈ 𝒪[k]} ∈ nhds X :=
      (isOpen_intMatrix.preimage (continuous_id.sub continuous_const)).mem_nhds (by
        intro i j; simp)
    filter_upwards [hn] with Y hY
    have := hP X (Y - X) (fun i j => by
      simpa using (Valuation.mem_integer_iff _ _).1 (hY i j))
    simpa using this
  · by_contra h
    exact hx (hS h)

private theorem isCompact_shellSet' (ϖ : kˣ) {n : ℕ} (m : Fin n → ℤ) :
    IsCompact (shellSet ϖ m : Set (GL (Fin n) k)) := by
  have h := ((isCompact_KO (k := k) (n := Fin n)).prod (isCompact_KO (k := k) (n := Fin n))).image
    (f := fun p : GL (Fin n) k × GL (Fin n) k => p.1 * (diagGL fun i => ϖ ^ m i) * p.2) (by fun_prop)
  convert h using 1
  ext g
  rw [mem_shellSet]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

end SlopeTestRemainingChoices

theorem UpperTheory.integral_mem_addSubgroup_of_ramified_twisted_invariant :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : ℕ} (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure] (J : Subgroup (GL (Fin n) k)), IsOpen (J : Set (GL (Fin n) k)) → J ≤ KO k (Fin n) → μ (J : Set (GL (Fin n) k)) = 1 → ∀ (ϖ : kˣ) (ν : kˣ →* ℂˣ) (e : ℕ), IsUnif ϖ → ¬ IsUnram ν → CondLE ϖ e ν → ∀ (z : ℂ) (φ : Matrix (Fin n) (Fin n) k → ℂ) (a : ℕ), Function.support φ ⊆ GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.scaledInt ϖ n (-(a : ℤ)) → GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.IsPeriodic ϖ 0 φ → (∀ j ∈ J, ∀ g : GL (Fin n) k, φ (j.val * g.val) * (ν (gdet j) : ℂ) = φ g.val) → ∀ M : AddSubgroup ℂ, (∀ m : Fin n → ℤ, (∀ i, -(a : ℤ) ≤ m i ∧ m i < 0) → ∀ g ∈ shellSet ϖ m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∈ M) → ∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ ∈ M := by
  intro k _ _ _ _ _ _ n μ _ J hJo hJK hJμ ϖ ν e hϖ hram hcond z φ a hS hP hinv M hM
  by_cases hint : Integrable (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) μ
  swap
  · rw [integral_undef hint]; exact M.zero_mem
  have hφ := mem_SB_of_periodic ϖ _ φ hS hP
  obtain ⟨-, h2, h3, h4⟩ := _root_.GlobalTheory.ShellVan.shell_lemma k ϖ hϖ ν e hram hcond n μ φ hφ
  haveI : BorelSpace (GL (Fin n) k) := borel_GL
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_of_haar μ
  have hsh : ∀ m : Fin n → ℤ, shell μ ϖ ν z φ m ∈ M := by
    intro m
    by_cases hm : ∀ i, -(a : ℤ) ≤ m i ∧ m i < 0
    · refine UpperTheory.setIntegral_mem_addSubgroup_of_openSubgroup_invariant μ J hJo hJμ (shellSet ϖ m) (isCompact_shellSet' ϖ m) ?_
        (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) ?_ M (hM m hm)
      · intro j hj g hg
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
        exact mem_shellSet.2 ⟨j * x, mul_mem (hJK hj) hx, y, hy, by simp only [mul_assoc]⟩
      · intro j hj g
        simp only [apow_mul, map_mul, Units.val_mul,
          apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (hJK hj)), one_mul]
        rw [← hinv j hj g]
        ring
    · by_cases hm' : ∀ i, -(a : ℤ) ≤ m i
      · have : ∃ i, (0 : ℤ) ≤ m i := by
          by_contra! h
          exact hm fun i => ⟨hm' i, h i⟩
        rw [h2 0 hP m this z]; exact M.zero_mem
      · rw [h3 a hS m hm' z]; exact M.zero_mem
  set S : {m : Fin n → ℤ // Antitone m} → Set (GL (Fin n) k) := fun m => shellSet ϖ m.1 with hSdef
  have hU : ⋃ m, S m = Set.univ :=
    Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 (GlobalTheory.ShellSumEqv.exists_unique_shell hϖ g).exists
  have hd : Pairwise (Function.onFun Disjoint S) := fun m m' hne =>
    Set.disjoint_left.2 fun g h1 h2 => hne ((GlobalTheory.ShellSumEqv.exists_unique_shell hϖ g).unique h1 h2)
  have hm : ∀ m, MeasurableSet (S m) := fun m => (GlobalTheory.ShellSumEqv.isOpen_shellSet ϖ m.1).measurableSet
  have hfin : (Function.support fun m : {m : Fin n → ℤ // Antitone m} => shell μ ϖ ν z φ m.1).Finite :=
    h4.subset fun m hm => ⟨z, hm⟩
  have key : ∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ =
      ∑ m ∈ hfin.toFinset, shell μ ϖ ν z φ m.1 :=
    calc _ = ∫ g in ⋃ m, S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ := by
          rw [hU, Measure.restrict_univ]
      _ = ∑' m, ∫ g in S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ :=
          integral_iUnion hm hd hint.integrableOn
      _ = ∑ᶠ m : {m : Fin n → ℤ // Antitone m}, shell μ ϖ ν z φ m.1 := tsum_eq_finsum hfin
      _ = _ := finsum_eq_sum _ hfin
  rw [key]
  exact sum_mem fun m _ => hsh m.1
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.DivisorFrames.IntegralMemAddSubgroupOfRamifiedTwistedInvariant =====
