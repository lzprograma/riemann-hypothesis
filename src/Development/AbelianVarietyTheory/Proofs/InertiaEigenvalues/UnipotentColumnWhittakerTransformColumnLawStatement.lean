module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariant
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformColumnLaw, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformColumnLawStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformColumnLaw =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformColumnLaw", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariant\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.CategoryTheory.Countable\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem colT_blkU_mul : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → ∀ (y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (g : GA E a),
      colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a (m + 1)) y) * colT ψ (m + 1) f g := by
  intro E _ _ a ψ hψ m f hf y g
  have hper := per_coef (a := a) hψ (eLast a (m + 1)) hf.cont
    (fun c g' => hf.left _ (isMir_blkU c) g') g
  have hT := _root_.GlobalTheory.CuspGeneric.avg_add_right (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)))
    (isCoLat_ratV E _) _ hper y
  have hpt : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E =>
        ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) =
      fun x => ψ (dot (eLast a (m + 1)) y) *
        (ψ (-dot (eLast a (m + 1)) (x + y)) * f (blkU (x + y) * g)) := by
    funext x
    have hd : dot (eLast a (m + 1)) (x + y) = dot (eLast a (m + 1)) x + dot (eLast a (m + 1)) y := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have hu : (blkU (x + y) : GA E a) = blkU x * blkU y := posU_add _ x y
    have h1 : ψ (dot (eLast a (m + 1)) y) * ψ (-dot (eLast a (m + 1)) y) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hd, hu, neg_add, AddChar.map_add_eq_mul, mul_assoc (blkU x)]
    calc ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))
        = (ψ (dot (eLast a (m + 1)) y) * ψ (-dot (eLast a (m + 1)) y)) *
            (ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) := by rw [h1, one_mul]
      _ = _ := by ring
  change avg _ (fun x => ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) =
    _ * avg _ (fun x => ψ (-dot (eLast a (m + 1)) x) * f (blkU x * g))
  rw [hpt, avg_const_mul]
  exact congrArg _ hT

end GlobalTheory.CuspGeneric
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformColumnLaw =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformColumnLawStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformColumnLawStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformColumnLaw\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformColumnLawStatement =====
