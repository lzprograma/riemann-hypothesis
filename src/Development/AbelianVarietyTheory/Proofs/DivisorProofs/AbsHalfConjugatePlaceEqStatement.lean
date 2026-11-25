module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorEqProductAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEq, Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEqStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEq =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEq", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorEqProductAbove\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.BCT.AbsHalfConj

theorem ordL_congr {L L' : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [Field L']
    [Valued L' (WithZero (Multiplicative ℤ))] {a : L} {b : L'} (h : Valued.v a = Valued.v b) : ordL a = ordL b := by
  unfold ordL
  by_cases ha : Valued.v a = 0
  · rw [dite_eq_left ha, dite_eq_left (h ▸ ha)]
  · rw [dite_eq_right ha, dite_eq_right (h ▸ ha)]
    congr 2
    exact WithZero.coe_inj.1 (by rw [WithZero.coe_unzero, WithZero.coe_unzero, h])

theorem absHalf_conjPl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u : Pl E), u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ x : E, absHalf u (algebraMap E (u.adicCompletion E) x) = absHalf w (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x)) := by
  intro E _ _ _ w u hne hund x
  have hcu : GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv w u :=
    ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w u).1 hund).resolve_left hne
  have hv : Valued.v (algebraMap E (u.adicCompletion E) x) =
      Valued.v (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x)) := by
    have h1 : Valued.v (algebraMap E (u.adicCompletion E) x) = u.valuation E x :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u x
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x)) =
        w.valuation E (IsCMField.complexConj E x) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h1, h2]
    have := hcu (IsCMField.complexConj E x)
    simp only [AlgEquiv.coe_ringEquiv, IsCMField.complexConj_apply_apply] at this
    exact this
  have hq : qV E u = qV E w := by
    unfold qV
    rw [eq_conjSrc hcu, GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc]
  unfold absHalf
  rw [ordL_congr hv, hq]

end GlobalTheory.BCT.AbsHalfConj
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEq =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEqStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEqStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEq\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEqStatement =====
