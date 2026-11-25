module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.TauDefs
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FrameInd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.AddLeMulPowOfSqLeOfLeMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.CoreInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.FvecCastSucc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.HermitianXiOrthogonal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.IsoRightInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.NsqMulVecLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.SecondOrderNormBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnipotentFixesFrameVector
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnitriangularInverseBoundOf
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.MXMulVecMid

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.PolyProperOfMx, Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialMapProper

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.PolyProperOfMx =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.PolyProperOfMx", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.TauDefs\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector\npublic import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FrameInd\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.AddLeMulPowOfSqLeOfLeMul\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.CoreInst\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.FvecCastSucc\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.HermitianXiOrthogonal\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.IsoRightInv\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.NsqMulVecLe\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.SecondOrderNormBound\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnipotentFixesFrameVector\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnitriangularInverseBoundOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace PI.PolynomialProperness

theorem polyProper_of_mx (hMX : MXFacts) : Formalism.FourierDecayAlt.C2.PolyProper := by
  have hT := tauMem_of hMX TauN.neFacts
  have hU := Formalism.FourierDecayAlt.P.unipotent_map_frame
  exact polyProper_of_steps gvGroup normInv gnFacts fmulBound zhatMove
    (frameS_of hU gvGroup) (frameSg_of hU hT gvGroup) (frameSg'_of hU hT gvGroup) (unitriangular_inverse_bound second_order_norm_bound)
    (coreInst_of isoCore hpkInvol gnFacts frameInd)

end PI.PolynomialProperness
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.PolyProperOfMx =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialMapProper =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialMapProper", "h": "module\n\npublic import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.MXMulVecMid\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.PolyProperOfMx\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

theorem Formalism.FourierDecayAlt.P.polynomial_map_proper : Formalism.FourierDecayAlt.C2.PolyProper :=
  PI.PolynomialProperness.polyProper_of_mx PI.PolynomialProperness.mxFacts
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialMapProper =====
