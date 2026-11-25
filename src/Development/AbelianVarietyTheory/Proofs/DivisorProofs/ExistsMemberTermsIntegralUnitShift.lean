module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumFractionFieldEqMulIntegralCongrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneTermEqConstMulPsiMulThetaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameEqConstMulIntegralGeneratorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTranslateThetaSectionUnitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointAbelianPartLiesUnderClassZeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTorsionPointLiftSectionTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueIntegralPointEqAdicSumTermsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustOfGenericGeometricStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Mathlib.Tactic.Polynomial.Basic

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShift

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShift =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShift", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd\npublic import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumFractionFieldEqMulIntegralCongrStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneTermEqConstMulPsiMulThetaStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingThetaConstantsGenerateIntegralTorsionLabStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionGenericFibreMemberStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameEqConstMulIntegralGeneratorStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTranslateThetaSectionUnitStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointAbelianPartLiesUnderClassZeStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointGenericFibreMemberHasLabelStatement\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelUnitThetaConstantNeZeroDividesAllStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta\npublic import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTorsionPointLiftSectionTorusExtension\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueIntegralPointEqAdicSumTermsStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustOfGenericGeometricStatement\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin\nimport Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Development.AbelianVarietyTheory.Definitions.Divisors.FromBase\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem mem_of_psiCoord {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} (D : DegData V I) {χ : D.toPre.X} (hχ : χ ≠ 0)
    {r : V} (h : Formalism.L2.Pj.PsiCoord D.toPre χ r) : r ∈ I := by
  obtain ⟨j, h₁, h₂, e⟩ := h
  obtain ⟨r', hr', e'⟩ := D.psi_pos χ hχ j ⊤ (isAffineOpen_top _) h₁ h₂
  have e₁ : r' = DegPre.toOpen (R := V) ⊤ r := GlobalTheory.PsiCoordLocal.jK_app_inj ⊤ (e'.trans e.symm)
  rw [e₁] at hr'
  have hb := GlobalTheory.PsiCoordLocal.toOpen_top_bijective (R := V)
  obtain ⟨s, hs, es⟩ := (Ideal.mem_map_iff_of_surjective _ hb.2).1 hr'
  rwa [← hb.1 es]

theorem isUnit_of_sub_mem {V : Type} [CommRing V] [IsLocalRing V] {a b : V} (h : a - b ∈ maximalIdeal V) :
    IsUnit a ↔ IsUnit b := by
  rw [← not_iff_not, ← mem_nonunits_iff, ← mem_nonunits_iff, ← mem_maximalIdeal, ← mem_maximalIdeal]
  exact ⟨fun ha => by simpa using sub_mem ha h, fun hb => by simpa using add_mem h hb⟩

end GlobalTheory.Poinc.IntTerm
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShift =====
