module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAlongHomsDescendsAbelianPartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoGenericFibreExtendsUniformisedGrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomTorsionCompatiblePeriodsLattices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatchStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfPairExistsTorsionInjectiveUpToEquiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitTorsionPointMapCommutesCharInjectiveHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupIsoAbelianPartCharacterIsosStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharacters
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoTraitUniformisationsMatchingData

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoTraitUniformisationsMatchingData =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoTraitUniformisationsMatchingData", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId\nimport Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal\nimport Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAlongHomsDescendsAbelianPartStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoGenericFibreExtendsUniformisedGrStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomTorsionCompatiblePeriodsLattices\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatchStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfPairExistsTorsionInjectiveUpToEquiStatement\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharacters\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitTorsionPointMapCommutesCharInjectiveHom\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupIsoAbelianPartCharacterIsosStatement\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
open GlobalTheory.TInj
open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

noncomputable section

namespace GlobalTheory.TInj

theorem lbIso_cube_of_lam {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (f : G ⟶ G')
    (H : LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ f) (snd G G ≫ f) : G2 G ⟶ G2 G').left)) :
    LBIso (cubeLB G' ![fst G G ≫ f, snd G G ≫ f] L') (cubeLB G ![fst G G ≫ 𝟙 G, snd G G ≫ 𝟙 G] L) := by
  have hΛ' : (abelian₂ G' L').IsLB := LB.isLB_linComb hL' _ _
  have e₁ : cubeCls G (x2 G) (cls L hL) = CechPic.pull (lift (fst G G ≫ f) (snd G G ≫ f) : G2 G ⟶ G2 G').left
      (cubeCls G' (x2 G') (cls L' hL')) :=
    (cls_cubeLB G _ hL).symm.trans (((cls_eq_iff _ (pull_isLB hΛ' _)).2 H).trans
      ((cls_pull hΛ' _ _).trans (congrArg _ (cls_cubeLB G' _ hL'))))
  rw [pull_cubeCls G' _ ![fst G G ≫ f, snd G G ≫ f] _ (fun i => by fin_cases i <;> simp [x2])] at e₁
  refine (cls_eq_iff (LB.isLB_linComb hL' _ _) (LB.isLB_linComb hL _ _)).1
    ((cls_cubeLB G' _ hL').trans (Eq.trans ?_ (cls_cubeLB G _ hL).symm))
  rw [← e₁]
  simp only [Category.comp_id]
  rfl



end GlobalTheory.TInj
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoTraitUniformisationsMatchingData =====
