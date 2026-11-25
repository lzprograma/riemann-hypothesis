module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumFractionFieldEqMulIntegralCongrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneTermEqConstMulPsiMulThetaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExhaustOfLabels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRenormalizationRigidificationMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameEqConstMulIntegralGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTranslateThetaSectionUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantPointDescendsToSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointAbelianPartLiesUnderClassZeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTorsionPointLiftSectionTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueIntegralPointEqAdicSumTermsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameAbelianPartTorsionFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustOfGenericGeometricStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegrallyClosedInFractionFieldPowerSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsTorsMap
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.Sep.HighTerms


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem exists_integral (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : IsCN V)
    (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) (N : ℕ) (hN : 1 ≤ N) (g' : GtPtF D.toPre (FractionRing V))
    (ho : ∃ o, GtPtF.IsNsmul N g' o ∧ o.IsZero) :
    ∃ g : GtPt D.toPre (𝟙_ (Over (Sp V))),
      GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' := by
  have : CharZero V := hV.2.2.2
  haveI : IsNoetherianRing V := hV.1
  have hR : GlobalTheory.Mum.Base V := ⟨admissibleBase_of_completeNormalLocalCharZero hV, hV.2.2.2⟩
  obtain ⟨M, g₀, x₀, hfin, -, hg₀, huniv, hx₀, hform⟩ :=
    GlobalTheory.ToricTorsionUnif.exists_torsion_toG V hR G D A U N hN
  have hkg : N • g' = 0 := by
    obtain ⟨o, h₁, h₂⟩ := ho
    exact ((GlobalTheory.TorusExt.isNsmul_iff_eq N g' o).1 h₁).symm.trans ((GlobalTheory.TorusExt.isZero_iff_eq o).1 h₂)
  obtain ⟨n, hn, -⟩ := huniv _ _ (GlobalTheory.Poinc.TorsLift.gtTors_toT g' hkg)
  have hj : spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ jFK (R := V) (FractionRing V) =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) := by
    rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let nb : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ M :=
    Over.homMk (spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ n.left) (by
      rw [Category.assoc, Over.w n]
      show _ ≫ jFK (R := V) (FractionRing V) ≫ jK V = jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V
      rw [← Category.assoc, hj])
  obtain ⟨s, hs⟩ := GlobalTheory.FinDescent.galoisFixed_point_of_finite V hV.2.1 M hfin nb (fun σ => by
    have hσ : spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) =
        spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) := by
      rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun r => σ.commutes r
    show spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ n.left = _
    rw [reassoc_of% hσ]; rfl)
  have hns : n = toUnit _ ≫ s := by
    apply Over.OverMorphism.ext
    apply GlobalTheory.OnePoint.point_ext (spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))))
    refine (congrArg (·.left) hs).trans ?_
    rw [Over.comp_left, Over.comp_left, ← Category.assoc]
    congr 1
    have e1 : ∀ X : Over (Sp V), (toUnit X).left = X.hom := fun X => by simp
    rw [e1, e1]
    show jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V =
      spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ jFK (R := V) (FractionRing V) ≫ jK V
    rw [← Category.assoc, hj]
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.ConstLie.exists_isPullGt s g₀
  obtain ⟨q, hq⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) g
  have h2 := GlobalTheory.FlatTors.TorsMapExists.isPullF_trans hg hq
  rw [← Over.comp_left, ← hns] at h2
  exact ⟨g, by rwa [GlobalTheory.FieldRestrictionTest.isPullF_unique h2 hn] at hq⟩

end GlobalTheory.Poinc.Sep.HighTerms
