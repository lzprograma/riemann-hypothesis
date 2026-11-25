module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueIsAl
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq
import Mathlib.NumberTheory.Padics.PadicIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitOfBijectiveMulNatural
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
import Development.AbelianVarietyTheory.Statements.ChartPoints.ChartPt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumBLieMemHtLatIffOfPointOver, Development.AbelianVarietyTheory.Counterexamples.JetSurvey.HtCharOfIsUnit, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTorusLeLieSpan, Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairTAdjTLeft

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumBLieMemHtLatIffOfPointOver =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumBLieMemHtLatIffOfPointOver", "h": "module\n\npublic import Mathlib.AlgebraicGeometry.Pullbacks\npublic import Mathlib.Basic.NNReal.Defs\npublic import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp\npublic import Mathlib.Combinatorics.Quiver.ReflQuiver\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.Padics.PadicIntegers\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar\nimport Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised\nimport Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame\nimport Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber\nimport Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
open GlobalTheory.KernelNoTorsion

namespace GlobalTheory.CompHt.IndepPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P P' : Point p v O Λ}

def ptsHom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (T : Over S) :
    (T ⟶ A) →* (T ⟶ B) :=
  MonoidHom.mk' (fun x => x ≫ f) fun x y => MonObj.mul_comp x y _


variable [IsAlgClosed C] [CharZero C]

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]


variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (e : P.T ≃ₗ[ℤ_[p]] P'.T)




end GlobalTheory.CompHt.IndepPoint

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumBLieMemHtLatIffOfPointOver =====

-- ===== clump member: Development.AbelianVarietyTheory.Counterexamples.JetSurvey.HtCharOfIsUnit =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Counterexamples.JetSurvey.HtCharOfIsUnit", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueIsAl\nimport Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitOfBijectiveMulNatural\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv

namespace GlobalTheory.HodgeTateTest

open GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage

variable {O : Type} [CommRing O]

noncomputable abbrev GmO (O : Type) [CommRing O] : Over (Spec (CommRingCat.of O)) :=
  Gm (Spec (CommRingCat.of O))

end GlobalTheory.HodgeTateTest
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Counterexamples.JetSurvey.HtCharOfIsUnit =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTorusLeLieSpan =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTorusLeLieSpan", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.Padics.PadicIntegers\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.HtCharOfIsUnit\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar\nimport Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective\nimport Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised\nimport Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus\nimport Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne\nimport Development.AbelianVarietyTheory.Statements.ChartPoints.ChartPt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat GlobalTheory.KernelNoTorsion GlobalTheory.HodgeTateTest GlobalTheory.PDiv GlobalTheory.SplitTorusPow

namespace GlobalTheory.TorusTateLie

section Torus

variable (C : Type) [Field C] {O : Type} [CommRing O] [Algebra O C] {X : Type} [AddCommGroup X]

def evalChar (χ : X) : (specO O O ⟶ splitTorus (Sp O) X) →* Cˣ :=
  (Units.map ((algebraMap O C).comp (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom).toMonoidHom).comp
    ((MonoidHom.eval (Multiplicative.ofAdd χ)).comp
      (splitTorusPointsEquiv (Sp O) X (specO O O)).toMonoidHom)

def lieMap {G G' : Over (Sp O)} [GrpObj G] [GrpObj G'] (φ : G ⟶ G') [IsMonHom φ] (x : LieG G) : LieG G' :=
  ⟨x.1 ≫ φ, by rw [← Category.assoc, x.2, Category.assoc, IsMonHom.one_hom]⟩

variable {C} {p : ℕ} [Fact p.Prime]

end Torus

end GlobalTheory.TorusTateLie
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTorusLeLieSpan =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairTAdjTLeft =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairTAdjTLeft", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule\npublic import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumBLieMemHtLatIffOfPointOver\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTorusLeLieSpan\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion\npublic import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM

namespace GlobalTheory.PointMap

section General

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P P' : Point p v O Λ)

def mapT (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P.T →ₗ[ℤ_[p]] P'.T :=
  Tate.map p (IndepPoint.ptsHom α _)

def mapV [Algebra ℤ_[p] C] (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P.V →ₗ[C] P'.V :=
  (mapT P P' α).baseChange C

variable [IsAlgClosed C] [CharZero C]

def adjT (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P'.T →ₗ[ℤ_[p]] P.T :=
  (LinearEquiv.ofBijective _ P.pairT_bijective).symm.toLinearMap ∘ₗ (mapT P P' α).dualMap ∘ₗ pairT P'.A P'.eps

def adjV [Algebra ℤ_[p] C] (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P'.V →ₗ[C] P.V :=
  (adjT P P' α).baseChange C

end General

section Good

variable {Λ : Type} [CommRing Λ] [StarRing Λ]

def pullAct {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Out.PolAV S) (o : B.OAct Λ) :
    (StrictPull.polPull B f).OAct Λ := (exists_oAct_polPull f B o).choose

theorem eq_map_of_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (a : X ⟶ Y)
    (b : (Over.pullback f).obj X ⟶ (Over.pullback f).obj Y)
    (h : b.left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left) : b = (Over.pullback f).map a :=
  Over.OverMorphism.ext (pullback.hom_ext (h.trans (pullback.lift_fst _ _ _).symm)
    ((Over.w b).trans (Over.w ((Over.pullback f).map a)).symm))

theorem pullAct_act {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Out.PolAV S) (o : B.OAct Λ) (a : Λ) :
    (pullAct f B o).act a = (Over.pullback f).map (o.act a) :=
  eq_map_of_fst f _ _ ((exists_oAct_polPull f B o).choose_spec a)

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] (hv : v.Integers O) (ε : Eps p C) {R : Type} [CommRing R] (j : R →+* O)

def goodPoint (B : Out.PolAV (Sp R)) (o : B.OAct Λ) : Point p v O Λ :=
  ofGoodReduction hv ε (StrictPull.polPull B (spMap j)) (pullAct (spMap j) B o)

variable {B B' : Out.PolAV (Sp R)} (o : B.OAct Λ) (o' : B'.OAct Λ)

theorem goodPoint_oA (a : Λ) : (goodPoint hv ε j B o).oA.act a =
    (Over.pullback (spMap (algebraMap O C))).map ((Over.pullback (spMap j)).map (o.act a)) :=
  (pullAct_act _ _ (pullAct (spMap j) B o) a).trans (congrArg _ (pullAct_act _ B o a))

def homO (f : B.A ⟶ B'.A) : (goodPoint hv ε j B o).Gt ⟶ (goodPoint hv ε j B' o').Gt :=
  (Over.pullback (spMap j)).map f

def homC (f : B.A ⟶ B'.A) : (goodPoint hv ε j B o).A.A ⟶ (goodPoint hv ε j B' o').A.A :=
  (Over.pullback (spMap (algebraMap O C))).map ((Over.pullback (spMap j)).map f)

instance (f : B.A ⟶ B'.A) [IsMonHom f] : IsMonHom (homO hv ε j o o' f) :=
  inferInstanceAs (IsMonHom ((Over.pullback (spMap j)).map f))

instance (f : B.A ⟶ B'.A) [IsMonHom f] : IsMonHom (homC hv ε j o o' f) :=
  inferInstanceAs (IsMonHom ((Over.pullback (spMap (algebraMap O C))).map ((Over.pullback (spMap j)).map f)))

def homT (f : B.A ⟶ B'.A) [IsMonHom f] : (goodPoint hv ε j B o).T →ₗ[ℤ_[p]] (goodPoint hv ε j B' o').T :=
  mapT _ _ (homC hv ε j o o' f)

theorem lev_homT (f : B.A ⟶ B'.A) [IsMonHom f] (t : (goodPoint hv ε j B o).T) (n : ℕ) :
    (homT hv ε j o o' f t).lev n = t.lev n ≫ homC hv ε j o o' f := rfl

end Good

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def patAct {S : Scheme.{0}} (T : PAT H S) : letI := H.starRing; T.pol.OAct (𝓞 E) :=
  letI := H.starRing
  haveI : IsCommMonObj T.t.G := T.ab.comm
  ⟨T.t.act.toRingAct, fun a =>
    (GlobalTheory.RosLam.rosatiAdj_iff_lamEq GlobalTheory.firstFiveLaws.1.globalFns _ T.pol _ _ (T.t.act.hom a) (T.t.act.hom _)).2 (by
      change GlobalTheory.CM.LamEq _ _ _ _ _ (T.t.act.act (H.bar a))
      simpa [GlobalTheory.CM.LamEq] using T.t.adj a)⟩

variable {K : Type} [Field K] {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

abbrev patPoint (T : PAT H (Sp (𝓞 K))) : letI := H.starRing; Point ℓ v O (𝓞 E) :=
  letI := H.starRing
  goodPoint hv ε (embO hv i) T.pol (patAct T)

section Linear

variable {T T' : PAT H (Sp (𝓞 K))} {f : T.t.G ⟶ T'.t.G} (hf : Serre.IsLinearHom T.t.act T'.t.act f)

abbrev patT : letI := H.starRing; (patPoint hv ε i T).T →ₗ[ℤ_[ℓ]] (patPoint hv ε i T').T :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homT (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') f

end Linear

variable [NumberField K] {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

abbrev pointB : letI := H.starRing; Point ℓ v O (𝓞 E) := patPoint hv ε i X.B

abbrev pointA (b : Bool) : letI := H.starRing; Point ℓ v O (𝓞 E) := patPoint hv ε i (X.A b)

end Triples

end GlobalTheory.PointMap
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairTAdjTLeft =====
