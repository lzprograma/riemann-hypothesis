module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open Limits (pullback biprod)
open MonoidalCategory CartesianMonoidalCategory
open GlobalTheory.Cartier
open GlobalTheory.CechPic (Pic cls lam)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
open scoped ContDiff ComplexOrder CategoryTheory.Obj

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ σ' : k →+* ℂ}

structure IsRegSurf (p : X ⟶ Sp k) : Prop extends IsArithVar p 1 where

  regular : ∀ x, IsRegularLocalRing (X.presheaf.stalk x)

structure RegCover (p : X ⟶ Sp k) [IsIntegral X] where

  Y : Scheme.{0}

  ρ : Y ⟶ X

  reg : IsRegSurf (ρ ≫ p)

  generic : haveI := reg.isIntegral; ρ (genericPoint Y) = genericPoint X

  finite : haveI := reg.isIntegral; ρ.residueDegree (genericPoint Y) ≠ 0

namespace RegCover

variable [IsIntegral X] (C : RegCover p)

end RegCover

namespace HermLB

variable [IsIntegral X] [IsLocallyNoetherian X] (L M : HermLB p)

variable {L M}

end HermLB

namespace VMetric

variable [IsIntegral X] {E : X.Modules} {r : ℕ} {h : VMetric p E r} {a b : ℝ}




end VMetric





def sqMap {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) : (A' ⊗ A').left ⟶ (A ⊗ A).left :=
  pullback.map A'.hom A'.hom A.hom A.hom φ φ f w.symm w.symm

structure PPAS (S : Scheme.{0}) where

  A : Over S

  [grp : GrpObj A]

  isAb : IsAbelianScheme A

  g : ℕ

  smoothDim : SmoothOfRelativeDimension g A.hom

  c : Pic (A ⊗ A).left

  isPol : IsPrincipalPol A c

namespace PPAS

attribute [instance] grp smoothDim

variable {S S' : Scheme.{0}} (P : PPAS S)

structure RiemannData (y : Sp ℂ ⟶ S) where

  B : Over (Sp ℂ)

  [grp : GrpObj B]

  φ : B.left ⟶ P.A.left

  isPull : IsGrpPullback B P.A y φ

  L : LB B.left

  isLB : L.IsLB

  pol : CechPic.pull (sqMap isPull.1.w) P.c = lam (cls L isLB) (fst B B) (snd B B)

  u : HolUnif B L P.g

  H : Matrix (Fin P.g) (Fin P.g) ℂ

  χ : u.Λ → ℂ

  isAH : u.IsAH H χ

namespace RiemannData

attribute [instance] grp

variable {P} {y : Sp ℂ ⟶ S} (d : P.RiemannData y)

end RiemannData

variable (P : PPAS X)

variable {P} {t : ℝ} {h h' : VMetric p (omega P.A) P.g}

variable (P p) [IsIntegral X]


variable {P p} {a b : ℝ}

end PPAS

end GlobalTheory
