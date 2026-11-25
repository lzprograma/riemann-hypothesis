module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.VertForm

namespace GlobalTheory.NefHodgeTateAt

section Curves

variable {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem topSelf_of_cls_eq_add (hp : IsProjOver p) {N A B : LB X} (hN : N.IsLB) (hA : A.IsLB) (hB : B.IsLB)
    (h : cls N hN = cls A hA + cls B hB) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type) [Field κ] [Finite κ]
    [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ (N.pull i) 1 = topSelfIntersection κ (A.pull i) 1 + topSelfIntersection κ (B.pull i) 1 := by
  obtain ⟨hpr, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have e2 (L : LB X) : topSelfIntersection κ (L.pull i) 1 = interNum κ (structureModule Z) ![L.pull i] := by
    rw [topSelf_def]
    congr 1
    funext j
    fin_cases j
    rfl
  rw [e2, e2, e2]
  refine interNum_one_of_cls_eq_add (hH.pull_of_isClosedImmersion i) hd (LB.isLB_pull hN i) (LB.isLB_pull hA i)
    (LB.isLB_pull hB i) ?_
  rw [cls_pull hN, cls_pull hA, cls_pull hB, h, map_add (f := _)]

theorem topSelf_pow (hp : IsProjOver p) (L : HermLB p) (m : ℕ) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i]
    (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ ((L.pow m).B.pull i) 1 = m * topSelfIntersection κ (L.B.pull i) 1 := by
  have c (n : ℕ) : cls (L.pow n).B (L.pow n).isLB = n • cls L.B L.isLB := cls_lbPow L.isLB n _
  induction m with
  | zero =>
    have := topSelf_of_cls_eq_add hp (L.pow 0).isLB (L.pow 0).isLB (L.pow 0).isLB (by rw [c]; simp) Z i κ hd
    simp only [Nat.cast_zero, zero_mul]
    linarith
  | succ n ih =>
    rw [topSelf_of_cls_eq_add hp (L.pow (n + 1)).isLB (L.pow n).isLB L.isLB (by rw [c, c, succ_nsmul]) Z i κ hd, ih]
    push_cast
    ring


end Curves

open Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4
open scoped ENNReal Classical

end GlobalTheory.NefHodgeTateAt
