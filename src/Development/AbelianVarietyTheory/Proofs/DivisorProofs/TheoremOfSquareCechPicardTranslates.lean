module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
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
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj

namespace GlobalTheory.SquareSym

theorem lam_mul_left {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    (c : Pic A.left) {Y : Over S} (a a' x : Y ⟶ A) : lam c (a * a') x = lam c a x + lam c a' x := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over S) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  have h := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hA hP
    (by rw [triv_ev_iff hP, e, lam_one_left]) (by rw [triv_ev_iff hP, e, lam_one_right])
  simpa only [e] using (isAdditive_iff hP).1 h Y a a' x

theorem pull_mul_add_pull_mul_inv : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (Y : Over S) (x a : Y ⟶ A), GlobalTheory.CechPic.pull (x * a).left c + GlobalTheory.CechPic.pull (x * a⁻¹).left c = 2 • GlobalTheory.CechPic.pull (x).left c + GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull (a⁻¹).left c - 2 • GlobalTheory.CechPic.pull ((1 : Y ⟶ A)).left c := by
  intro S _ A _ hA c Y x a
  haveI := hA.comm
  have h := lam_mul_left hA c a a⁻¹ x
  rw [mul_inv_cancel, lam_one_left, lam_comm c a x, lam_comm c a⁻¹ x, lam, lam] at h
  rw [← sub_eq_zero, h]
  abel

end GlobalTheory.SquareSym
