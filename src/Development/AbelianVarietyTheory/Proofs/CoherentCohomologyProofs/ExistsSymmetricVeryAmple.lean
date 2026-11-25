module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSymmetricVeryAmpleBy
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVarietyStatement
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
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.SymVeryAmple

theorem exists_iso_pull_of_triv {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (f : X ⟶ X)
    (h : Triv (LB.LinComb H (K := Fin 2) ![f, 𝟙 X] ![1, -1])) : ∃ w : LB.Iso H (H.pull f), w.IsGen := by
  have e := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hH _ _)).2 h
  rw [CechPic.cls_linComb hH, Fin.sum_univ_two] at e
  refine (CechPic.cls_eq_iff hH (LB.isLB_pull hH f)).1 ?_
  rw [CechPic.cls_pull hH]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, CechPic.pull_id, one_smul, neg_smul] at e
  exact (add_neg_eq_zero.1 e).symm

theorem exists_symmetric_veryAmple : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B → ∃ (H : LB B.left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy B.hom H s ∧ ∃ w : LB.Iso H (H.pull (GrpObj.inv : B ⟶ B).left), w.IsGen := by
  intro K _ _ B _ hB
  have := hB.comm
  obtain ⟨H, m, s, hH, hs, ht⟩ := exists_symmetric_veryAmpleBy K B hB (GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety K B hB)
  exact ⟨H, m, s, hH, hs, exists_iso_pull_of_triv hH _ ht⟩

end GlobalTheory.SymVeryAmple
