module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
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
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj

namespace GlobalTheory.SymVeryAmple


open GlobalTheory.CechPic in
theorem exists_of_involution {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (σ : X ⟶ X) (hσ : σ ≫ σ = 𝟙 X) (h : IsProjBy f) :
    ∃ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy f H s ∧
      Triv (LB.LinComb H (K := Fin 2) ![σ, 𝟙 X] ![1, -1]) := by
  obtain ⟨L, hL, m, s, hs⟩ := h
  have : IsProper f := isProper_of_veryAmpleBy hs
  have : IsIso σ := ⟨σ, hσ, hσ⟩
  have hA : IsAmpleLB L := isAmpleLB_of_veryAmpleBy hs
  have hP : IsAmpleLB (L.pull σ) := hA.pull_of_isAffineHom σ
  have hN : (tens L (L.pull σ)).IsLB := isLB_tens hL hP.isLB
  have hT : IsAmpleLB (tens L (L.pull σ)) := by
    refine hA.tensor hP hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hP.isLB)).1 ?_)
    rw [cls_div (LB.isLB_div hN hL) hP.isLB, cls_div hN hL, cls_tens hL hP.isLB]
    abel
  obtain ⟨n, -, M, t, ht⟩ := hT.exists_veryAmpleBy f
  have hH := isLB_lbPow hN n
  refine ⟨_, M, t, hH, ht, (cls_eq_zero_iff (LB.isLB_linComb hH _ _)).1 ?_⟩
  rw [cls_linComb hH, Fin.sum_univ_two, cls_lbPow hN, cls_tens hL hP.isLB, cls_pull hL]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, map_nsmul, map_add (f := _), ← pull_comp, hσ]
  rw [add_comm (pull σ (cls L hL)), one_zsmul, neg_one_zsmul, Category.id_comp, add_neg_cancel]

theorem exists_symmetric_veryAmpleBy : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∃ (H : LB B.left) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy B.hom H s ∧ Triv (LB.LinComb H (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]) := by
  intro R _ B _ _ _ h
  refine exists_of_involution B.hom _ ?_ h
  rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left]

end GlobalTheory.SymVeryAmple
