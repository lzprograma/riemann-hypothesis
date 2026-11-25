module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem prod_famT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (α : D.X) (k : ℕ) {U : Type} [CommGroup U] (h : ((T ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ i, h (famφT D T α i) ^ DegPre.famε k i =
      h (snd T D.P.A).left ^ ((k : ℤ) - 1) * h (DVR.cP D (T ⊗ D.P.A) α * snd T D.P.A).left *
        (h (DVR.cP D (T ⊗ D.P.A) α).left)⁻¹ * h (1 : T ⊗ D.P.A ⟶ D.P.A).left := by
  have e₁ : famφT D T α 1 = (DVR.cP D (T ⊗ D.P.A) α * snd T D.P.A).left :=
    congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (mul_comm (snd T D.P.A) (DVR.cP D (T ⊗ D.P.A) α))
  have e₂ : famφT D T α 2 = (DVR.cP D (T ⊗ D.P.A) α).left := rfl
  have e₃ : famφT D T α 3 = (1 : T ⊗ D.P.A ⟶ D.P.A).left := rfl
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

theorem exists_isProdB : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (k l : ℕ) (β ga α : D.X), β + ga = α → ∀ (f : SecBT D T k β) (g : SecBT D T l ga),
    ∃ h : SecBT D T (k + l) α, IsProdB f g h := by
  intro R _ _ D T k l β ga α hα f g
  subst hα
  let a : T ⊗ D.P.A ⟶ D.P.A := DVR.cP D _ β
  let b : T ⊗ D.P.A ⟶ D.P.A := DVR.cP D _ ga
  let x : T ⊗ D.P.A ⟶ D.P.A := snd T D.P.A
  have hu := DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift a (lift b x)).left
  obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := famφT D T (β + ga)) (ε' := DegPre.famε (k + l)) (fun U _ h => by
      have p₁ := prod_cub a b x h
      have p₂ := prod_famT D T β k h
      have p₃ := prod_famT D T ga l h
      have p₄ := prod_famT D T (β + ga) (k + l) h
      rw [DVR.cPoint_add] at p₄
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₂ p₃) p₁) (Eq.trans ?_ p₄.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, a, b, x]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec f g) (genSec (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift a (lift b x)).left) hu))
  refine ⟨t, fun Z r z J hJ => ?_⟩
  refine (ht _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ) ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val
      ((val_cub D.cub r hJ a b x).trans ?_)))))
  rw [DVR.comp_cP, DVR.comp_cP]; rfl

end GlobalTheory.UU
