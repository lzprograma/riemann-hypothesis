module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsionThetaLocal

theorem exists_theta_of_pow_eq_one : ∀ (S₀ : Scheme.{0}) (G : Over S₀) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (S : Type) [CommRing S] [IsLocalRing S] (t : Spec (CommRingCat.of S) ⟶ S₀) (k : ℕ) (x : Over.mk t ⟶ G), x ^ k = 1 → ∃ θ : ThetaGrp G L.L (k : ℤ) (Over.mk t), θ.pt = x := by
  intro S₀ G _ _ L c S _ _ t k x hx
  obtain ⟨u, hu, -⟩ := Geo.Tor.exists_cubN c (1 : Over.mk t ⊗ G ⟶ G) (fst (Over.mk t) G ≫ x) (snd (Over.mk t) G) k
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := S) L.L L.isLB (K := Fin 2)
    ![x.left, (1 : Over.mk t ⟶ G).left] ![-(k : ℤ), k]
  have hm : (fst (Over.mk t) G ≫ x) ^ k = 1 := by
    rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have h1 : (fst (Over.mk t) G).left ≫ (1 : Over.mk t ⟶ G).left = (1 : Over.mk t ⊗ G ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have h2 : (fst (Over.mk t) G).left ≫ x.left = (fst (Over.mk t) G ≫ x).left := rfl
  have h3 : translPt G x = (fst (Over.mk t) G ≫ x) * snd (Over.mk t) G := rfl
  obtain ⟨w, hw, -⟩ := Geo.Tor.exists_gen L.isLB
    (φ' := ![(snd (Over.mk t) G).left, (translPt G x).left]) (ε' := ![(k : ℤ), -(k : ℤ)]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ]
      erw [h1, h2]
      rw [hm, h3]
      simp only [_root_.one_mul, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ u (LB.pullGen L.L _ _ e (fst (Over.mk t) G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.pullGen_isGen _ _ _ _ he _))
  exact ⟨⟨x, w, hw⟩, rfl⟩

end GlobalTheory.TorsionThetaLocal
