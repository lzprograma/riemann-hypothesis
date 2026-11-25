module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.DiagPull

theorem weilIs_diag_eq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left),
    IsAbelianScheme A → P.IsLB → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ),
    Out.WeilIs (G2 A) P n (lift u u) (lift v v) c → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n u v c' →
    c = c' := by
  intro S A _ _ P hA hP n T u v c c' h h'
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := LB.isLB_pull hP _
  have hw : LBIso (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 1) (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
    have h1 : (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 1).IsLB := LB.isLB_linComb hL _ _
    refine (CechPic.cls_eq_iff h1 hL).1 ?_
    rw [CechPic.cls_lbPow hL, one_smul]
  have hu : u ≫ lift (𝟙 A) (𝟙 A) = lift u u := by simp
  have hv : v ≫ lift (𝟙 A) (𝟙 A) = lift v v := by simp
  rw [← hu, ← hv] at h
  have h2 := WeilIsogeny.weilIs_pull_hom globalFns_holds hA hL hP (lift (𝟙 A) (𝟙 A)) hw h
  rw [Nat.cast_one, Int.mul_one] at h2
  exact CommutatorPairing.weilIs_unique globalFns_holds hA hL h2 h'

end GlobalTheory.DiagPull
