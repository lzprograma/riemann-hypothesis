module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

def pullTop {X Y : Scheme.{0}} (f : X ⟶ Y) : Γ(Y, ⊤)ˣ →* Γ(X, ⊤)ˣ := Units.map f.appTop.hom

def pmap {A A' : Over S} (q : A ⟶ A') (T : Over S) : A ⊗ T ⟶ A' ⊗ T := lift (fst A T ≫ q) (snd A T)

def actMap {A N : Over S} [GrpObj A] (i : N ⟶ A) (T : Over S) : A ⊗ (N ⊗ T) ⟶ A ⊗ T :=
  lift (fst A (N ⊗ T) * (snd A (N ⊗ T) ≫ fst N T ≫ i)) (snd A (N ⊗ T) ≫ snd N T)

def prMap (A N T : Over S) : A ⊗ (N ⊗ T) ⟶ A ⊗ T := lift (fst A (N ⊗ T)) (snd A (N ⊗ T) ≫ snd N T)

def IsCharacter {N T : Over S} [GrpObj N] (χ : Γ((N ⊗ T).left, ⊤)ˣ) : Prop :=
  pullTop (lift (fst N (N ⊗ T) * (snd N (N ⊗ T) ≫ fst N T)) (snd N (N ⊗ T) ≫ snd N T)).left χ =
    pullTop (lift (fst N (N ⊗ T)) (snd N (N ⊗ T) ≫ snd N T)).left χ * pullTop (snd N (N ⊗ T)).left χ

def IsPullGen {X Y : Scheme.{0}} (p : X ⟶ Y) (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ) : Prop :=
  ∀ (k l : M.ι) (W : X.Opens) (h₁ : W ≤ p ⁻¹ᵁ M.U k) (h₂ : W ≤ p ⁻¹ᵁ M.U l) (h₃ : W ≤ p ⁻¹ᵁ (M.U k ⊓ M.U l)),
    res h₁ (e k) = res h₃ (pullU p _ (M.g k l)) * res h₂ (e l)

def IsEquivGen {A A' N T : Over S} [GrpObj A] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ)
    (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) : Prop :=
  IsPullGen (pmap q T).left M e ∧
    ∀ (k : M.ι) (W : (A ⊗ (N ⊗ T)).left.Opens)
      (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k))
      (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k)),
      res h₁ (pullU (actMap i T).left _ (e k)) =
        res le_top (pullTop (snd A (N ⊗ T)).left χ) * res h₂ (pullU (prMap A N T).left _ (e k))

end GlobalTheory.CharKer
