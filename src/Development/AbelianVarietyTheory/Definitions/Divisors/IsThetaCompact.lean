module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

namespace GlobalTheory.Poinc

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

structure Trait (F : SFam g n ζ) where

  V : Type
  [ring : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  [char : CharZero V]
  complete : IsAdicComplete (maximalIdeal V) V

  ϖ : V
  irr : Irreducible ϖ

  y : Sp (FractionRing V) ⟶ F.X

  G : Over (Sp V)
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G

  D : DegData V (maximalIdeal V)

  A : PolAV (Sp (FractionRing V))

  U : Unif (maximalIdeal V) D A G

  α : A.A.left ⟶ F.univ.A.left

  α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left
  cart : IsGrpPullback A.A F.univ.A y α
  sq : IsSquare α α₂
  lb : LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂)

  β : LinearMap.BilinForm ℤ D.toPre.X
  symm : ∀ a b, β a b = β b a
  mono : IsMonomial D.toPre ![ϖ] ![β]

attribute [instance] Trait.ring Trait.dom Trait.dvr Trait.char Trait.grp Trait.comm

def ValOn (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) (φ : InvFun ℤ) (J : S.IdealSheafData) (d : ℕ) : Prop :=
  ∀ (T : Trait F) (ξ : Sp T.V ⟶ S), jK T.V ≫ ξ = T.y ≫ j →
    ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a}

def SharpOver (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X) : Prop :=
  ∃ c : SiegPre g n ζ (u ≫ F.s), SiegPB c F.univ u ∧ ∃ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) ∧
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y a) ∧
    LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2))

def ThetaInt (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {Z : Scheme.{0}} (i : F.X ⟶ Z) : Prop :=
  ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real)
    (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) →
    ∀ (M : RatModel o' Ω) (π : M.Z ⟶ Z), IsNormalScheme M.Z → M.pt ≫ π = spMap S.R.val.toRingHom ≫ u ≫ i →
      M.HasDiv S.th

def IsNormBl {S Z : Scheme.{0}} (π : S ⟶ Z) (J : Z.IdealSheafData) : Prop :=
  IsNormalScheme S ∧ ∃ (S₀ : Scheme.{0}) (π₀ : S₀ ⟶ Z) (ν : S ⟶ S₀) (U : S₀.Opens), FinalTheorems.Blowup π₀ J ∧ ν ≫ π₀ = π ∧
    IsFinite ν ∧ Dense (U : Set S₀) ∧ Dense (ν ⁻¹' U : Set S) ∧ IsIso (ν ∣_ U)

def IsThetaCompact (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) : Prop :=
  IsProjOver z ∧ IsNormalScheme Z ∧ IsOpenImmersion i ∧ i ≫ z = F.s ∧ Dense (Set.range i) ∧
    ∃ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W ∧ ThetaInt F W i
end GlobalTheory.Poinc
