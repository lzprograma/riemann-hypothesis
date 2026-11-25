module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

namespace GlobalTheory.Poinc.Sep

def DefOver {K : Type} [Field K] (k₀ : Subfield K) {Y : Scheme.{0}} (P : Sp K ⟶ Y) : Prop :=
  ∃ P₀ : Sp k₀ ⟶ Y, spMap k₀.subtype ≫ P₀ = P

variable {V : Type} [CommRing V] [IsDomain V]

abbrev Gens (Q : Data V) : Type := ∀ a b : Q.X, LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε)

def TauIn (Q : Data V) (τ₀ : Gens Q) {N : ℕ} (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ Q.X) : Prop :=
  ∀ a b, (τ₀ a b).IsGen ∧ ∃ k : (FractionRing V)ˣ,
    (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i a b ∧ ∀ z J, Good Q.M.L z J →
      val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k) * val (τ₀ a b) (toUnit (TK V)).left z J

def FromBase (Q : Data V) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* V) : Prop :=
  ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
    (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
    (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left)
    (w : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)),
    IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.B B₀ (spMap ιb) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (Q.c a).left ≫ β = spMap ιb ≫ (c₀ a).left) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
    ∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
      val (τ₀ a b) (toUnit T).left z J' =
        lamVal w (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ιb) z J

end GlobalTheory.Poinc.Sep
