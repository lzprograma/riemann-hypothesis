module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM

def CMExistsSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (Z : CMLat hP D.p D.q)
    (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k →
    ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ρ : 𝓞 K₁)
      (X : CMObj H K₁ ρ (algebraMap K₁ ℂ) D.p D.q) (y : Sp K₁ ⟶ Xo.X) (t₀ : SAB H (Sp K₁))
      (m : SABMap t₀ Xo.univ.t y) (m' : SABMap t₀ X.B.t (spMap (algebraMap (𝓞 K₁) K₁)))
      (gA : Bool → ℕ) (tyA : ∀ b, Fin (gA b) → (E →+* ℂ)) (PA : ∀ b, (Z.D₁ b).La →+ (Fin (gA b) → ℂ))
      (e : ∀ b, (Fin (gA b) → ℂ) → (Over.mk (spMap ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁))) ⟶ (X.A b).t.G))
      (F : ∀ j : Fin D.p ⊕ Fin D.q, (Fin (gA j.isLeft) → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      k ≤ K₁ ∧ ((ρ : K₁) : ℂ) = H.rt0 ∧ X.hh = Z.hh ∧
      y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe ∧
      (∀ b, IsTypeFn H (Z.D₁ b).p (Z.D₁ b).q (tyA b) ∧ IsExp (X.A b) _ (Z.D₁ b) (tyA b) (PA b) (e b)) ∧
      (∀ j a, F j (PA _ a) = Pe (Z.f j a)) ∧
      ∀ (j : Fin D.p ⊕ Fin D.q) (z : Fin (gA j.isLeft) → ℂ) (x : Sp ℂ ⟶ t₀.G.left), x ≫ t₀.G.hom = spMap (algebraMap K₁ ℂ) →
        x ≫ m'.φ = (e _ z ≫ X.φ j).left → x ≫ m.φ = (FU.ex i Pe (F j z)).left

end GlobalTheory.CM
end
