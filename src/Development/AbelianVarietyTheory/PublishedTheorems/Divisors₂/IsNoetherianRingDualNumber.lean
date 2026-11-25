module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
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

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

open GlobalTheory.SqLift

def AbelianSchemeLifts.At {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0) (π : R →+* R₀) :
    Prop :=
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left)
    (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom →
    ((∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left) (h : IsPullback i A₀.hom X.hom (spMap π)), Smooth X.hom →
        ∃ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F ∧
          schemeFil (divided₂ hI) A₀ X i h.w = F.comap (crysToDR (divided₂ hI) h')) ∧
      ∀ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F →
        ∃ (X : Over (Sp R)) (i : A₀.left ⟶ X.left) (h : IsPullback i A₀.hom X.hom (spMap π)), Smooth X.hom ∧
          schemeFil (divided₂ hI) A₀ X i h.w = F.comap (crysToDR (divided₂ hI) h')) ∧
    ∀ (X Y : Over (Sp R)) (i : A₀.left ⟶ X.left) (j : A₀.left ⟶ Y.left) (h : IsPullback i A₀.hom X.hom (spMap π))
      (k : IsPullback j A₀.hom Y.hom (spMap π)), Smooth X.hom → Smooth Y.hom →
      schemeFil (divided₂ hI) A₀ X i h.w = schemeFil (divided₂ hI) A₀ Y j k.w → ∃ e : X ≅ Y, i ≫ e.hom.left = j

def AbelianSchemeLifts : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀]
    (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π

namespace AbelianSchemeLifts.At

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {hI : I ^ 2 = 0} {π : R →+* R₀} {g : ℕ}
  {A₀ : Over (Sp R₀)} [GrpObj A₀] {A' : Over (Sp R)} [GrpObj A'] {i' : A₀.left ⟶ A'.left}

theorem exists_lift (H : At hI π) (h' : IsGrpPullback A₀ A' (spMap π) i') (hA : IsAbelianScheme A')
    (hg : SmoothOfRelativeDimension g A'.hom) {F : Submodule R (HdR A')}
    (hF : GrothendieckMessing.IsAdmissible h' F) :
    ∃ (X : Over (Sp R)) (i : A₀.left ⟶ X.left) (h : IsPullback i A₀.hom X.hom (spMap π)), Smooth X.hom ∧
      schemeFil (divided₂ hI) A₀ X i h.w = F.comap (crysToDR (divided₂ hI) h') :=
  (H g A₀ A' i' h' hA hg).1.2 F hF

theorem exists_iso (H : At hI π) (h' : IsGrpPullback A₀ A' (spMap π) i') (hA : IsAbelianScheme A')
    (hg : SmoothOfRelativeDimension g A'.hom) {X Y : Over (Sp R)} {i : A₀.left ⟶ X.left} {j : A₀.left ⟶ Y.left}
    (h : IsPullback i A₀.hom X.hom (spMap π)) (k : IsPullback j A₀.hom Y.hom (spMap π)) (hX : Smooth X.hom)
    (hY : Smooth Y.hom) (e : schemeFil (divided₂ hI) A₀ X i h.w = schemeFil (divided₂ hI) A₀ Y j k.w) :
    ∃ e : X ≅ Y, i ≫ e.hom.left = j :=
  (H g A₀ A' i' h' hA hg).2 X Y i j h k hX hY e

end AbelianSchemeLifts.At

end GlobalTheory.Published
