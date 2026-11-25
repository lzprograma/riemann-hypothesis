module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open CategoryTheory AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def AbelianHodgeDeRham : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    (Module.Finite R (HH1 A.hom) ∧ Module.Projective R (HH1 A.hom) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (HH1 A.hom) p = 2 * g) ∧
    (∃ e : ⋀[R]^2 (HH1 A.hom) ≃ₗ[R] HH2 A.hom, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHH A.hom a b) ∧
    (Module.Finite R (GlobForm A.hom) ∧ Module.Projective R (GlobForm A.hom) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (GlobForm A.hom) p = g) ∧
    (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧
    (ClosedForm A.hom = ⊤ ∧ Function.Injective (clForm A.hom) ∧ Function.Surjective (toHO1 A.hom)) ∧
    ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left)
      (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))),
      (∃ e : R' ⊗[R] HH1 A.hom ≃ₗ[R'] HH1 s', ∀ c, IsPull1 h.w c (e (1 ⊗ₜ c))) ∧
      (∃ e : R' ⊗[R] GlobForm A.hom ≃ₗ[R'] GlobForm s', ∀ c, IsPullForm h.w c (e (1 ⊗ₜ c))) ∧
      ∃ e : R' ⊗[R] HO1 A.hom ≃ₗ[R'] HO1 s', ∀ c, IsPullO h.w c (e (1 ⊗ₜ c))

end GlobalTheory.Published
