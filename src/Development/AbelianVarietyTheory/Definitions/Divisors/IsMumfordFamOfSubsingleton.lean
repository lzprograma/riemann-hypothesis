module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

namespace GlobalTheory.PolDeg

section Generic

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_genericMap {ρ : R →+* R'} (hρ : Function.Injective ρ) :
    ∃ κ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ ≫ jK R = jK R' ≫ spMap ρ := by
  have h : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) := (IsFractionRing.injective R' _).comp hρ
  refine ⟨spMap (IsFractionRing.lift (K := FractionRing R) h), ?_⟩
  change spMap _ ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ
  rw [← spMap_comp, ← spMap_comp]
  congr 1
  ext r
  simp

end Generic

section Good

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

alias lbIso_pull_comp := _root_.GlobalTheory.Ex.GenericFibre.lbIso_pull

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ : G''.left ⟶ G'.left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
    by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

end Good

end GlobalTheory.PolDeg
