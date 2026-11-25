module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.LimitsOver
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

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms

open ReciprocityTheory.ChartRestriction.G.Out

def stdForm {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) : ℤ :=
  ∑ i : Fin g, (a (Sum.inl i) * b (Sum.inr i) - a (Sum.inr i) * b (Sum.inl i))

def reduce {g : ℕ} (k : ℕ) (a : Fin g ⊕ Fin g → ℤ) : Fin g ⊕ Fin g → ZMod k :=
  fun j => (a j : ZMod k)

variable {S : Scheme.{0}}

def mulBy (A : Over S) [GrpObj A] (k : ℕ) : A ⟶ A := (𝟙 A) ^ k

abbrev constOver (S : Scheme.{0}) (I : Type) : Over S := ∐ fun _ : I => 𝟙_ (Over S)

structure Level (P : PolAV S) (k : ℕ) (ζ : Γ(S, ⊤)ˣ) where

  hom : Multiplicative (Fin P.g ⊕ Fin P.g → ZMod k) →* (𝟙_ (Over S) ⟶ P.A)

  isKer : IsPullback
    (Sigma.desc fun v : Fin P.g ⊕ Fin P.g → ZMod k => hom (Multiplicative.ofAdd v) :
      constOver S (Fin P.g ⊕ Fin P.g → ZMod k) ⟶ P.A)
    (toUnit _) (mulBy P.A k) η[P.A]

  pairing : ∀ a b : Fin P.g ⊕ Fin P.g → ℤ,
    WeilIs P.A P.L (k : ℤ) (T := 𝟙_ (Over S))
      (hom (Multiplicative.ofAdd (reduce k a))) (hom (Multiplicative.ofAdd (reduce k b)))
      (ζ ^ stdForm a b : Γ(S, ⊤)ˣ)

namespace Level

variable {P : PolAV S} {k : ℕ} {ζ : Γ(S, ⊤)ˣ}

end Level

end GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms
