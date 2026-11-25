module

public import Formalism.ThetaSupremumBounds.StatementA
public import Mathlib.Analysis.Calculus.FDeriv.Defs
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.ThetaSupremumBounds.StatementE

@[expose] public section

open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms

open Formalism.DimensionVariation (mono mfact nsq liftBlock)

section Calculus

variable {E κ W : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype κ]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

def dirDeriv (v : E) (F : E → ℂ) : E → ℂ := fun z => fderiv ℂ F z v

def monoDeriv (v : κ → E) (e : κ → ℕ) (F : E → ℂ) : E → ℂ :=
  (univ : Finset κ).toList.foldr (fun x G => (dirDeriv (v x))^[e x] G) F


open Classical in
def coordVec (x : κ) : κ → ℂ := Pi.single x 1

def taylorCoeff (F : (κ → ℂ) → ℂ) (e : κ → ℕ) : ℂ :=
  monoDeriv coordVec e F 0 / (mfact e : ℂ)

end Calculus

section OnePlace

variable {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B] {n₀ n₁ : ℕ}

end OnePlace

section AllPlaces

variable {Pl : Type} [Fintype Pl] {X₀ X₁ : Pl → Type}
  [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
  [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
  {n₀ n₁ : ℕ}


end AllPlaces

end GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms
