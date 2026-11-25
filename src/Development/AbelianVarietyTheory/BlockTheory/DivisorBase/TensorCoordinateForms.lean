module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorCoordinateForms

def dirDeriv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : V) (F : V → ℂ) : V → ℂ :=
  fun z => fderiv ℂ F z v

def wordDeriv {κ V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : κ → V) (w : List κ)
    (F : V → ℂ) : V → ℂ :=
  w.foldr (fun x G => dirDeriv (v x) G) F

def IsSpelling {κ : Type} [DecidableEq κ] (w : (κ → ℕ) → List κ) : Prop :=
  ∀ e x, (w e).count x = e x

section OnePlace

variable {X X' : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup X'] [InnerProductSpace ℂ X'] [FiniteDimensional ℂ X'] {n₀ n₁ : ℕ}

end OnePlace

section Places

variable {Pl : Type} [Fintype Pl] [DecidableEq Pl] {X X' : Pl → Type}
  [∀ τ, NormedAddCommGroup (X τ)] [∀ τ, InnerProductSpace ℂ (X τ)] [∀ τ, FiniteDimensional ℂ (X τ)]
  [∀ τ, NormedAddCommGroup (X' τ)] [∀ τ, InnerProductSpace ℂ (X' τ)] [∀ τ, FiniteDimensional ℂ (X' τ)]
  {n₀ n₁ : ℕ}

end Places

def coordVec {κ : Type} [DecidableEq κ] (p : κ) : κ → ℂ := Pi.single p 1

end GlobalTheory.IndefiniteRowSideFullHecke.TensorCoordinateForms
