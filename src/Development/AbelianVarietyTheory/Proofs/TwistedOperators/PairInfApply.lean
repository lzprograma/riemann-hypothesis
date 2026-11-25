module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

noncomputable section

namespace GlobalTheory.GaussLine

open Complex NumberField

def heisFun {V : Type} [AddCommGroup V] [Module ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (p q : V) (f : V → ℂ) : V → ℂ :=
  fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((β x q + β p q / 2 : ℝ) : ℂ)) * f (x + p)

def dHeis {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : V → ℂ)
    (x : V) : ℂ :=
  fderiv ℝ f x w.1 - 2 * Real.pi * Complex.I * (β x w.2 : ℂ) * f x

variable (F : Type) [Field F] [NumberField F]

def pairInf (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun x x' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
    (fun c x y => by simp [← Finset.smul_sum])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
    (fun c x y => by simp [← Finset.smul_sum])

theorem pairInf_apply (κ : Type) [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) :
    pairInf F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

theorem heisFun_apply {V : Type} [AddCommGroup V] [Module ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (p q : V) (f : V → ℂ) (x : V) :
    heisFun β p q f x = Complex.exp (-(2 * Real.pi * Complex.I) * ((β x q + β p q / 2 : ℝ) : ℂ)) * f (x + p) := rfl

end GlobalTheory.GaussLine

end
