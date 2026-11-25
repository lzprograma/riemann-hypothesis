module

public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace

open NumberField NumberField.IsCMField TensorProduct

abbrev Bil (Y : Type) [AddCommGroup Y] : Type := Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ

section Forms

variable {Y : Type} [AddCommGroup Y]

def IsIntegralFn (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  ∀ β : S, (∀ a c, ∃ z : ℤ, (β : Bil Y) a c = z) → ∃ z : ℤ, l β = z

def IsPositiveFn (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  ∀ β : S, (∀ a, 0 ≤ (β : Bil Y) a a) → β ≠ 0 → 0 < l β

def evalSum (S : Submodule ℝ (Bil Y)) {k : ℕ} (x x' : Fin k → Y) : S →ₗ[ℝ] ℝ where
  toFun β := ∑ i, (β : Bil Y) (x i) (x' i)
  map_add' β γ := by simp [Finset.sum_add_distrib]
  map_smul' r β := by simp [Finset.mul_sum]

end Forms

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def IsBalanced (β : Bil Y) : Prop :=
  (∀ x y, β x y = β y x) ∧
    ∀ (a : 𝓞 E) (x y : Y), β (a • x) y = β x (ringOfIntegersComplexConj E a • y)

def IsBalancedSpace (S : Submodule ℝ (Bil Y)) : Prop := ∀ β, β ∈ S ↔ IsBalanced E β



open NumberField NumberField.IsCMField TensorProduct in
variable (E : Type) [Field E] [NumberField E] [IsCMField E] in
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y] in
omit [NumberField E] [IsCMField E] [Module (𝓞 E) Y] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.isIntegralFn_evalSum (S : Submodule ℝ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.Bil Y))
    {k : ℕ} (x x' : Fin k → Y) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.IsIntegralFn S (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.evalSum S x x') := by
  intro β hβ
  choose f hf using hβ
  refine ⟨∑ i, f (x i) (x' i), ?_⟩
  show ∑ i, (β : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.Bil Y) (x i) (x' i) = _
  push_cast
  exact Finset.sum_congr rfl fun i _ => hf _ _

end GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
