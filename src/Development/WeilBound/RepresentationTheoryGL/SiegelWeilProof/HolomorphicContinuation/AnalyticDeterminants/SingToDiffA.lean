module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open scoped Matrix.Norms.Elementwise

open PositivityTheory.Rg.Sw

namespace STD

variable {n : ℕ}

abbrev Vr (n : ℕ) := Fin n → Fin n → ℝ

def hermLin (n : ℕ) : Vr n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := herm
  map_add' x y := by
    ext i j
    simp only [herm, Pi.add_apply, Matrix.add_apply]
    push_cast
    ring
  map_smul' c x := by
    ext i j
    simp only [herm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast
    ring

def hermL (n : ℕ) : Vr n →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap (hermLin n)

theorem hermL_apply (x : Vr n) : hermL n x = herm x := rfl

theorem herm_zero : herm (0 : Vr n) = 0 := by
  ext i j; simp [herm]

def v1 (r c : Fin n) : Vr n := fun i j =>
  ((if i = r ∧ j = c then 1 else 0) + (if i = c ∧ j = r then 1 else 0)) / 2

def v2 (r c : Fin n) : Vr n := fun i j =>
  ((if i = c ∧ j = r then 1 else 0) - (if i = r ∧ j = c then 1 else 0)) / 2

theorem herm_v (r c : Fin n) : herm (v1 r c) + Complex.I • herm (v2 r c) = Matrix.single r c 1 := by
  ext i j
  have e1 : (if j = r ∧ i = c then (1:ℝ) else 0) = if i = c ∧ j = r then 1 else 0 := by
    simp only [and_comm]
  have e2 : (if j = c ∧ i = r then (1:ℝ) else 0) = if i = r ∧ j = c then 1 else 0 := by
    simp only [and_comm]
  have e3 : (Matrix.single r c (1:ℂ)) i j = (((if i = r ∧ j = c then (1:ℝ) else 0 : ℝ)) : ℂ) := by
    rw [Matrix.single_apply]
    by_cases h : i = r ∧ j = c
    · obtain ⟨rfl, rfl⟩ := h; simp
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]; simp
  rw [e3]
  simp only [herm, v1, v2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, e1, e2]
  generalize (if i = r ∧ j = c then (1:ℝ) else 0) = a
  generalize (if i = c ∧ j = r then (1:ℝ) else 0) = b
  push_cast
  linear_combination ((b:ℂ) - a) / 2 * Complex.I_sq

def dc (a : Fin n × Fin n) (f : Vr n → ℂ) : Vr n → ℂ :=
  fun x => fderiv ℝ f x (v1 a.1 a.2) + Complex.I * fderiv ℝ f x (v2 a.1 a.2)

def dList : List (Fin n × Fin n) → (Vr n → ℂ) → Vr n → ℂ
  | [], f => f
  | a :: l, f => dc a (dList l f)

end STD

end PositivityTheory.Rg.Sw.LVs
