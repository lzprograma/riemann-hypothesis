module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryTwistInvolutionGLProperties
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwConj
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

noncomputable section

namespace GlobalTheory.Tw.Model

variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

omit [StarRing R] in
theorem Phi_apply' (i j : Fin n) : Phi n R i j = if j = i.rev then (-1) ^ (i : ℕ) else 0 := by
  simp only [Phi, Matrix.of_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff, Fin.val_rev]
  have := i.2
  have := j.2
  omega

omit [StarRing R] in
theorem Phi_mul_transpose : Phi n R * (Phi n R)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Phi_apply', ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fin.rev_inj, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [← pow_add, ← two_mul, pow_mul]; simp
  · simp

omit [StarRing R] in
theorem transpose_mul_Phi : (Phi n R)ᵀ * Phi n R = 1 := mul_eq_one_comm.mp Phi_mul_transpose

theorem Phi_conjTranspose : (Phi n R)ᴴ = (Phi n R)ᵀ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Phi_apply']
  split_ifs <;> simp

omit [StarRing R] in
theorem Phi_transpose : (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • Phi n R := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, Phi, Matrix.of_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + (j : ℕ) + 1 = n
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    have : n - 1 = i + j := by omega
    rw [this, ← pow_add, show (i : ℕ) + j + i = 2 * i + j by ring, pow_add, pow_mul]; simp
  · rw [ite_eq_right h, ite_eq_right (by omega)]; simp

theorem theta_mul (g h : Matrix (Fin n) (Fin n) R) : theta (g * h) = theta g * theta h := by
  simp only [theta, Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R), transpose_mul_Phi, Matrix.one_mul]

theorem theta_mul_theta_inv {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    theta g * theta g⁻¹ = 1 := by
  rw [← theta_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg), GlobalTheory.Tw.PhiConjugateTranspose.theta_one]

theorem theta_inv_eq {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    (theta g)⁻¹ = Phi n R * gᴴ * (Phi n R)ᵀ := by
  rw [Matrix.inv_eq_right_inv (theta_mul_theta_inv hg), theta,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg)]

theorem theta_theta {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : theta (theta g) = g := by
  apply GlobalTheory.Tw.PhiConjugateTranspose.theta_theta <;> assumption

theorem adj_eq {δ g : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (hg : IsUnit g) :
    adj δ g = (δ * theta g * δ⁻¹)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, theta_inv_eq hg,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det δ).mp hδ), adj]
  simp only [Matrix.mul_assoc]

end GlobalTheory.Tw.Model
