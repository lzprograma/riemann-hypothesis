module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.RingTheory.MvPolynomial.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MvPolynomial
open scoped IsMulCommutative

namespace GlobalTheory.Wick

section Eval

variable {k A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] {σ ι κ : Type*}


open scoped IsMulCommutative in
noncomputable def commEval (k : Type*) [CommSemiring k] [Algebra k A] (a : σ → A)
    (ha : ∀ i j, Commute (a i) (a j)) : MvPolynomial σ k →ₐ[k] A :=
  haveI : IsMulCommutative (Algebra.adjoin k (Set.range a)) :=
    Algebra.isMulCommutative_adjoin k (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact ha i j)
  (Algebra.adjoin k (Set.range a)).val.comp
    (aeval fun i => (⟨a i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : Algebra.adjoin k (Set.range a)))

@[simp] theorem commEval_X (a : σ → A) (ha : ∀ i j, Commute (a i) (a j)) (i : σ) :
    commEval k a ha (X i) = a i := by
  simp [commEval]

@[simp] theorem commEval_C (a : σ → A) (ha : ∀ i j, Commute (a i) (a j)) (c : k) :
    commEval k a ha (C c) = algebraMap k A c := algHom_C _ _

variable {a : ι → A} {a' : κ → A} (ha : ∀ i j, Commute (a i) (a j))
  (ha' : ∀ i j, Commute (a' i) (a' j))

end Eval

section Divided

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {σ : Type*}

def multiChoose (n β : σ →₀ ℕ) : ℕ := β.prod fun i e => (n i).choose e

@[simp] theorem multiChoose_zero (n : σ →₀ ℕ) : multiChoose n 0 = 1 := by simp [multiChoose]

theorem multiChoose_eq_mul_erase (n β : σ →₀ ℕ) (i : σ) :
    multiChoose n β = (n i).choose (β i) * multiChoose n (β.erase i) :=
  (Finsupp.mul_prod_erase' β i _ fun _ => Nat.choose_zero_right _).symm

theorem le_of_multiChoose_ne_zero {n β : σ →₀ ℕ} (h : multiChoose n β ≠ 0) : β ≤ n := by
  intro i
  rw [multiChoose_eq_mul_erase n β i] at h
  by_contra hi
  exact h (by rw [Nat.choose_eq_zero_of_lt (not_le.mp hi), zero_mul])


variable (R) in
noncomputable def dividedDeriv (β : σ →₀ ℕ) : Module.End R (MvPolynomial σ R) :=
  (basisMonomials σ R).constr R fun n => multiChoose n β • monomial (n - β) 1

theorem dividedDeriv_monomial (β n : σ →₀ ℕ) (c : R) :
    dividedDeriv R β (monomial n c) = multiChoose n β • monomial (n - β) c := by
  have h : (monomial n c : MvPolynomial σ R) = c • basisMonomials σ R n := by
    simp [smul_monomial]
  rw [h, map_smul, dividedDeriv, Module.Basis.constr_basis, smul_comm, smul_monomial, smul_eq_mul,
    mul_one]

theorem coeff_dividedDeriv (β m : σ →₀ ℕ) (P : MvPolynomial σ R) :
    AddMonoidAlgebra.coeff (dividedDeriv R β P) m = multiChoose (m + β) β • AddMonoidAlgebra.coeff P (m + β) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [dividedDeriv_monomial, AddMonoidAlgebra.coeff_smul_apply, coeff_monomial, coeff_monomial]
    by_cases h : n = m + β
    · subst h; simp
    · rw [ite_eq_right h, smul_zero]
      by_cases h0 : multiChoose n β = 0
      · rw [h0, zero_smul]
      · rw [ite_eq_right, smul_zero]
        rintro rfl
        exact h (tsub_add_cancel_of_le (le_of_multiChoose_ne_zero h0)).symm
  | add P Q hP hQ =>
    rw [map_add]
    rw [AddMonoidAlgebra.coeff_add]
    change ((dividedDeriv R β P).coeff m + (dividedDeriv R β Q).coeff m) =
      multiChoose (m + β) β • (P.coeff (m + β) + Q.coeff (m + β))
    rw [hP, hQ, smul_add]

@[simp] theorem dividedDeriv_zero : dividedDeriv R (0 : σ →₀ ℕ) =
    (1 : Module.End R (MvPolynomial σ R)) := by
  apply LinearMap.ext
  intro P
  apply MvPolynomial.ext
  intro m
  simp [coeff_dividedDeriv]

end Divided

section Contraction

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {ι κ : Type*}

variable [Fintype κ]

variable [Fintype ι]


end Contraction

end GlobalTheory.Wick
