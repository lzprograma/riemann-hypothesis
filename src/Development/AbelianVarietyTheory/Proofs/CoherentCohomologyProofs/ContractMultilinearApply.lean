module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct BigOperators

namespace GlobalTheory.MultilinearContraction

section

variable {ι : Type*} [Fintype ι] [dι : DecidableEq ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]

def contractMultilinear (φ : ∀ i, X i →ₗ[R] R) (j : ι) : (Π i, X i) →ₘₗ[R] X j where
  toFun x := (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j
  map_update_add' := by
    intro inst x k y z
    have h₁ : j ∉ @Finset.erase ι dι Finset.univ j := @Finset.notMem_erase ι dι j Finset.univ
    have h₂ : k ≠ j → k ∈ @Finset.erase ι dι Finset.univ j := fun h =>
      (@Finset.mem_erase ι dι _ _ _).2 ⟨h, Finset.mem_univ _⟩
    generalize @Finset.erase ι dι Finset.univ j = S at h₁ h₂ ⊢
    simp only [Function.apply_update (fun i => φ i)]
    by_cases h : k = j
    · subst h
      simp only [Finset.prod_update_of_notMem h₁,
        Function.update_self, smul_add]
    · have hk := h₂ h
      simp only [Finset.prod_update_of_mem hk, Function.update_of_ne (Ne.symm h), map_add (f := _),
        add_mul, add_smul]
  map_update_smul' := by
    intro inst x k c y
    have h₁ : j ∉ @Finset.erase ι dι Finset.univ j := @Finset.notMem_erase ι dι j Finset.univ
    have h₂ : k ≠ j → k ∈ @Finset.erase ι dι Finset.univ j := fun h =>
      (@Finset.mem_erase ι dι _ _ _).2 ⟨h, Finset.mem_univ _⟩
    generalize @Finset.erase ι dι Finset.univ j = S at h₁ h₂ ⊢
    simp only [Function.apply_update (fun i => φ i)]
    by_cases h : k = j
    · subst h
      simp only [Finset.prod_update_of_notMem h₁, Function.update_self, RingHom.id_apply]
      exact smul_comm _ _ _
    · have hk := h₂ h
      simp only [Finset.prod_update_of_mem hk, Function.update_of_ne (Ne.symm h), map_smul,
        RingHom.id_apply, smul_eq_mul, mul_assoc, mul_smul]

@[simp] theorem contractMultilinear_apply (φ : ∀ i, X i →ₗ[R] R) (j : ι) (x : ∀ i, X i) :
    contractMultilinear φ j x = (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j := rfl

noncomputable def contract (φ : ∀ i, X i →ₗ[R] R) (j : ι) : (⨂[R] i, X i) →ₗ[R] X j :=
  PiTensorProduct.lift (contractMultilinear φ j)

theorem contract_def (φ : ∀ i, X i →ₗ[R] R) (j : ι) :
    contract φ j = PiTensorProduct.lift (contractMultilinear φ j) := rfl

@[simp] theorem contract_tprod (φ : ∀ i, X i →ₗ[R] R) (j : ι) (x : ∀ i, X i) :
    contract φ j (⨂ₜ[R] i, x i) = (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j := by
  rw [contract_def, PiTensorProduct.lift.tprod, contractMultilinear_apply]

end

section

variable {ι : Type*} [Fintype ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]

def prodMultilinear (φ : ∀ i, X i →ₗ[R] R) : (Π i, X i) →ₘₗ[R] R :=
  (MultilinearMap.mkPiAlgebra R ι R).compLinearMap φ

@[simp] theorem prodMultilinear_apply (φ : ∀ i, X i →ₗ[R] R) (x : ∀ i, X i) :
    prodMultilinear φ x = ∏ i, φ i (x i) := rfl

noncomputable def prodForm (φ : ∀ i, X i →ₗ[R] R) : (⨂[R] i, X i) →ₗ[R] R :=
  PiTensorProduct.lift (prodMultilinear φ)

theorem prodForm_def (φ : ∀ i, X i →ₗ[R] R) :
    prodForm φ = PiTensorProduct.lift (prodMultilinear φ) := rfl

@[simp] theorem prodForm_tprod (φ : ∀ i, X i →ₗ[R] R) (x : ∀ i, X i) :
    prodForm φ (⨂ₜ[R] i, x i) = ∏ i, φ i (x i) := by
  rw [prodForm_def, PiTensorProduct.lift.tprod, prodMultilinear_apply]

end

end GlobalTheory.MultilinearContraction
