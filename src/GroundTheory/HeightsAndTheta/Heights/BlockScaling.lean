module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.BlockScaling

open MvPolynomial

theorem eval₂_mul_block_right {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {R S : Type*} [CommSemiring R] [CommSemiring S] (g : R →+* S)
    (x : (Σ k, ι k) → S) (t : K → S) {p : MvPolynomial (Σ k, ι k) R} {d : K → ℕ}
    (hp : ∀ m ∈ p.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) :
    eval₂ g (fun v => x v * t v.1) p = eval₂ g x p * ∏ k, t k ^ d k := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [eval₂_sum, eval₂_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [eval₂_monomial, eval₂_monomial, mul_assoc]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  show ∏ i, t k ^ m ⟨k, i⟩ = t k ^ d k
  rw [Finset.prod_pow_eq_pow_sum, hp m hm k]

theorem eval₂_mul_block_left {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {R S : Type*} [CommSemiring R] [CommSemiring S] (g : R →+* S)
    (t : K → S) (x : (Σ k, ι k) → S) {p : MvPolynomial (Σ k, ι k) R} {d : K → ℕ}
    (hp : ∀ m ∈ p.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) :
    eval₂ g (fun v => t v.1 * x v) p = (∏ k, t k ^ d k) * eval₂ g x p := by
  simpa [mul_comm] using eval₂_mul_block_right g x t hp

theorem eval₂_cone_block {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {R S : Type*} [CommSemiring R] [CommSemiring S] (g : R →+* S)
    (x : (Σ k, ι k) → S) {p : MvPolynomial (Σ k, ι k) R} {d : K → ℕ}
    (hp : ∀ m ∈ p.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) :
    eval₂ (C.comp g) (fun v => C (x v) * X v.1) p = C (eval₂ g x p) * ∏ k, X k ^ d k :=
  (eval₂_mul_block_right (C.comp g) (C ∘ x) X hp).trans (by rw [← eval₂_comp_left])

theorem aeval_cone_block {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (x : (Σ k, ι k) → S) {p : MvPolynomial (Σ k, ι k) R} {d : K → ℕ}
    (hp : ∀ m ∈ p.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) :
    aeval (fun v => C (x v) * X v.1) p = C (aeval x p) * ∏ k, X k ^ d k :=
  eval₂_cone_block (algebraMap R S) x hp

theorem sum_eq_of_isWeightedHomogeneous_single {K : Type*} [Fintype K] [DecidableEq K]
    {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommSemiring R]
    {p : MvPolynomial (Σ k, ι k) R} {d : K → ℕ}
    (hp : IsWeightedHomogeneous (fun v : Σ k, ι k => (Pi.single v.1 1 : K → ℕ)) p d)
    {m : (Σ k, ι k) →₀ ℕ} (hm : m ∈ p.support) (k : K) :
    ∑ i, m ⟨k, i⟩ = d k := by
  have h1 := congrFun (hp (mem_support_iff.mp hm)) k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h1
  rw [← h1, Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'; simp [Ne.symm hk']
  · simp

end GroundTheory.Heights₂.Heights.BlockScaling
