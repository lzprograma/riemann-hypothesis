module

public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Unramified.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Unramified.Finite

@[expose] public section

open IsLocalRing

namespace GlobalTheory.QuadraticEtale

section Galois

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (σ : S →+* S)

theorem isIntegral_of_involution (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x ∈ (algebraMap R S).range) : Algebra.IsIntegral R S := by
  refine ⟨fun x => ?_⟩
  obtain ⟨t, ht⟩ := hfix (x + σ x) (by rw [map_add (f := _), hσ, add_comm])
  obtain ⟨n, hn⟩ := hfix (x * σ x) (by rw [map_mul, hσ, mul_comm])
  refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, ht, hn]
    ring

variable [IsLocalRing R]

theorem algebraMap_mem_of_isMaximal [Algebra.IsIntegral R S] (n : Ideal S) [n.IsMaximal]
    {r : R} (hr : r ∈ maximalIdeal R) : algebraMap R S r ∈ n := by
  have h := eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) n)
  rw [← h] at hr
  exact hr

theorem isUnit_or_mem_of_fixed (hfix : ∀ x, σ x = x → x ∈ (algebraMap R S).range)
    {x : S} (hx : σ x = x) :
    IsUnit x ∨ x ∈ (maximalIdeal R).map (algebraMap R S) := by
  obtain ⟨r, rfl⟩ := hfix x hx
  by_cases hr : IsUnit r
  · exact Or.inl (hr.map _)
  · exact Or.inr (Ideal.mem_map_of_mem _ hr)

theorem exists_isUnit_add_mul (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x ∈ (algebraMap R S).range) (hgal : ∃ ω, IsUnit (ω - σ ω))
    {u : S} (hu : u * σ u = 1) : ∃ a, IsUnit (a + u * σ a) := by
  haveI := isIntegral_of_involution σ hσ hfix
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact ⟨0, isUnit_of_subsingleton _⟩
  obtain ⟨n, hn⟩ := Ideal.exists_maximal S
  obtain ⟨ω, hω⟩ := hgal
  by_contra hcon
  push Not at hcon
  have key : ∀ a, a + u * σ a ∈ n := by
    intro a
    have hz : σ ((a + u * σ a) * σ (a + u * σ a)) = (a + u * σ a) * σ (a + u * σ a) := by
      rw [map_mul, hσ, mul_comm]
    rcases isUnit_or_mem_of_fixed σ hfix hz with h | h
    · exact absurd (isUnit_of_mul_isUnit_left h) (hcon a)
    · have h1 : (a + u * σ a) * σ (a + u * σ a) ∈ n :=
        (Ideal.map_le_iff_le_comap (I := maximalIdeal R)).2
          (fun r hr => algebraMap_mem_of_isMaximal n hr) h
      have h2 : a + u * σ a = u * σ (a + u * σ a) := by
        rw [map_add (f := _), map_mul, hσ]
        linear_combination (-a) * hu
      rcases hn.isPrime.mem_or_mem h1 with h3 | h3
      · exact h3
      · rw [h2]; exact n.mul_mem_left _ h3
  have : ω - σ ω ∈ n := by
    have := n.sub_mem (key ω) (n.mul_mem_left (σ ω) (key 1))
    convert this using 1
    rw [map_one]; ring
  exact hn.ne_top (n.eq_top_of_isUnit_mem this hω)


omit [IsLocalRing R] [Algebra R S] [CommRing R] in
theorem exists_add_eq_one (hσ : ∀ x, σ (σ x) = x) (hgal : ∃ ω, IsUnit (ω - σ ω)) :
    ∃ t, t + σ t = 1 := by
  obtain ⟨ω, hω⟩ := hgal
  obtain ⟨v, hv⟩ := hω.exists_right_inv
  have h2 := congrArg σ hv
  rw [map_mul, map_sub, hσ, map_one] at h2
  refine ⟨ω * v, ?_⟩
  rw [map_mul]
  have : σ v = -v := by linear_combination (-σ v) * hv - v * h2
  rw [this]
  linear_combination hv

variable {M : Type*} [AddCommGroup M] [Module S M]

end Galois

section Quadratic

open TensorProduct Module

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem eq_coord (B : Basis (Fin 2) R S) (hB : B 0 = 1) (x : S) :
    x = algebraMap R S (B.repr x 0) + algebraMap R S (B.repr x 1) * B 1 := by
  conv_lhs => rw [← B.sum_repr x]
  rw [Fin.sum_univ_two, hB, Algebra.smul_def, Algebra.smul_def, mul_one]

theorem repr_coord_zero (B : Basis (Fin 2) R S) (hB : B 0 = 1) (r s : R) :
    B.repr (algebraMap R S r + algebraMap R S s * B 1) 0 = r := by
  rw [← mul_one (algebraMap R S r), ← hB, ← Algebra.smul_def, ← Algebra.smul_def]
  simp

theorem repr_coord_one (B : Basis (Fin 2) R S) (hB : B 0 = 1) (r s : R) :
    B.repr (algebraMap R S r + algebraMap R S s * B 1) 1 = s := by
  rw [← mul_one (algebraMap R S r), ← hB, ← Algebra.smul_def, ← Algebra.smul_def]
  simp

theorem coord_inj (B : Basis (Fin 2) R S) (hB : B 0 = 1) {r s r' s' : R}
    (h : algebraMap R S r + algebraMap R S s * B 1 = algebraMap R S r' + algebraMap R S s' * B 1) :
    r = r' ∧ s = s' :=
  ⟨by rw [← repr_coord_zero B hB r s, h, repr_coord_zero B hB],
    by rw [← repr_coord_one B hB r s, h, repr_coord_one B hB]⟩

theorem trace_coord (B : Basis (Fin 2) R S) (hB : B 0 = 1) {a b : R}
    (hab : B 1 * B 1 = algebraMap R S b + algebraMap R S a * B 1) (r s : R) :
    Algebra.trace R S (algebraMap R S r + algebraMap R S s * B 1) = 2 * r + s * a := by
  rw [Algebra.trace_eq_matrix_trace B, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, hB, mul_one, repr_coord_zero B hB]
  have : (algebraMap R S r + algebraMap R S s * B 1) * B 1
      = algebraMap R S (s * b) + algebraMap R S (r + s * a) * B 1 := by
    simp only [map_add (f := _), map_mul]
    linear_combination (algebraMap R S s) * hab
  rw [this, repr_coord_one B hB]
  ring

end Quadratic

section Unramified

open Module

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
  [Module.Free R S] [Algebra.FormallyUnramified R S]

section Star

variable [StarRing S]

end Star

end Unramified

end GlobalTheory.QuadraticEtale
