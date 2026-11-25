module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

namespace GlobalTheory.IntegralNormBound

theorem main {k A : Type} [Field k] [CommRing A] [Algebra k A] {Q : Ideal A} {π : A}
    (hπ : π ∈ Q) (hres : ∀ c : A, ∃ a : k, c - algebraMap k A a ∈ Q)
    (hfil : ∀ m : ℕ, Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + 1)) :
    ∀ (m : ℕ) (u : A), ∃ p : Polynomial k, u - Polynomial.aeval π p ∈ Q ^ m := by
  intro m u
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨y, hy, q, hq, hyq⟩ := Submodule.mem_sup.mp (hfil m hp)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    obtain ⟨a, ha⟩ := hres c
    refine ⟨p + Polynomial.C a * Polynomial.X ^ m, ?_⟩
    have hpm : π ^ m * (c - algebraMap k A a) ∈ Q ^ (m + 1) := by
      rw [pow_succ]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ m) ha
    have key : u - Polynomial.aeval π (p + Polynomial.C a * Polynomial.X ^ m)
        = q + π ^ m * (c - algebraMap k A a) := by
      simp only [map_add (f := _), map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow]
      linear_combination (-1 : A) * hyq
    rw [key]
    exact Ideal.add_mem _ hq hpm

end GlobalTheory.IntegralNormBound
