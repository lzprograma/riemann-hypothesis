module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

@[expose] public section

open scoped NNReal TensorProduct

namespace GlobalTheory

theorem valuation_map_algEquiv_eq_of_le_one_iff_isIntegral (R Ω : Type) [CommRing R] [Nontrivial R]
    [Field Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω]
    (hinj : Function.Injective (algebraMap R Ω)) (v : Valuation Ω ℝ≥0)
    (hv : ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x) (g : Ω ≃ₐ[R] Ω) (x : Ω) : v (g x) = v x := by
  have hle : ∀ a b : Ω, v (g a) ≤ v (g b) ↔ v a ≤ v b := by
    intro a b
    by_cases hb : b = 0
    · subst hb
      simp
    · have hgb : g b ≠ 0 := by simpa using hb
      have hvb : 0 < v b := by simpa [pos_iff_ne_zero] using hb
      have hvgb : 0 < v (g b) := by simpa [pos_iff_ne_zero] using hgb
      have h1 : v (a / b) ≤ 1 ↔ v a ≤ v b := by rw [map_div₀, div_le_one hvb]
      have h2 : v (g (a / b)) ≤ 1 ↔ v (g a) ≤ v (g b) := by
        rw [map_div₀ g, map_div₀, div_le_one hvgb]
      rw [← h1, ← h2, hv, hv, isIntegral_algEquiv]
  have hlt : ∀ a b : Ω, v (g a) < v (g b) ↔ v a < v b := by
    intro a b
    rw [← not_le, ← not_le, hle]
  have hstep : ∀ k : ℕ, (g ^ (k + 1)) x = g ((g ^ k) x) := by
    intro k
    rw [pow_succ', AlgEquiv.mul_apply]
  have hdown : ∀ n : ℕ, v ((g ^ (n + 1)) x) < v ((g ^ n) x) ↔ v (g x) < v x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hlt ((g ^ (n + 1)) x) ((g ^ n) x)
      rw [← hstep (n + 1), ← hstep n] at h
      exact h.trans ih
  have hup : ∀ n : ℕ, v ((g ^ n) x) < v ((g ^ (n + 1)) x) ↔ v x < v (g x) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hlt ((g ^ n) x) ((g ^ (n + 1)) x)
      rw [← hstep n, ← hstep (n + 1)] at h
      exact h.trans ih
  obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) x
  have hmap : p.map (algebraMap R Ω) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff hinj]
  have hmem : ∀ n : ℕ, (g ^ n) x ∈ p.rootSet Ω := by
    intro n
    rw [Polynomial.mem_rootSet']
    exact ⟨hmap, by rw [Polynomial.aeval_algEquiv]; simp [hpx]⟩
  obtain ⟨k, l, hkl, heq⟩ :=
    (Polynomial.rootSet_finite p Ω).exists_lt_map_eq_of_forall_mem hmem
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hs : ∀ n : ℕ, v ((g ^ (n + 1)) x) < v ((g ^ n) x) := fun n => (hdown n).mpr h
    have := (strictAnti_nat_of_succ_lt (f := fun n => v ((g ^ n) x)) hs) hkl
    simp only [heq] at this
    exact lt_irrefl _ this
  · have hs : ∀ n : ℕ, v ((g ^ n) x) < v ((g ^ (n + 1)) x) := fun n => (hup n).mpr h
    have := (strictMono_nat_of_lt_succ (f := fun n => v ((g ^ n) x)) hs) hkl
    simp only [heq] at this
    exact lt_irrefl _ this

end GlobalTheory
