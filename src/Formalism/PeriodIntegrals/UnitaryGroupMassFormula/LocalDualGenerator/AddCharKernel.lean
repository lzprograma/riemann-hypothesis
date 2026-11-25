module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.FpDualUnram
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace PI.LocDualGen.Psi

open PI.LocDualGen.W

theorem addCharKernel : PsiKer := by
  rintro l _ t a ⟨n, hn⟩ ht
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hexp : Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = 1 ↔ a.den = 1 := by
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨m, hm⟩
      rw [mul_comm (m : ℂ)] at hm
      have h1 : (a : ℂ) = (m : ℂ) := mul_left_cancel₀ hI hm
      have ha : a = m := by exact_mod_cast h1
      rw [ha]
      exact Rat.den_intCast m
    · intro h1
      refine ⟨a.num, ?_⟩
      have ha : (a : ℂ) = (a.num : ℂ) := by
        have h := (Rat.den_eq_one_iff a).mp h1
        exact_mod_cast h.symm
      rw [ha]
      ring
  have hna : ‖t‖ ≤ 1 ↔ ‖(a : ℚ_[l])‖ ≤ 1 := by
    constructor
    · intro h
      have e : (a : ℚ_[l]) = t + ((a : ℚ_[l]) - t) := by ring
      rw [e]
      refine le_trans (Padic.nonarchimedean _ _) (max_le h ?_)
      rw [norm_sub_rev]
      exact ht
    · intro h
      have e : t = (t - (a : ℚ_[l])) + (a : ℚ_[l]) := by ring
      rw [e]
      exact le_trans (Padic.nonarchimedean _ _) (max_le ht h)
  have hrat : ‖(a : ℚ_[l])‖ ≤ 1 ↔ a.den = 1 := by
    have hden : a.den = 1 ↔ ¬ l ∣ a.den :=
      ⟨fun h => h ▸ (Fact.out : l.Prime).not_dvd_one, fun h => by
        rcases n with _ | n
        · exact hn
        · exact absurd (hn ▸ dvd_pow_self l n.succ_ne_zero) h⟩
    rw [hden, ← Rat.padicValuation_le_one_iff (p := l), ← Padic.comap_mulValuation_eq_padicValuation]
    by_cases ha : (a : ℚ_[l]) = 0
    · simp [ha]
    · rw [Padic.norm_le_one_iff_val_nonneg]
      simp [Padic.mulValuation_toFun, ha]
  rw [hexp, hna, hrat]

end PI.LocDualGen.Psi
