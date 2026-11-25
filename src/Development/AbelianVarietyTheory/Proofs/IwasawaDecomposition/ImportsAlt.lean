module

import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsTer
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

namespace GlobalTheory.KeyLemmaTwo

lemma key {z : ℂ} (h : ∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) (k : ℕ) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  apply GlobalTheory.IterationConvergence.iter <;> assumption

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := key h k
  have h2 := h (2 ^ k)
  rw [div_lt_iff₀ hpos] at hk
  linarith

end GlobalTheory.KeyLemmaTwo
