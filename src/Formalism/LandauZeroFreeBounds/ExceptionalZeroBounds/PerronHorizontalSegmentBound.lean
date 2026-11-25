module

import Formalism.ZeroFreeRegion.PerronKernelBounds

public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf

@[expose] public section
open Complex MeasureTheory
noncomputable section
namespace Formalism.ZeroFreeDirichlet

theorem norm_sum_le_of_card_le_one (B : Finset ℝ) (hB : B.card ≤ 1) (f : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ β ∈ B, ‖f β‖ ≤ M) : ‖∑ β ∈ B, f β‖ ≤ M :=
  (norm_sum_le B f).trans ((Finset.sum_le_card_nsmul B _ M hf).trans
    (by simpa using nsmul_le_nsmul_left hM hB))

theorem log_conductor_pos_real (q : ℕ) [NeZero q] (u : ℝ) : 0 < Real.log ((q : ℝ) * (|u| + 2)) :=
  Real.log_pos (one_lt_mul_of_le_of_lt (Nat.one_le_cast.mpr (NeZero.pos q)) (by linarith [abs_nonneg u]))
theorem log_analytic_conductor_mono (q : ℕ) [NeZero q] (u T : ℝ) (hu : |u| ≤ T) :
    Real.log ((q : ℝ) * (|u| + 2)) ≤ Real.log ((q : ℝ) * (T + 2)) :=
  Real.log_le_log (mul_pos (Nat.cast_pos.mpr (NeZero.pos q)) (by positivity)) (by gcongr)
private theorem negLD_le_of_dist {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {c₁ C d : ℝ}
    {B : Finset ℝ} (hB : B.card ≤ 1)
    (hD : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    {s : ℂ} (hreg : InRegion (c₁ / 2) q s) (hd : 0 < d) (hdist : ∀ β ∈ B, d ≤ ‖s - (β : ℂ)‖) :
    ‖negLD χ s‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 + 1 / d := by
  have hne (β : ℝ) (hβ : β ∈ B) : s ≠ (β : ℂ) := fun h => by
    have := hdist β hβ; simp [h] at this; linarith
  have hsum := norm_sum_le_of_card_le_one B hB (fun β : ℝ => 1 / (s - (β : ℂ))) (1 / d)
    (one_div_nonneg.mpr hd.le) fun β hβ => by
      rw [norm_div, norm_one]; exact one_div_le_one_div_of_le hd (hdist β hβ)
  have htri := norm_sub_le (negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))) (∑ β ∈ B, 1 / (s - (β : ℂ)))
  rw [add_sub_cancel_right] at htri; linarith [hD s hreg hne]

theorem perron_horizontal_segment_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (c₁ C : ℝ)
    (B : Finset ℝ) (hB : B.card ≤ 1)
    (hD : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (y T x v σ₀ σ₁ : ℝ) (hy : 1 ≤ y) (hT : 1 ≤ T) (hv : |v| = T)
    (hσ₁ : 1 - (c₁ / 2) / Real.log ((q : ℝ) * (T + 2)) ≤ σ₁)
    (hx1 : σ₁ ≤ x) (hx2 : x ≤ σ₀) :
    ‖Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤
      (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  set s : ℂ := (x : ℂ) + (v : ℂ) * I
  have him (r : ℝ) : T ≤ ‖s - r‖ := by simpa [s, hv] using Complex.abs_im_le_norm (s - r)
  have hN : ‖negLD χ s‖ ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 := by
    simpa [s, hv] using negLD_le_of_dist χ hB hD
      (by simpa [InRegion, s, hv] using hσ₁.trans hx1) zero_lt_one fun β _ => hT.trans (him β)
  exact PerronKernel.norm_le hy0 (zero_lt_one.trans_le hT) (by simp [s, hv]) hN
    (by simpa [s] using Real.rpow_le_rpow_of_exponent_le hy hx2)

theorem perron_left_line_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (c₁ C : ℝ)
    (hc₁ : 0 ≤ c₁) (hC : 0 ≤ C) (B : Finset ℝ) (hB : B.card ≤ 1)
    (hD : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (y T u σ₁ δ ε : ℝ) (hy : 0 < y) (hu : |u| ≤ T)
    (hσ₁ : 1 - (c₁ / 2) / Real.log ((q : ℝ) * (T + 2)) ≤ σ₁) (hhalf : 1 / 2 ≤ σ₁)
    (hε : 0 < ε) (hgap : ε ≤ 1 - σ₁) (hδ : 0 < δ) (hδB : ∀ β ∈ B, δ ≤ |σ₁ - β|) :
    ‖Fchi χ y ((σ₁ : ℂ) + u * I)‖ ≤
      (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ) * y ^ σ₁ * (2 / ε) := by
  set s : ℂ := (σ₁ : ℂ) + (u : ℂ) * I
  have hsre : s.re = σ₁ := by simp [s]
  have hsim : s.im = u := by simp [s]
  have hLu := log_conductor_pos_real q u; have hmono := log_analytic_conductor_mono q u T hu
  have hreg : InRegion (c₁ / 2) q s := by
    unfold InRegion; rw [hsim, hsre]; linarith [div_le_div_of_nonneg_left (by linarith : 0 ≤ c₁ / 2) hLu hmono]
  have hD0 := negLD_le_of_dist χ hB hD hreg hδ fun β hβ =>
    (hδB β hβ).trans (by simpa [hsre] using Complex.abs_re_le_norm (s - (β : ℂ)))
  rw [hsim] at hD0
  have hN : ‖negLD χ s‖ ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ := by
    linarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLu.le hmono 2) hC]
  exact PerronKernel.norm_left_le (w := s) hy hε (by simpa [hsre] using hhalf)
    (by simpa [hsre] using hgap) hN (by rw [hsre])

theorem real_zero_residue_term_bound (y β σ₁ ε : ℝ) (hy : 1 ≤ y) (hβ : 1 / 2 ≤ β) (hβσ : β ≤ σ₁)
    (hε : 0 < ε) (hgap : ε ≤ 1 - σ₁) :
    ‖(y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤ y ^ σ₁ * (2 / ε) := by
  simpa only [one_mul] using PerronKernel.norm_left_le (z := (1 : ℂ)) (w := (β : ℂ))
    (P := y ^ σ₁) (zero_lt_one.trans_le hy) hε hβ (hgap.trans (by linarith : 1 - σ₁ ≤ 1 - β))
    (le_of_eq (norm_one : ‖(1 : ℂ)‖ = 1)) (Real.rpow_le_rpow_of_exponent_le hy hβσ)

end Formalism.ZeroFreeDirichlet
