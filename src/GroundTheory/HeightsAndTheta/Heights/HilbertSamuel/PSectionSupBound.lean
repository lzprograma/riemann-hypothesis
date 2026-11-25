module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionSupBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionSupBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartPiece (c : ∀ k, ι k) : Set ((Σ k, ι k) → ℂ) :=
  Metric.closedBall 0 1 ∩ {w | ∀ k, w ⟨k, c k⟩ = 1}

theorem isCompact_chartPiece (c : ∀ k, ι k) : IsCompact (chartPiece c) := by
  refine (isCompact_closedBall _ _).inter_right ?_
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun k => isClosed_eq (continuous_apply _) continuous_const

theorem exists_lower (A : HermLine ι) (hA : ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) (c : ∀ k, ι k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) →
      (∀ k, z ⟨k, c k⟩ ≠ 0) → ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k ≤ M * A.h z := by
  have hsub : chartPiece c ⊆ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun w hw k =>
    ⟨c k, by rw [hw.2 k]; exact one_ne_zero⟩
  have hcont : ContinuousOn (fun w => (A.h w)⁻¹) (chartPiece c) :=
    (hA.mono hsub).inv₀ fun w hw => (A.pos w (hsub hw)).ne'
  obtain ⟨M, hM⟩ := (isCompact_chartPiece c).exists_bound_of_continuousOn hcont
  refine ⟨|M|, abs_nonneg M, fun z hmax hz0 => ?_⟩
  have hr : ∀ k, 0 < ‖z ⟨k, c k⟩‖ := fun k => norm_pos_iff.mpr (hz0 k)
  set s : K → ℂ := fun k => (z ⟨k, c k⟩)⁻¹ with hs
  have hs0 : ∀ k, s k ≠ 0 := fun k => inv_ne_zero (hz0 k)
  set w : (Σ k, ι k) → ℂ := fun p => s p.1 * z p with hw
  have hwS : w ∈ chartPiece c := by
    refine ⟨?_, fun k => inv_mul_cancel₀ (hz0 k)⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro p
    obtain ⟨k, i⟩ := p
    show ‖(z ⟨k, c k⟩)⁻¹ * z ⟨k, i⟩‖ ≤ 1
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (hr k), mul_one]
    exact hmax k i
  have hwpos : 0 < A.h w := A.pos w (hsub hwS)
  have h1 : 1 ≤ |M| * A.h w := by
    have := (hM w hwS).trans (le_abs_self M)
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hwpos] at this
    rw [inv_le_iff_one_le_mul₀ hwpos] at this
    exact this
  have hAw : A.h w = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ * A.h z := by
    rw [hw, A.smul s z hs0, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hs, norm_inv, inv_zpow]
  have hR : 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k := Finset.prod_pos fun k _ => zpow_pos (hr k) _
  rw [hAw] at h1
  calc ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * 1 := (mul_one _).symm
    _ ≤ (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * (|M| * ((∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ * A.h z)) :=
        mul_le_mul_of_nonneg_left h1 hR.le
    _ = |M| * A.h z := by field_simp

end SectionSupBound


open SectionBounded SectionSupBound in
theorem SectionSupBound.proof : SectionSupBound.Statement := by
  intro K _ ι _ Ω _ y A τ e hA he
  obtain ⟨S, hS0, hS⟩ := SectionBounded.exists_bound_of_lower y A τ he fun c _ => by
    obtain ⟨M, hM0, hM⟩ := SectionSupBound.exists_lower A hA c
    exact ⟨M, hM0, fun z _ => hM z⟩
  refine ⟨Real.log (1 + S), Real.log_nonneg (by linarith), ?_⟩
  rw [Real.exp_log (by linarith)]
  intro dg dh g h z hg hh hdeg hgy hz
  have h1 := hS dg dh g h z hg hh hdeg hgy hz
  have hAh : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  calc ‖eval z (map (Int.castRingHom ℂ) g)‖
      ≤ S * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := h1
    _ ≤ (1 + S) * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
        have := norm_nonneg (eval z (map (Int.castRingHom ℂ) h))
        gcongr
        linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
