module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Hermitian

@[expose] public section

universe u_1

namespace Bl.PosDefOfRealQuadratic

open scoped ComplexOrder in
theorem goal1 {X : Type u_1} [TopologicalSpace X] {m : ℕ} (A : X → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ i j, Continuous fun x => A x i j) (hH : ∀ x, (A x).IsHermitian)
    (x0 : X) (h0 : (A x0).PosDef) : ∀ᶠ x in nhds x0, (A x).PosDef := by
  have hAc : Continuous A := continuous_pi fun i => continuous_pi fun j => hA i j
  have hq : Continuous fun p : X × (Fin m → ℂ) => (star p.2 ⬝ᵥ (A p.1).mulVec p.2).re :=
    Complex.continuous_re.comp <|
      continuous_snd.star.dotProduct ((hAc.comp continuous_fst).matrix_mulVec continuous_snd)
  have key : ∀ᶠ x in nhds x0, ∀ y ∈ Metric.sphere (0 : Fin m → ℂ) 1,
      0 < (star y ⬝ᵥ (A x).mulVec y).re := by
    refine (isCompact_sphere (0 : Fin m → ℂ) 1).eventually_forall_of_forall_eventually fun y hy => ?_
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    exact (continuousAt_const (x := (x0, y))).eventually_lt (hq.continuousAt (x := (x0, y)))
      (Complex.pos_iff.mp (h0.dotProduct_mulVec_pos hy0)).1
  filter_upwards [key] with x hx
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hH x) fun v hv =>
    Complex.pos_iff.mpr ⟨?_, ((hH x).im_star_dotProduct_mulVec_self v).symm⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 := hx (((‖v‖⁻¹ : ℝ) : ℂ) • v) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ hn.ne'])
  have hscale : (star (((‖v‖⁻¹ : ℝ) : ℂ) • v) ⬝ᵥ (A x).mulVec (((‖v‖⁻¹ : ℝ) : ℂ) • v)).re =
      ‖v‖⁻¹ ^ 2 * (star v ⬝ᵥ (A x).mulVec v).re := by
    rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    rw [show ((‖v‖⁻¹ : ℝ) : ℂ) * (((‖v‖⁻¹ : ℝ) : ℂ) * (star v ⬝ᵥ (A x).mulVec v)) =
        (((‖v‖⁻¹ ^ 2 : ℝ) : ℂ)) * (star v ⬝ᵥ (A x).mulVec v) by push_cast; ring,
      Complex.re_ofReal_mul]
  rw [hscale] at h1
  exact pos_of_mul_pos_right h1 (by positivity)

end Bl.PosDefOfRealQuadratic
