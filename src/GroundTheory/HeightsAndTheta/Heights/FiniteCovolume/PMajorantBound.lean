module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

theorem majorant_mul_inv_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {H P : Matrix ι ι ℂ}
    (hM : IsMajorantOf H P) : H * P⁻¹ * H = P := by
  obtain ⟨hP, -, hdet, hPHP⟩ := hM
  nth_rw 1 [← hPHP]
  rw [mul_nonsing_inv_cancel_right _ _ hP.det_pos.ne'.isUnit,
    nonsing_inv_mul_cancel_right _ _ hdet]

theorem MajorantBound.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MajorantBound.Statement ι := by
  intro H P hM z
  obtain ⟨hP, hH, -⟩ := id hM
  let _ := P.toSeminormedAddCommGroup hP.posSemidef
  let _ := P.toInnerProductSpace hP.posSemidef
  set w := P⁻¹ *ᵥ (H *ᵥ z) with hw
  have inner_eq (x y : ι → ℂ) : inner ℂ x y = star x ⬝ᵥ (P *ᵥ y) := dotProduct_comm _ _
  have hPw : P *ᵥ w = H *ᵥ z := by
    rw [hw, mulVec_mulVec, mul_nonsing_inv _ hP.det_pos.ne'.isUnit, one_mulVec]
  apply le_of_sq_le_sq _ (hP.posSemidef.re_dotProduct_nonneg z)
  convert inner_mul_inner_self_le (𝕜 := ℂ) z w using 1
  · rw [norm_inner_symm (𝕜 := ℂ) w z, inner_eq, hPw, sq]
  · rw [inner_eq, inner_eq, hPw, hw, star_mulVec, star_mulVec, conjTranspose_nonsing_inv,
      hP.isHermitian.eq, hH.eq, vecMul_vecMul, ← dotProduct_mulVec, mulVec_mulVec,
      majorant_mul_inv_mul hM, sq]

end GroundTheory.Heights₂.Heights.FiniteCovolume
