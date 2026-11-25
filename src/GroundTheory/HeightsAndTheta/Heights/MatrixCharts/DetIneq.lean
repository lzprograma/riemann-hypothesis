module

public import Mathlib.Analysis.Matrix.Order

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCDet

open Matrix
open scoped MatrixOrder ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

theorem det_eq_ofReal_re {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A.det = (RCLike.re A.det : 𝕜) :=
  (RCLike.conj_eq_iff_re.mp (IsSelfAdjoint.of_nonneg hA.det_nonneg)).symm

theorem re_det_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) : 0 ≤ RCLike.re A.det :=
  (RCLike.nonneg_iff.mp hA.det_nonneg).1

theorem re_det_pos {A : Matrix n n 𝕜} (hA : A.PosDef) : 0 < RCLike.re A.det :=
  (RCLike.pos_iff.mp hA.det_pos).1

theorem one_le_re_det_one_add {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) :
    1 ≤ RCLike.re (1 + Q).det := by
  have hdet : (1 + Q).det =
      ((1 : Matrix n n 𝕜) + diagonal (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues)).det := by
    conv_lhs =>
      rw [hQ.isHermitian.spectral_theorem,
        ← map_one (Unitary.conjStarAlgAut 𝕜 _ hQ.isHermitian.eigenvectorUnitary), ← map_add]
    exact det_units_conj (Unitary.toUnits hQ.isHermitian.eigenvectorUnitary) _
  rw [hdet, ← diagonal_one, diagonal_add, det_diagonal]
  simp only [Function.comp_apply, ← RCLike.ofReal_one (K := 𝕜), ← RCLike.ofReal_add,
    ← RCLike.ofReal_prod, RCLike.ofReal_re]
  exact Finset.one_le_prod₀ fun i _ => le_add_of_nonneg_right (hQ.eigenvalues_nonneg i)

theorem re_det_le_re_det_add {A P : Matrix n n 𝕜} (hA : A.PosSemidef) (hP : P.PosSemidef) :
    RCLike.re A.det ≤ RCLike.re (A + P).det := by
  by_cases h0 : A.det = 0
  · rw [h0, map_zero]
    exact re_det_nonneg (hA.add hP)
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [star_eq_conjTranspose] at hB
  have hBdet : B.det ≠ 0 := by
    intro hb
    apply h0
    rw [hB, det_mul, hb, mul_zero]
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hBHu : IsUnit Bᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hBdet)
  set Q := (B⁻¹)ᴴ * P * B⁻¹ with hQdef
  have hQ : Q.PosSemidef := by
    have := hP.mul_mul_conjTranspose_same ((B⁻¹)ᴴ)
    simpa [hQdef, conjTranspose_conjTranspose] using this
  have hAP : A + P = Bᴴ * (1 + Q) * B := by
    rw [hQdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← hB]
    congr 1
    rw [conjTranspose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hBHu, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBu, Matrix.mul_one]
  have hdet : (A + P).det = A.det * (1 + Q).det := by
    rw [hAP, hB, det_mul, det_mul, det_mul]
    ring
  rw [hdet, det_eq_ofReal_re hA, det_eq_ofReal_re (PosSemidef.one.add hQ),
    ← RCLike.ofReal_mul]
  simp only [RCLike.ofReal_re]
  exact le_mul_of_one_le_right (re_det_nonneg hA) (one_le_re_det_one_add hQ)

theorem re_det_mono {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hAB : (B - A).PosSemidef) :
    RCLike.re A.det ≤ RCLike.re B.det := by
  have := re_det_le_re_det_add hA hAB
  rwa [add_sub_cancel] at this

end GroundTheory.Heights₂.Heights.MCDet
