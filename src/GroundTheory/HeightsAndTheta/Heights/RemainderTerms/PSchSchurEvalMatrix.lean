module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur

@[expose] public section

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchSchurEvalMatrix.aeval_completeSymmetric (h1 : SchCompleteAtRootsOfUnity.Statement)
    (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (d : ℤ) :
    aeval (rootOfUnityPoint N k) (completeSymmetric (Fin N) d) =
      if 0 ≤ d ∧ (k : ℤ) ∣ d then 1 else 0 := by
  unfold completeSymmetric
  by_cases h0 : 0 ≤ d
  · rw [ite_eq_left h0, h1 N k d.toNat hk hkN]
    have hdiv : (k ∣ d.toNat) ↔ ((k : ℤ) ∣ d) := by
      rw [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg h0]
    by_cases hd : (k : ℤ) ∣ d
    · rw [ite_eq_left (hdiv.mpr hd), ite_eq_left ⟨h0, hd⟩]
    · rw [ite_eq_right (fun h => hd (hdiv.mp h)), ite_eq_right (fun h => hd h.2)]
  · rw [ite_eq_right h0, map_zero, ite_eq_right (fun h => h0 h.1)]

theorem SchSchurEvalMatrix.proof (h1 : SchCompleteAtRootsOfUnity.Statement) :
    SchSchurEvalMatrix.Statement := by
  intro N k r nu hk hkN
  unfold schur
  rw [AlgHom.map_det]
  congr 1
  ext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    SchSchurEvalMatrix.aeval_completeSymmetric h1 N k hk hkN]
  rfl

end

end GroundTheory.Heights₂.Heights.RestTerms
