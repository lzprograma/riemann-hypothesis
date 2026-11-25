module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexTrans

end KLinesGenIndexTrans


open KLinesGenIndexTrans in
theorem LinesGenIndexTrans.proof (h1 : LinesLatticeBasis.Statement)
    (h2 : LinesGenIndexDet.Statement) : LinesGenIndexTrans.Statement := by
  intro V _ _ _ A B C hA hB hC
  classical
  obtain ⟨bA, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) A hA
  obtain ⟨bB, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) B hB
  obtain ⟨bC, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) C hC
  have hAB := h2 V _ bA bB _ _ (Submodule.span_int_eq_addSubgroupClosure _) (Submodule.span_int_eq_addSubgroupClosure _)
  have hBC := h2 V _ bB bC _ _ (Submodule.span_int_eq_addSubgroupClosure _) (Submodule.span_int_eq_addSubgroupClosure _)
  have hAC := h2 V _ bA bC _ _ (Submodule.span_int_eq_addSubgroupClosure _) (Submodule.span_int_eq_addSubgroupClosure _)
  refine ⟨?_, ?_⟩
  · rw [hAB]
    have h0 : (bA.det bB : ℚ) ≠ 0 := (bA.isUnit_det bB).ne_zero
    positivity
  · rw [hAB, hBC, hAC, ← abs_mul, ← Rat.cast_mul, Module.Basis.det_mul_det]

end GroundTheory.Heights₂.Heights
