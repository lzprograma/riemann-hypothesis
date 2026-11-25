module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpUniMul
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

universe u_1

namespace GlobalTheory.UpperUnipotentProductInertiaEigenvalues

theorem isUpUni_mul {K : Type u_1} [inst : CommRing K] {N : ℕ} {U B : Matrix (Fin N) (Fin N) K}
    (hU : Formalism.MainNotions.S.IsUpUni U) (hB : Formalism.MainNotions.S.IsUpUni B) : Formalism.MainNotions.S.IsUpUni (U * B) := by
  apply GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption

end GlobalTheory.UpperUnipotentProductInertiaEigenvalues
