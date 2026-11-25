module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AlgDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.SumGramInr
import Mathlib.RingTheory.PiTensorProduct

@[expose] public section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem formC_of_rel (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hG : IsUnit (gramC cj Z T T').det) (Y W : Ix r → O) (c : Ix r → E)
    (hY : ∀ j, (Y j : E) = ∑ i, c i * gramC cj Z T T' i j) :
    formC O cj Z T T' Y W = ∑ j, c j * cj (W j) := by
  have hc : Matrix.vecMul (fun j => (Y j : E)) (gramC cj Z T T')⁻¹ = c := by
    have hYv : (fun j => (Y j : E)) = Matrix.vecMul c (gramC cj Z T T') := by
      funext j
      rw [hY j]
      rfl
    rw [hYv, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one]
  unfold formC
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul, ← congrFun hc j]
  rfl

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
