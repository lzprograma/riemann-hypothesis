module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.MemPerpSpanIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.AdjLast
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.HSumRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem h_z_omP (f f' : Fin (r + 1) → V) (hD : IsUnit (H.Dl f f' (r + 1))) :
    H.h (f (Fin.last r)) (omP H f f') = 1 := by
  have hDl : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
    simp [Formalism.MainNotions.S.Loc.HermSp.Dl, Fin.castLE_rfl, Matrix.submatrix_id_id]
  have hz : ∀ b, H.h (f (Fin.last r)) (f' b) = M.L.cj (H.Zhat f f' (Fin.last r) b) := fun b => H.h_herm _ _
  have hsum : ∑ b, M.L.cj ((H.Zhat f f').adjugate b (Fin.last r)) * M.L.cj (H.Zhat f f' (Fin.last r) b) =
      M.L.cj (H.Zhat f f').det := by
    have h1 := congrFun (congrFun (Matrix.mul_adjugate (H.Zhat f f')) (Fin.last r)) (Fin.last r)
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1

    rw [← h1, map_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [map_mul, mul_comm]
  unfold omP
  rw [h_smul_right, Formalism.MainNotions.S.Loc.HermSp.om', h_sum_right]
  simp only [hz]
  rw [hsum, ← map_mul, ← hDl, Ring.inverse_mul_cancel _ hD, map_one]

theorem omP_mem_span (f f' : Fin (r + 1) → V) :
    omP H f f' ∈ Submodule.span E (Set.range (Sum.elim f f')) := by
  unfold omP
  apply Submodule.smul_mem
  unfold Formalism.MainNotions.S.Loc.HermSp.om'
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)

end Formalism.L2.SG.LocalCountModules.LocCntCommon
