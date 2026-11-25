module

public import Formalism.SharpRestriction.CuspSpanNormBounds.ThinScalesBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.HSumRight
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.MemPerpSpanIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem h_frame (f : Fin (r + 1) → V) (T : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (a b : Fin (r + 1)) :
    H.h (f b) (f a) = if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0 := by
  split_ifs with hab
  · obtain ⟨rfl, rfl⟩ := hab
    exact hF.2
  · apply hF.1 b a
    by_contra hc
    push Not at hc
    exact hab ⟨hc.2, hc.1⟩

theorem adj_last (f f' : Fin (r + 1) → V) :
    (H.Zhat f f').adjugate (Fin.last r) (Fin.last r) = H.Dl f f' r := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  unfold HermSp.Dl
  rw [dite_eq_left (Nat.le_succ r)]
  have hpow : ((-1 : E) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]
    simp
  rw [hpow, one_mul]
  congr 1
  ext i j
  simp [Matrix.submatrix_apply, Fin.succAbove_last]
  rfl

end Formalism.L2.SG.LocalCountModules.LocCntCommon
