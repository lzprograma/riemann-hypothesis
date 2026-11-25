module

import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACorr
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.StepsL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.SharpEquivApply
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem gdet_rel (H : HermSp M V) {r : ℕ} (f₁ f₁' f₂ f₂' : Fin (r + 1) → V) (T T' : F)
    (hrel : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    H.Gdet f₂ f₂' T T' * H.normE (H.Dl f₁ f₁' (r + 1)) =
      H.normE (H.Dl f₂ f₂' (r + 1)) * H.Gdet f₁ f₁' T T' := by
  apply _root_.Formalism.L2.SG.LsDatumA.Gdet_rel <;> assumption

theorem unit_gramC_of (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F)
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD1 : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T')) :
    IsUnit (gramC (M.L.cj : E →+* E) (H.Zhat f f') (algebraMap F E T) (algebraMap F E T')).det := by
  rw [gramC_eq H f f' T T' hF hF', Matrix.det_transpose]
  obtain ⟨s, hs, hdet⟩ := gram_det H f f' T T' hF hF' hD1
  have : (H.gram (Sum.elim f f')).det = H.Gdet f f' T T' * s := by
    rw [← hdet, mul_assoc, hs, mul_one]
  rw [this]
  exact hG.mul ⟨⟨s, s, hs, hs⟩, rfl⟩

theorem thetaPresentation_of_nonsplit (h1 : CoordU) (h2 : AlgAll) (M : Model F E)
    (hsplit : M.split = none) (r n : ℕ) : ThetaPresentation M r n := by
  obtain ⟨L, sp, mu⟩ := M
  change sp = none at hsplit
  subst sp
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp hU2 Z₁ Z₂ e₁ e₂
  have hs : (⟨L, none, mu⟩ : Model F E).split = none := rfl
  have z₁ : Z₁.map (Model.R ⟨L, none, mu⟩).subtype = H.Zhat t₁.f t₁.f' := by
    rw [e₁]; exact zzplusOf_none hs _ _ _
  have z₂ : Z₂.map (Model.R ⟨L, none, mu⟩).subtype = H.Zhat f₂ f₂' := by
    rw [e₂]; exact zzplusOf_none hs _ _ _
  have hU1 : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := dl_succ_unit hyp
  have hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1) :=
    hyp.2.2.2.1.2.2.2.2.2
  have hint : ∀ a b, H.Zhat f₂ f₂' a b ∈ L.O := by
    intro a b
    rw [← z₂]
    exact (Z₂ a b).2
  have hT : t₁.T ∈ 𝒪[F] := hyp.1.1.2.1.2.2.2.1
  have hT' : t₁.T' ∈ 𝒪[F] := hyp.1.1.2.2.1.2.2.2.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hyp.1.1.2.1.2.1, hyp.1.1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hyp.1.1.2.2.1.2.1, hyp.1.1.2.2.1.2.2.1⟩
  have hGu₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := _root_.Formalism.L2.SG.LsDatumA.isUnit_Gdet H _ _ _ _ hyp.1.1.2.2.2.2.1
  have hGu₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hU2.mul (hU2.map L.cj)
    have := gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hrel
    have hp : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [this]; exact hN₂.mul hGu₁
    exact isUnit_of_mul_isUnit_left hp
  have hG1 := unit_gramC_of H _ _ _ _ hF₁ hF₁' hU1 hGu₁
  have hG2 := unit_gramC_of H _ _ _ _ hyp.2.1 hyp.2.2.1 hU2 hGu₂
  have hh : ((Z₁.map (Model.R ⟨L, none, mu⟩).subtype).submatrix Fin.castSucc Fin.castSucc).det *
      (Z₂.map (Model.R ⟨L, none, mu⟩).subtype).det =
      ((Z₂.map (Model.R ⟨L, none, mu⟩).subtype).submatrix Fin.castSucc Fin.castSucc).det *
      (Z₁.map (Model.R ⟨L, none, mu⟩).subtype).det := by
    rw [z₁, z₂, ← dl_eq_det, ← dl_eq_det, ← dl_full, ← dl_full]
    exact hrel
  rw [← z₁] at hG1
  rw [← z₂] at hG2
  rw [h1 F E ⟨L, none, mu⟩ hs r n V H hn t₁ f₂ f₂' φ φ' hyp hU2 hint, ← z₁, ← z₂]
  rw [dl_full] at hU1 hU2
  exact h2 E L.O (L.cj : E →+* E) (fun x => L.cj_cj x) (fun x hx => cj_mem_O L hx)
    r _ _ (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O L ⟨t₁.T, hT⟩) (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O L ⟨t₁.T', hT'⟩)
    (AlgEquiv.commutes _ _) (AlgEquiv.commutes _ _) Z₁ Z₂ ((congrArg (fun A => IsUnit A.det) z₁).mpr hU1)
    ((congrArg (fun A => IsUnit A.det) z₂).mpr hU2) hh hG1 hG2

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU
