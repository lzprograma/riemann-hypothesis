module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.DlRSwapZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ThetaC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.HOmPOmPU
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.ThetaMbeUFalseOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.StepsL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.LamSZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AlgInj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.LamSMulVec
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.BRawHeadColsRight
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.MulVecSingleApply
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.PairGSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.FormCAddRight
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.SumMapCompSub
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AssembleG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.FwdEx
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AlgDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACut
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.GraphTransport
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.HSumRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.OmPMemSpan
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.MemHeadColsIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.DetSmulMk
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.FormCOfRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.GsLinSpec

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

def nuU (f f' : Fin (r + 1) → V) : E := H.h (omP H f f') (omP H f f')

def alU (f f' : Fin (r + 1) → V) (T : F) (u : V) : E :=
  Ring.inverse (1 + algebraMap F E T * nuU H f f') * (H.h u (omP H f f') - nuU H f f' * H.h u (f (Fin.last r)))

theorem decompU (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T'))
    (u : V) (hu : u ∈ Submodule.span E (Set.range (Sum.elim f f'))) (hX : u ∈ H.perp (H.X f)) :
    u - (alU H f f' T u • f (Fin.last r) + (H.h u (f (Fin.last r)) + algebraMap F E T * alU H f f' T u) •
      omP H f f') ∈ H.X f := by
  have hX' := (mem_perpX_iff H f u).1 hX
  apply mem_X_ofU H f f' T T' hF hF' hD hG
  · refine Submodule.sub_mem _ hu (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ (omP_mem_span H f f')))
    exact Submodule.subset_span ⟨Sum.inl _, rfl⟩
  · intro a
    rw [h_sub_left H, H.h_add_left, H.h_smul_left, H.h_smul_left, h_frame H f T hF,
      h_omP_f H f f' hD]
    by_cases ha : a = Fin.last r
    · subst ha
      simp only [and_self, ite_true]
      ring
    · obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 ha
      simp [ha, hX' a']
  · have hη : (1 + algebraMap F E T * nuU H f f') * Ring.inverse (1 + algebraMap F E T * nuU H f f') = 1 :=
      Ring.mul_inverse_cancel _ (eta_unit H f f' T T' hF' hD hG)
    have e1 : H.h (u - (alU H f f' T u • f (Fin.last r) + (H.h u (f (Fin.last r)) +
        algebraMap F E T * alU H f f' T u) • omP H f f')) (omP H f f') = 0 := by
      rw [h_sub_left H, H.h_add_left, H.h_smul_left, H.h_smul_left, h_z_omP H f f' hD]
      rw [show H.h (omP H f f') (omP H f f') = nuU H f f' from rfl, alU]
      linear_combination (-(H.h u (omP H f f') - nuU H f f' * H.h u (f (Fin.last r)))) * hη
    have e2 : H.h (u - (alU H f f' T u • f (Fin.last r) + (H.h u (f (Fin.last r)) +
        algebraMap F E T * alU H f f' T u) • omP H f f')) (H.om' f f') = 0 := by
      rw [omP, h_smul_right] at e1
      have hu' : IsUnit (M.L.cj (Ring.inverse (H.Dl f f' (r + 1)))) :=
        (IsUnit.map M.L.cj (⟨⟨Ring.inverse (H.Dl f f' (r + 1)), H.Dl f f' (r + 1), Ring.inverse_mul_cancel _ hD,
          Ring.mul_inverse_cancel _ hD⟩, rfl⟩ :
          IsUnit (Ring.inverse (H.Dl f f' (r + 1)))))
      exact hu'.mul_right_eq_zero.1 e1
    rw [H.h_herm, e2, map_zero]

theorem mkW_decompU (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T'))
    (u : ↥(H.perp (H.X f))) (hu : (u : V) ∈ Submodule.span E (Set.range (Sum.elim f f'))) :
    H.mkW f u = alU H f f' T u • H.mkW f ⟨f (Fin.last r), z_mem H f T hF⟩ +
      (H.h u (f (Fin.last r)) + algebraMap F E T * alU H f f' T u) •
        H.mkW f ⟨omP H f f', omP_mem H f f' hD⟩ := by
  have hd := decompU H f f' T T' hF hF' hD hG u hu u.2
  unfold HermSp.mkW
  rw [← map_smul, ← map_smul, ← map_add (f := _), Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
    Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul]
  exact hd

theorem mkW_decompU' (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T'))
    (u : ↥(H.perp (H.X f'))) (hu : (u : V) ∈ Submodule.span E (Set.range (Sum.elim f f'))) :
    H.mkW f' u = alU H f' f T' u • H.mkW f' ⟨f' (Fin.last r), z_mem H f' T' hF'⟩ +
      (H.h u (f' (Fin.last r)) + algebraMap F E T' * alU H f' f T' u) •
        H.mkW f' ⟨omP H f' f, omP_mem H f' f (unit_swap H f f' hD)⟩ := by
  have hG' : IsUnit (H.Gdet f' f T' T) := by
    have he : H.Gdet f' f T' T = H.Gdet f f' T T' := by
      unfold HermSp.Gdet HermSp.normE
      rw [dl_swap_full H f f', dl_swap_r H f f', M.L.cj_cj, M.L.cj_cj, mul_comm T' T]
      ring
    rw [he]
    exact hG
  have hu' : (u : V) ∈ Submodule.span E (Set.range (Sum.elim f' f)) := by
    rw [Set.Sum.elim_range, Set.union_comm, ← Set.Sum.elim_range]
    exact hu
  exact mkW_decompU H f' f T' T hF' hF (unit_swap H f f' hD) hG' u hu'

def GoodU {r : ℕ} (t : Term V M r) : Prop :=
  M.split = none ∧ Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T ∧ Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T' ∧
    IsUnit (H.Dl t.f t.f' (r + 1)) ∧ IsUnit (H.Gdet t.f t.f' t.T t.T')

private theorem MMfam_eq_sum_elim_of_goodU {t : Term V M r} (hg : GoodU H t) : H.MMfam t = Sum.elim t.f t.f' := by
  unfold HermSp.MMfam
  rw [hg.1]

theorem gramH_eqU {r : ℕ} {t : Term V M r} (hg : GoodU H t) :
    gramH H (H.MMfam t) = gramC (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') := by
  rw [MMfam_eq_sum_elim_of_goodU H hg]
  obtain ⟨-, ⟨h0, hT⟩, ⟨h0', hT'⟩, -, -⟩ := hg
  ext i j
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [gramC, gramH, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.transpose_apply, HermSp.Zhat]
  · split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact hT
    · exact h0 a b (not_and_or.mp h)
  · first
      | exact H.h_herm _ _
  · split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact hT'
    · exact h0' a b (not_and_or.mp h)

theorem unit_gramHU {r : ℕ} {t : Term V M r} (hg : GoodU H t) :
    IsUnit (gramH H (H.MMfam t)).det := by
  rw [gramH_eqU H hg]
  exact unit_gramC_of H t.f t.f' t.T t.T' hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2

theorem relSub_eqU {r : ℕ} {t : Term V M r} (hg : GoodU H t) :
    relSub H t = relC M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') := by
  ext y
  simp only [relSub, relC, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq]
  rw [← gramH_eqU H hg]
  rfl

def PsiU {r : ℕ} {t : Term V M r} (hg : GoodU H t) :
    DDt H t ≃ₗ[M.L.O] DDc M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') :=
  (ddEquiv H t (unit_gramHU H hg)).trans (Submodule.quotEquivOfEq _ _ (relSub_eqU H hg))

theorem PsiU_mk {r : ℕ} {t : Term V M r} (hg : GoodU H t) (u : ↥(MMsharp H t)) :
    PsiU H hg (ddMk H t u) = Submodule.Quotient.mk (sharpEquiv H t (unit_gramHU H hg) u) := rfl

theorem h_eq_formCU {r : ℕ} {t : Term V M r} (hg : GoodU H t) (u w : ↥(MMsharp H t)) :
    H.h u w = formC M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') (sharpEquiv H t (unit_gramHU H hg) u)
      (sharpEquiv H t (unit_gramHU H hg) w) := by
  rw [h_eq_form H (H.MMfam t) (unit_gramHU H hg) (u : V) (w : V) ((mem_MMsharp_iff H t u).1 u.2).1,
    gramH_eqU H hg]
  simp only [formC, sharpEquiv_apply]
  rfl

def PcU {t : Term V M r} (hg : GoodU H t) : H.Wb t.f →ₗ[E] E × E :=
  coordW H t.f (t.f (Fin.last r)) (omP H t.f t.f') (z_mem H t.f t.T hg.2.1)
    (omP_mem H t.f t.f' hg.2.2.2.1)

def PcU' {t : Term V M r} (hg : GoodU H t) : H.Wb t.f' →ₗ[E] E × E :=
  coordW H t.f' (omP H t.f' t.f) (t.f' (Fin.last r))
    (omP_mem H t.f' t.f (unit_swap H t.f t.f' hg.2.2.2.1)) (z_mem H t.f' t.T' hg.2.2.1)

theorem sharp_inlU {t : Term V M r} (hg : GoodU H t) (u : ↥(MMsharp H t)) (a : Fin (r + 1)) :
    (sharpEquiv H t (unit_gramHU H hg) u (Sum.inl a) : E) = H.h u (t.f a) := by
  rw [sharpEquiv_apply, MMfam_eq_sum_elim_of_goodU H hg, Sum.elim_inl]

theorem sharp_inrU {t : Term V M r} (hg : GoodU H t) (u : ↥(MMsharp H t)) (b : Fin (r + 1)) :
    (sharpEquiv H t (unit_gramHU H hg) u (Sum.inr b) : E) = H.h u (t.f' b) := by
  rw [sharpEquiv_apply, MMfam_eq_sum_elim_of_goodU H hg, Sum.elim_inr]

theorem mem_span_of_sharpU {t : Term V M r} (hg : GoodU H t) (u : ↥(MMsharp H t)) :
    (u : V) ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  have hs := ((mem_MMsharp_iff H t u).1 u.2).1
  rwa [MMfam_eq_sum_elim_of_goodU H hg] at hs

theorem gam_imageU {t : Term V M r} (hg : GoodU H t) :
    (fun p => (PsiU H hg p.1, PcU H hg p.2)) '' Gam H t =
      GamC M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T) (algebraMap F E t.T') := by
  ext ⟨d, c⟩
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, he⟩
    refine ⟨sharpEquiv H t (unit_gramHU H hg) u, fun a => ?_, ?_⟩
    · apply Subtype.ext
      rw [sharp_inlU H hg]
      exact (mem_perpX_iff H t.f u).1 hu a
    · rw [← he]
      beta_reduce
      rw [PsiU_mk]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · show H.h u (t.f (Fin.last r)) = _
        rw [sharp_inlU H hg]
      · show H.h u (omP H t.f t.f') = _
        rw [h_omP, lamStarC]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [sharp_inrU H hg]
        rfl
  · rintro ⟨Y, hY, he⟩
    set u := (sharpEquiv H t (unit_gramHU H hg)).symm Y with hu
    have hYu : sharpEquiv H t (unit_gramHU H hg) u = Y := by rw [hu, LinearEquiv.apply_symm_apply]
    have hX : (u : V) ∈ H.perp (H.X t.f) := by
      rw [mem_perpX_iff]
      intro a
      rw [← sharp_inlU H hg, hYu, hY a]
      rfl
    refine ⟨(ddMk H t u, H.mkW t.f ⟨u, hX⟩), ⟨u, hX, rfl⟩, ?_⟩
    rw [he]
    beta_reduce
    rw [PsiU_mk, hYu]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · show H.h u (t.f (Fin.last r)) = _
      rw [← sharp_inlU H hg, hYu]
    · show H.h u (omP H t.f t.f') = _
      rw [h_omP, lamStarC]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← sharp_inrU H hg u, hYu]
      rfl

theorem gam_imageU' {t : Term V M r} (hg : GoodU H t) :
    (fun p => (PsiU H hg p.1, PcU' H hg p.2)) '' Gam' H t =
      GamC' M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T) (algebraMap F E t.T') := by
  ext ⟨d, c⟩
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, he⟩
    refine ⟨sharpEquiv H t (unit_gramHU H hg) u, fun a => ?_, ?_⟩
    · apply Subtype.ext
      rw [sharp_inrU H hg]
      exact (mem_perpX_iff H t.f' u).1 hu a
    · rw [← he]
      beta_reduce
      rw [PsiU_mk]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · show H.h u (omP H t.f' t.f) = _
        rw [h_omP_swap H t.f t.f' hg.2.2.2.1, lamC, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sharp_inlU H hg]
      · show H.h u (t.f' (Fin.last r)) = _
        rw [sharp_inrU H hg]
  · rintro ⟨Y, hY, he⟩
    set u := (sharpEquiv H t (unit_gramHU H hg)).symm Y with hu
    have hYu : sharpEquiv H t (unit_gramHU H hg) u = Y := by rw [hu, LinearEquiv.apply_symm_apply]
    have hX : (u : V) ∈ H.perp (H.X t.f') := by
      rw [mem_perpX_iff]
      intro a
      rw [← sharp_inrU H hg, hYu, hY a]
      rfl
    refine ⟨(ddMk H t u, H.mkW t.f' ⟨u, hX⟩), ⟨u, hX, rfl⟩, ?_⟩
    rw [he]
    beta_reduce
    rw [PsiU_mk, hYu]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · show H.h u (omP H t.f' t.f) = _
      rw [h_omP_swap H t.f t.f' hg.2.2.2.1, lamC, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← sharp_inlU H hg u, hYu]
    · show H.h u (t.f' (Fin.last r)) = _
      rw [← sharp_inrU H hg, hYu]

theorem gam_sepU {t₁ t₂ : Term V M r} (hg₁ : GoodU H t₁) (hg₂ : GoodU H t₂) (hT : t₂.T = t₁.T)
    (hν : nuU H t₂.f t₂.f' = nuU H t₁.f t₁.f')
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (hz : φ (H.mkW t₁.f ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩) = H.mkW t₂.f ⟨_, z_mem H t₂.f t₂.T hg₂.2.1⟩)
    (ho : φ (H.mkW t₁.f ⟨_, omP_mem H t₁.f t₁.f' hg₁.2.2.2.1⟩) =
      H.mkW t₂.f ⟨_, omP_mem H t₂.f t₂.f' hg₂.2.2.2.1⟩) :
    ∀ p ∈ Gam H t₁, ∀ q ∈ Gam H t₂, PcU H hg₂ q.2 = PcU H hg₁ p.2 → q.2 = φ p.2 := by
  intro p hp q hq hc
  obtain ⟨u, hu, rfl⟩ := hp
  obtain ⟨w, hw, rfl⟩ := hq
  have e1 : H.h (w : V) (t₂.f (Fin.last r)) = H.h (u : V) (t₁.f (Fin.last r)) := congrArg Prod.fst hc
  have e2 : H.h (w : V) (omP H t₂.f t₂.f') = H.h (u : V) (omP H t₁.f t₁.f') := congrArg Prod.snd hc
  have hα : alU H t₂.f t₂.f' t₂.T (w : V) = alU H t₁.f t₁.f' t₁.T (u : V) := by
    unfold alU
    rw [hT, hν, e1, e2]
  have hβ : H.h (w : V) (t₂.f (Fin.last r)) + algebraMap F E t₂.T * alU H t₂.f t₂.f' t₂.T (w : V) =
      H.h (u : V) (t₁.f (Fin.last r)) + algebraMap F E t₁.T * alU H t₁.f t₁.f' t₁.T (u : V) := by
    rw [e1, hα, hT]
  show H.mkW t₂.f ⟨w, hw⟩ = φ (H.mkW t₁.f ⟨u, hu⟩)
  rw [mkW_decompU H t₂.f t₂.f' t₂.T t₂.T' hg₂.2.1 hg₂.2.2.1 hg₂.2.2.2.1 hg₂.2.2.2.2 ⟨w, hw⟩
      (mem_span_of_sharpU H hg₂ w),
    mkW_decompU H t₁.f t₁.f' t₁.T t₁.T' hg₁.2.1 hg₁.2.2.1 hg₁.2.2.2.1 hg₁.2.2.2.2 ⟨u, hu⟩
      (mem_span_of_sharpU H hg₁ u),
    map_add, map_smul, map_smul, hz, ho, hβ, hα]

theorem gam_sepU' {t₁ t₂ : Term V M r} (hg₁ : GoodU H t₁) (hg₂ : GoodU H t₂) (hT : t₂.T' = t₁.T')
    (hν : nuU H t₂.f' t₂.f = nuU H t₁.f' t₁.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f')
    (hz : φ' (H.mkW t₁.f' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩) =
      H.mkW t₂.f' ⟨_, z_mem H t₂.f' t₂.T' hg₂.2.2.1⟩)
    (ho : φ' (H.mkW t₁.f' ⟨_, omP_mem H t₁.f' t₁.f (unit_swap H t₁.f t₁.f' hg₁.2.2.2.1)⟩) =
      H.mkW t₂.f' ⟨_, omP_mem H t₂.f' t₂.f (unit_swap H t₂.f t₂.f' hg₂.2.2.2.1)⟩) :
    ∀ p ∈ Gam' H t₁, ∀ q ∈ Gam' H t₂, PcU' H hg₂ q.2 = PcU' H hg₁ p.2 → q.2 = φ' p.2 := by
  intro p hp q hq hc
  obtain ⟨u, hu, rfl⟩ := hp
  obtain ⟨w, hw, rfl⟩ := hq
  have e1 : H.h (w : V) (omP H t₂.f' t₂.f) = H.h (u : V) (omP H t₁.f' t₁.f) := congrArg Prod.fst hc
  have e2 : H.h (w : V) (t₂.f' (Fin.last r)) = H.h (u : V) (t₁.f' (Fin.last r)) := congrArg Prod.snd hc
  have hα : alU H t₂.f' t₂.f t₂.T' (w : V) = alU H t₁.f' t₁.f t₁.T' (u : V) := by
    unfold alU
    rw [hT, hν, e1, e2]
  have hβ : H.h (w : V) (t₂.f' (Fin.last r)) + algebraMap F E t₂.T' * alU H t₂.f' t₂.f t₂.T' (w : V) =
      H.h (u : V) (t₁.f' (Fin.last r)) + algebraMap F E t₁.T' * alU H t₁.f' t₁.f t₁.T' (u : V) := by
    rw [e2, hα, hT]
  show H.mkW t₂.f' ⟨w, hw⟩ = φ' (H.mkW t₁.f' ⟨u, hu⟩)
  rw [mkW_decompU' H t₂.f t₂.f' t₂.T t₂.T' hg₂.2.1 hg₂.2.2.1 hg₂.2.2.2.1 hg₂.2.2.2.2 ⟨w, hw⟩
      (mem_span_of_sharpU H hg₂ w),
    mkW_decompU' H t₁.f t₁.f' t₁.T t₁.T' hg₁.2.1 hg₁.2.2.1 hg₁.2.2.2.1 hg₁.2.2.2.2 ⟨u, hu⟩
      (mem_span_of_sharpU H hg₁ u),
    map_add, map_smul, map_smul, hz, ho, hβ, hα]

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

section Parts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem mmInt_U {t : Term V M r} (hg : GoodU H t) (hT : t.T ∈ 𝒪[F]) (hT' : t.T' ∈ 𝒪[F])
    (hint : ∀ a b, H.Zhat t.f t.f' a b ∈ M.L.O) : MMInt H t := by
  have hTO : algebraMap F E t.T ∈ M.L.O := Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨t.T, hT⟩
  have hTO' : algebraMap F E t.T' ∈ M.L.O := Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨t.T', hT'⟩
  have hgen : ∀ i j, H.h (H.MMfam t i) (H.MMfam t j) ∈ M.L.O := by
    intro i j
    have e := congrFun (congrFun (gramH_eqU H hg) i) j
    simp only [gramH, Matrix.of_apply] at e
    rw [e]
    rcases i with a | a <;> rcases j with b | b
    · simp only [gramC, Matrix.fromBlocks_apply₁₁, Matrix.of_apply]
      split_ifs
      · exact neg_mem hTO
      · exact zero_mem _
    · simp only [gramC, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
      exact cj_mem_O M.L (hint a b)
    · simp only [gramC, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply]
      exact hint b a
    · simp only [gramC, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
      split_ifs
      · exact neg_mem hTO'
      · exact zero_mem _
  have hzero : ∀ y : V, H.h 0 y = 0 := by
    intro y
    have h0 := H.h_smul_left 0 0 y
    rwa [zero_smul, zero_mul] at h0
  have h1 : ∀ i, ∀ m ∈ MMo H t, H.h m (H.MMfam t i) ∈ M.L.O := by
    intro i m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hgen j i
    | zero => rw [hzero]; exact zero_mem _
    | add x y _ _ hx hy => rw [H.h_add_left]; exact add_mem hx hy
    | smul c x _ hx => rw [Subring.smul_def, H.h_smul_left]; exact mul_mem c.2 hx
  intro m hm m' hm'
  have h2 : ∀ i, H.h (H.MMfam t i) m' ∈ M.L.O := by
    intro i
    rw [H.h_herm]
    exact cj_mem_O M.L (h1 i m' hm')
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact h2 j
  | zero => rw [hzero]; exact zero_mem _
  | add x y _ _ hx hy => rw [H.h_add_left]; exact add_mem hx hy
  | smul c x _ hx => rw [Subring.smul_def, H.h_smul_left]; exact mul_mem c.2 hx

theorem PsiU_symm_mk {t : Term V M r} (hg : GoodU H t) (Y : Ix r → M.L.O) :
    (PsiU H hg).symm (Submodule.Quotient.mk Y) =
      ddMk H t ((sharpEquiv H t (unit_gramHU H hg)).symm Y) := by
  rw [LinearEquiv.symm_apply_eq, PsiU_mk, LinearEquiv.apply_symm_apply]

theorem isomD_iffU {t₁ t₂ : Term V M r} (hg₁ : GoodU H t₁) (hg₂ : GoodU H t₂)
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) :
    IsomD H t₁ t₂ θ ↔ ∀ Y W Y₂ W₂ : Ix r → M.L.O,
      PsiU H hg₂ (θ ((PsiU H hg₁).symm (Submodule.Quotient.mk Y))) = Submodule.Quotient.mk Y₂ →
      PsiU H hg₂ (θ ((PsiU H hg₁).symm (Submodule.Quotient.mk W))) = Submodule.Quotient.mk W₂ →
      formC M.L.O (M.L.cj : E →+* E) (H.Zhat t₂.f t₂.f') (algebraMap F E t₂.T) (algebraMap F E t₂.T')
          Y₂ W₂ -
        formC M.L.O (M.L.cj : E →+* E) (H.Zhat t₁.f t₁.f') (algebraMap F E t₁.T)
          (algebraMap F E t₁.T') Y W ∈ M.L.O := by
  unfold IsomD
  constructor
  · intro h Y W Y₂ W₂ hY hW
    rw [PsiU_symm_mk H hg₁, ← LinearEquiv.eq_symm_apply, PsiU_symm_mk H hg₂] at hY hW
    have key := h _ _ _ _ hY hW
    rw [h_eq_formCU H hg₂, h_eq_formCU H hg₁] at key
    simpa only [LinearEquiv.apply_symm_apply] using key
  · intro h x y x₂ y₂ hx hy
    have hx' : PsiU H hg₂ (θ ((PsiU H hg₁).symm
        (Submodule.Quotient.mk (sharpEquiv H t₁ (unit_gramHU H hg₁) x)))) =
        Submodule.Quotient.mk (sharpEquiv H t₂ (unit_gramHU H hg₂) x₂) := by
      rw [PsiU_symm_mk H hg₁, LinearEquiv.symm_apply_apply, hx, PsiU_mk]
    have hy' : PsiU H hg₂ (θ ((PsiU H hg₁).symm
        (Submodule.Quotient.mk (sharpEquiv H t₁ (unit_gramHU H hg₁) y)))) =
        Submodule.Quotient.mk (sharpEquiv H t₂ (unit_gramHU H hg₂) y₂) := by
      rw [PsiU_symm_mk H hg₁, LinearEquiv.symm_apply_apply, hy, PsiU_mk]
    rw [h_eq_formCU H hg₂, h_eq_formCU H hg₁]
    exact h _ _ _ _ hx' hy'

theorem kap_eq (f₁ f₁' f₂ f₂' : Fin (r + 1) → V) (hD₁ : IsUnit (H.Dl f₁ f₁' (r + 1)))
    (hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)))
    (hrel : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    kapU H f₂ f₂' = kapU H f₁ f₁' := by
  obtain ⟨u₁, hu₁⟩ := hD₁
  obtain ⟨u₂, hu₂⟩ := hD₂
  simp only [kapU]
  rw [← hu₁, ← hu₂] at hrel ⊢
  rw [Ring.inverse_unit, Ring.inverse_unit, Units.inv_mul_eq_iff_eq_mul, mul_left_comm,
    Units.eq_inv_mul_iff_mul_eq]
  linear_combination -hrel

private theorem Dl_swap_eq_cj_Dl (f f' : Fin (r + 1) → V) (l : ℕ) :
    H.Dl f' f l = M.L.cj (H.Dl f f' l) := by
  unfold HermSp.Dl
  split_ifs with hl
  · rw [AlgEquiv.map_det, ← Matrix.det_transpose]
    congr 1
    ext a b
    simp only [HermSp.Zhat, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply,
      AlgEquiv.mapMatrix_apply, Matrix.map_apply]
    exact H.h_herm _ _
  · simp

theorem rel_swap (f₁ f₁' f₂ f₂' : Fin (r + 1) → V)
    (hrel : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    H.Dl f₁' f₁ r * H.Dl f₂' f₂ (r + 1) = H.Dl f₂' f₂ r * H.Dl f₁' f₁ (r + 1) := by
  rw [Dl_swap_eq_cj_Dl H f₁, Dl_swap_eq_cj_Dl H f₂, Dl_swap_eq_cj_Dl H f₂, Dl_swap_eq_cj_Dl H f₁, ← map_mul, ← map_mul,
    hrel]

end Parts

private theorem image_prod_map_eq_iff_image_transport_eq {A₁ A₂ B₁ B₂ C₁ C₂ D : Type*} (G₁ : Set (A₁ × B₁)) (G₂ : Set (A₂ × B₂))
    (Ψ₁ : A₁ → C₁) (Ψ₁' : C₁ → A₁) (hΨ₁ : ∀ a, Ψ₁' (Ψ₁ a) = a) (Ψ₂ : A₂ → C₂)
    (hΨ₂ : Function.Injective Ψ₂) (P₁ : B₁ → D) (P₂ : B₂ → D) (θ : A₁ → A₂) (φ : B₁ → B₂)
    (hP : ∀ b, P₂ (φ b) = P₁ b)
    (sep : ∀ p ∈ G₁, ∀ q ∈ G₂, P₂ q.2 = P₁ p.2 → q.2 = φ p.2) :
    (fun p : A₁ × B₁ => (θ p.1, φ p.2)) '' G₁ = G₂ ↔
      (fun p : C₁ × D => (Ψ₂ (θ (Ψ₁' p.1)), p.2)) '' ((fun p : A₁ × B₁ => (Ψ₁ p.1, P₁ p.2)) '' G₁) =
        (fun p : A₂ × B₂ => (Ψ₂ p.1, P₂ p.2)) '' G₂ := by
  rw [Set.image_image]
  simp only [hΨ₁]
  constructor
  · intro h
    rw [← h, Set.image_image]
    simp only [hP]
  · intro h
    ext ⟨x, y⟩
    constructor
    · rintro ⟨p, hp, hpq⟩
      have hm : (Ψ₂ (θ p.1), P₁ p.2) ∈ (fun p : A₂ × B₂ => (Ψ₂ p.1, P₂ p.2)) '' G₂ := by
        rw [← h]
        exact ⟨p, hp, rfl⟩
      obtain ⟨q, hq, hqe⟩ := hm
      simp only [Prod.mk.injEq] at hqe hpq
      have h1 := hΨ₂ hqe.1
      have h2 := sep p hp q hq hqe.2
      rw [← hpq.1, ← hpq.2, ← h1, ← h2]
      exact hq
    · intro hq
      have hm : (Ψ₂ x, P₂ y) ∈ (fun p : A₁ × B₁ => (Ψ₂ (θ p.1), P₁ p.2)) '' G₁ := by
        rw [h]
        exact ⟨(x, y), hq, rfl⟩
      obtain ⟨p, hp, hpe⟩ := hm
      simp only [Prod.mk.injEq] at hpe
      have h1 := hΨ₂ hpe.1
      have h2 := sep p hp (x, y) hq hpe.2.symm
      refine ⟨p, hp, ?_⟩
      simp only [Prod.mk.injEq]
      exact ⟨h1, h2.symm⟩

theorem coordU_holds : CoordU := by
  intro F _ _ _ E _ _ _ _ M hsplit r n V _ _ H _ t₁ f₂ f₂' φ φ' hyp hD₂ hZ
  obtain ⟨⟨⟨_, hF₁, hF₁', hD₁, hG₁, _⟩, _⟩, hK₂, hK₂', hId, hS, hS'⟩ := hyp
  obtain ⟨hiso, hiso', _, hom', hom, hrel⟩ := hId
  set t₂ : Term V M r := { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } with ht₂
  have hK₁ : MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hF₁.2.1, hF₁.2.2.1⟩
  have hK₁' : MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hF₁'.2.1, hF₁'.2.2.1⟩
  have hT : t₁.T ∈ 𝒪[F] := hF₁.2.2.2.1
  have hT' : t₁.T' ∈ 𝒪[F] := hF₁'.2.2.2.1
  have hG₁u := Formalism.L2.SG.LsDatumA.isUnit_Gdet H _ _ _ _ hG₁
  have hN₁ : IsUnit (H.normE (H.Dl t₁.f t₁.f' (r + 1))) := hD₁.mul (hD₁.map M.L.cj)
  have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
  have e := gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hrel
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have hm : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁u
    exact isUnit_of_mul_isUnit_left hm
  have hg₁ : GoodU H t₁ := ⟨hsplit, hK₁, hK₁', hD₁, hG₁u⟩
  have hg₂ : GoodU H t₂ := ⟨hsplit, hK₂, hK₂', hD₂, hG₂⟩
  have hint₂ : MMInt H t₂ := mmInt_U H hg₂ hT hT' hZ
  have hD₁s : IsUnit (H.Dl t₁.f' t₁.f (r + 1)) := by
    rw [Dl_swap_eq_cj_Dl]
    exact hD₁.map _
  have hD₂s : IsUnit (H.Dl f₂' f₂ (r + 1)) := by
    rw [Dl_swap_eq_cj_Dl]
    exact hD₂.map _
  have hnu : nuU H t₂.f t₂.f' = nuU H t₁.f t₁.f' := by
    show nuU H f₂ f₂' = nuU H t₁.f t₁.f'
    unfold nuU
    rw [h_omP_omPU H f₂ f₂' t₁.T' hK₂', h_omP_omPU H t₁.f t₁.f' t₁.T' hK₁',
      kap_eq H t₁.f t₁.f' f₂ f₂' hD₁ hD₂ hrel]
  have hnu' : nuU H t₂.f' t₂.f = nuU H t₁.f' t₁.f := by
    show nuU H f₂' f₂ = nuU H t₁.f' t₁.f
    unfold nuU
    rw [h_omP_omPU H f₂' f₂ t₁.T hK₂, h_omP_omPU H t₁.f' t₁.f t₁.T hK₁,
      kap_eq H t₁.f' t₁.f f₂' f₂ hD₁s hD₂s (rel_swap H _ _ _ _ hrel)]
  have sends1 : ∀ {g₁ g₂ : Fin (r + 1) → V} (ψ : H.Wb g₁ →ₗ[E] H.Wb g₂) (v₁ v₂ : V)
      (h₁ : v₁ ∈ H.perp (H.X g₁)) (h₂ : v₂ ∈ H.perp (H.X g₂)), H.SendsTo ψ 1 1 v₁ v₂ →
      ψ (H.mkW g₁ ⟨v₁, h₁⟩) = H.mkW g₂ ⟨v₂, h₂⟩ := by
    intro g₁ g₂ ψ v₁ v₂ h₁ h₂ hs
    simpa only [one_smul] using hs ⟨v₁, h₁⟩ ⟨v₂, h₂⟩ rfl rfl
  have hc : ∀ w, PcU H hg₂ (φ w) = PcU H hg₁ w := by
    intro w
    unfold PcU
    refine coordW_comp H φ hiso _ _ _ _ _ _ _ _ ?_ ?_ w
    · exact sends1 _ _ _ _ _ hS
    · exact sends_omP H φ hD₁ hD₂ hom'
  have hc' : ∀ w, PcU' H hg₂ (φ' w) = PcU' H hg₁ w := by
    intro w
    unfold PcU'
    refine coordW_comp H φ' hiso' _ _ _ _ _ _ _ _ ?_ ?_ w
    · exact sends_omP' H φ' hD₁ hD₂ hom
    · exact sends1 _ _ _ _ _ hS'
  have sep := gam_sepU H hg₁ hg₂ rfl hnu φ (sends1 _ _ _ _ _ hS) (sends_omP H φ hD₁ hD₂ hom')
  have sep' := gam_sepU' H hg₁ hg₂ rfl hnu' φ' (sends1 _ _ _ _ _ hS') (sends_omP' H φ' hD₁ hD₂ hom)
  let eqv : (DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) ≃
      (DDc M.L.O (M.L.cj : E →+* E) (H.Zhat t₁.f t₁.f') (algebraMap F E t₁.T) (algebraMap F E t₁.T') ≃ₗ[M.L.O]
        DDc M.L.O (M.L.cj : E →+* E) (H.Zhat f₂ f₂') (algebraMap F E t₁.T) (algebraMap F E t₁.T')) :=
    { toFun := fun θ => ((PsiU H hg₁).symm.trans θ).trans (PsiU H hg₂)
      invFun := fun ψ => ((PsiU H hg₁).trans ψ).trans (PsiU H hg₂).symm
      left_inv := fun θ => by
        ext x
        simp
      right_inv := fun ψ => by
        ext x
        simp }
  refine Nat.card_congr (Equiv.subtypeEquiv eqv ?_)
  intro θ
  simp only [Theta, ThetaC, Set.mem_ofPred_eq]
  rw [isomD_iffU H hg₁ hg₂ θ]
  have key := image_prod_map_eq_iff_image_transport_eq (Gam H t₁) (Gam H t₂) (PsiU H hg₁) (PsiU H hg₁).symm
    (PsiU H hg₁).symm_apply_apply (PsiU H hg₂) (PsiU H hg₂).injective (PcU H hg₁) (PcU H hg₂) θ φ
    hc sep
  have key' := image_prod_map_eq_iff_image_transport_eq (Gam' H t₁) (Gam' H t₂) (PsiU H hg₁) (PsiU H hg₁).symm
    (PsiU H hg₁).symm_apply_apply (PsiU H hg₂) (PsiU H hg₂).injective (PcU' H hg₁) (PcU' H hg₂) θ φ'
    hc' sep'
  constructor
  · rintro ⟨_, _, hI, hGm, _⟩
    obtain ⟨hA, hB⟩ := hGm hsplit
    refine ⟨hI, ?_, ?_⟩
    · rw [← gam_imageU H hg₁]
      refine Eq.trans ?_ (gam_imageU H hg₂)
      exact key.1 hA
    · rw [← gam_imageU' H hg₁]
      refine Eq.trans ?_ (gam_imageU' H hg₂)
      exact key'.1 hB
  · rintro ⟨hI, hA, hB⟩
    refine ⟨hD₂, hint₂, hI, fun _ => ⟨?_, ?_⟩, fun g hg => ?_⟩
    · refine key.2 ?_
      rw [gam_imageU H hg₁]
      exact hA.trans (gam_imageU H hg₂).symm
    · refine key'.2 ?_
      rw [gam_imageU' H hg₁]
      exact hB.trans (gam_imageU' H hg₂).symm
    · rw [hsplit] at hg
      cases hg

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

private theorem exists_cj_combination_of_isUnit_det (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu : IsUnit (Z.map O.subtype).det) (y' : Fin (r + 1) → O) :
    ∃ w : Fin (r + 1) → E, ∀ b, (y' b : E) = ∑ a, cj (Z.map O.subtype a b) * w a := by
  set N : Matrix (Fin (r + 1)) (Fin (r + 1)) E := (Z.map O.subtype).transpose.map cj with hN
  have hdet : IsUnit N.det := by
    have h1 : N.det = cj (Z.map O.subtype).det := by
      rw [hN, ← Matrix.det_transpose (Z.map O.subtype)]
      exact (RingHom.map_det cj _).symm
    rw [h1]
    exact hu.map cj
  refine ⟨N⁻¹.mulVec (fun j => (y' j : E)), fun b => ?_⟩
  have h2 : N.mulVec (N⁻¹.mulVec (fun j => (y' j : E))) = fun j => (y' j : E) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hdet, Matrix.one_mulVec]
  have h3 := congrFun h2 b
  rw [← h3]
  simp [Matrix.mulVec, dotProduct, hN]

theorem pair_eG (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O)
    {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ : kap O Z₂ = kap O Z₁) (p : PairSet O cj hO Z₁ Z₂) :
    p.1.2 (eCl (cjT O cj hO Z₁)) = eCl (cjT O cj hO Z₂) := by
  obtain ⟨y₂', hy₂'⟩ := Submodule.Quotient.mk_surjective _ (p.1.2 (eCl (cjT O cj hO Z₁)))
  have hlam : lamS O cj Z₂ y₂' = lamS O cj Z₁ (Pi.single (Fin.last r) 1) :=
    p.2.2.1 (Pi.single (Fin.last r) 1) y₂' hy₂'.symm
  set d : Fin (r + 1) → O := y₂' - Pi.single (Fin.last r) 1 with hd
  obtain ⟨w, hw⟩ := exists_cj_combination_of_isUnit_det O cj Z₂ hu₂ d
  have hlast : w (Fin.last r) = 0 := by
    rw [← lamS_cjT O cj Z₂ hu₂ d w hw, hd, lamS_sub, hlam, lamS_e', lamS_e', hκ, sub_self]
  have hmem : ∀ a, w a ∈ O := by
    intro a
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
      (p.1.1.symm (Submodule.Quotient.mk (Pi.single a 1)))
    have h1 : p.1.1 (Submodule.Quotient.mk c) = Submodule.Quotient.mk (Pi.single a 1) := by
      rw [hc]
      simp
    have hB := p.2.2.2 c (Pi.single (Fin.last r) 1) (Pi.single a 1) y₂' h1 hy₂'.symm
    have hL := lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 c (Pi.single a 1) h1
    have hsplit : y₂' = d + Pi.single (Fin.last r) 1 := by
      rw [hd]
      abel
    rw [hsplit, bRaw_add_right, bRaw_e, bRaw_e, hL, add_sub_cancel_right,
      bRaw_cjT O cj hcj Z₂ hu₂ _ d w hw] at hB
    have hs : (∑ b : Fin (r + 1), cj (w b) * ((Pi.single a (1 : O) : Fin (r + 1) → O) b : E)) = cj (w a) := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ a) h
    rw [hs] at hB
    have := hO _ hB
    rwa [hcj] at this
  have hdmem : d ∈ headCols (cjT O cj hO Z₂) := by
    rw [mem_headCols_iff]
    refine ⟨fun a => ⟨w a, hmem a⟩, Subtype.ext hlast, ?_⟩
    funext b
    apply Subtype.ext
    rw [cjT_mulVec_coe]
    exact hw b
  rw [← hy₂']
  exact (Submodule.Quotient.eq _).2 hdmem

section Bwd

variable (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
  (hcT : cj (t : E) = t) (hcT' : cj (t' : E) = t') {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
  (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
  (hκ : kap O Z₂ = kap O Z₁)
  (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
  (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det)


include hcj hu₁ hu₂ hκ hG₁ hG₂ in
theorem form_diff (p : PairSet O cj hO Z₁ Z₂) (Y Y₂ W W₂ : Ix r → O)
    (hy : p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)) = Submodule.Quotient.mk fun j => Y₂ (Sum.inl j))
    (hy' : p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)) = Submodule.Quotient.mk fun j => Y₂ (Sum.inr j))
    (hw : p.1.1 (Submodule.Quotient.mk fun j => W (Sum.inl j)) = Submodule.Quotient.mk fun j => W₂ (Sum.inl j))
    (hw' : p.1.2 (Submodule.Quotient.mk fun j => W (Sum.inr j)) = Submodule.Quotient.mk fun j => W₂ (Sum.inr j)) :
    formC O cj (Z₂.map O.subtype) t t' Y₂ W₂ - formC O cj (Z₁.map O.subtype) t t' Y W ∈ O := by
  have hl : lamC (Z₂.map O.subtype) (fun j => ((Y₂ (Sum.inl j) : O) : E)) =
      lamC (Z₁.map O.subtype) (fun j => ((Y (Sum.inl j) : O) : E)) :=
    lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 _ _ hy
  have hs : lamStarC cj (Z₂.map O.subtype) (fun j => ((Y₂ (Sum.inr j) : O) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => ((Y (Sum.inr j) : O) : E)) :=
    p.2.2.1 _ _ hy'
  have hlw : lamC (Z₂.map O.subtype) (fun j => ((W₂ (Sum.inl j) : O) : E)) =
      lamC (Z₁.map O.subtype) (fun j => ((W (Sum.inl j) : O) : E)) :=
    lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 _ _ hw
  have hsw : lamStarC cj (Z₂.map O.subtype) (fun j => ((W₂ (Sum.inr j) : O) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => ((W (Sum.inr j) : O) : E)) :=
    p.2.2.1 _ _ hw'
  obtain ⟨hc1, hc2⟩ := cG_transfer O cj hcj Z₁ Z₂ hu₁ hu₂ _ _ hG₁ hG₂ hκ Y Y₂ hl hs
  have hb1 := p.2.2.2 _ _ _ _ hy hw'
  have hb2 := p.2.2.2 _ _ _ _ hw hy'
  rw [formC_eqG O cj hcj Z₂ hu₂ _ _ hG₂, formC_eqG O cj hcj Z₁ hu₁ _ _ hG₁, hc1, hc2, hlw, hsw]
  have key : ∀ a b c d X X' : E,
      (a + cj b + X + X') - (c + cj d + X + X') = (a - c) + cj (b - d) := by
    intro a b c d X X'
    rw [map_sub]
    ring
  rw [key]
  exact add_mem hb1 (hO _ hb2)

end Bwd

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

private theorem bwdEx_lemma {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
    (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O) {Z₁ Z₂ : Matrix (Fin (r+1)) (Fin (r+1)) O}
    (γ : LocCntCommon.MbMod Z₁ ≃ₗ[O] LocCntCommon.MbMod Z₂)
    (γs : LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₁) ≃ₗ[O] LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₂))
    (hb : γ (LocCntCommon.bCls Z₁) = LocCntCommon.bCls Z₂) (he : γ (LocCntCommon.eCl Z₁) = LocCntCommon.eCl Z₂)
    (hbs : γs (LocCntCommon.bCls (LocCnt0LAlg.cjT O cj hO Z₁)) = LocCntCommon.bCls (LocCnt0LAlg.cjT O cj hO Z₂))
    (hes : γs (LocCntCommon.eCl (LocCnt0LAlg.cjT O cj hO Z₁)) = LocCntCommon.eCl (LocCnt0LAlg.cjT O cj hO Z₂))
    (Y : LocCntCommon.Ix r → O) :
    LocCnt0LAlg.thetaOf O cj hO t t' γ γs hb he hbs hes (Submodule.Quotient.mk Y) =
      iL O cj hO Z₂ t t' (γ (Submodule.Quotient.mk fun j => Y (Sum.inl j))) +
        iR O cj hO Z₂ t t' (γs (Submodule.Quotient.mk fun j => Y (Sum.inr j))) := by
  have h1 := LocCnt0LAlg.liftOf_spec O (γ : LocCntCommon.MbMod Z₁ →ₗ[O] LocCntCommon.MbMod Z₂)
    (fun j => Y (Sum.inl j))
  have h2 := LocCnt0LAlg.liftOf_spec O (γs : LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₁) →ₗ[O]
    LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₂)) (fun j => Y (Sum.inr j))
  rw [LinearEquiv.coe_coe] at h1 h2
  rw [← h1, ← h2, ← mk_elim]
  rfl

private theorem linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero {E : Type} [CommRing E] (O : Subring E) {r : ℕ}
    {Z₁ Z₂ : Matrix (Fin (r+1)) (Fin (r+1)) O}
    (γ : LocCntCommon.MbMod Z₁ ≃ₗ[O] LocCntCommon.MbMod Z₂)
    (he : γ (LocCntCommon.eCl Z₁) = LocCntCommon.eCl Z₂) (y : Fin (r+1) → O)
    (hy : ∀ a : Fin r, y a.castSucc = 0) :
    γ (Submodule.Quotient.mk y) = Submodule.Quotient.mk y := by
  have hy' : y = y (Fin.last r) • Pi.single (Fin.last r) (1 : O) := by
    funext j
    refine Fin.lastCases ?_ (fun a => ?_) j
    · simp
    · simp [hy a, Fin.castSucc_ne_last]
  rw [hy', Submodule.Quotient.mk_smul, map_smul]
  unfold LocCntCommon.eCl at he
  rw [he, ← Submodule.Quotient.mk_smul]

theorem bwdEx : BwdEx := by
  intro E _ O cj hcj hO r t t' ht ht' Z₁ Z₂ hZ₁ hZ₂ hk hG₁ hG₂ p
  have hb := p.2.1.1
  have he := p.2.1.2
  have hbs := LocCnt0LAlg.pair_b O cj hcj hO hZ₁ hZ₂ p
  have hes := pair_eG O cj hcj hO hZ₁ hZ₂ hk p
  set θ := LocCnt0LAlg.thetaOf O cj hO t t' p.1.1 p.1.2 hb he hbs hes with hθdef
  have hθ := bwdEx_lemma O cj hO t t' p.1.1 p.1.2 hb he hbs hes
  rw [← hθdef] at hθ
  have hlift : ∀ Y : LocCntCommon.Ix r → O, ∃ Y₃ : LocCntCommon.Ix r → O,
      θ (Submodule.Quotient.mk Y) = Submodule.Quotient.mk Y₃ ∧
      p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)) =
        Submodule.Quotient.mk (fun j => Y₃ (Sum.inl j)) ∧
      p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)) =
        Submodule.Quotient.mk (fun j => Y₃ (Sum.inr j)) := by
    intro Y
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _
      (p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)))
    obtain ⟨b, hb'⟩ := Submodule.Quotient.mk_surjective _
      (p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)))
    refine ⟨Sum.elim a b, ?_, ha.symm, hb'.symm⟩
    rw [hθ, ← ha, ← hb', mk_elim]
  have hsplit : ∀ Y₂ : LocCntCommon.Ix r → O,
      (Submodule.Quotient.mk Y₂ : LocCntCommon.DDc O cj (Z₂.map O.subtype) ↑t ↑t') =
        iL O cj hO Z₂ t t' (Submodule.Quotient.mk fun j => Y₂ (Sum.inl j)) +
          iR O cj hO Z₂ t t' (Submodule.Quotient.mk fun j => Y₂ (Sum.inr j)) := by
    intro Y₂
    rw [← mk_elim]
    congr 1
    funext i
    cases i <;> rfl
  refine ⟨θ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro Y W Y₂ W₂ hY hW
    obtain ⟨Y₃, hY3, hY3l, hY3r⟩ := hlift Y
    obtain ⟨W₃, hW3, hW3l, hW3r⟩ := hlift W
    have hfd := form_diff O cj hcj hO t t' hZ₁ hZ₂ hk hG₁ hG₂ p Y Y₃ W W₃ hY3l hY3r hW3l hW3r
    rw [hY3] at hY
    rw [hW3] at hW
    have e1 := (Submodule.Quotient.eq _).1 hY.symm
    have e2 := (Submodule.Quotient.eq _).1 hW.symm
    have f1 := LocCnt0LAlg.formC_rel_left O cj (Z₂.map O.subtype) ↑t ↑t' hG₂ hO _ W₂ e1
    have f2 := LocCnt0LAlg.formC_rel_right O cj hcj (Z₂.map O.subtype) ↑t ↑t' ht ht' hG₂ hO Y₃ _ e2
    rw [LocCnt0LAlg.formC_sub_left] at f1
    rw [LocCnt0LAlg.formC_sub_right] at f2
    have hsum := O.add_mem (O.add_mem f1 f2) hfd
    convert hsum using 1
    ring
  · apply Set.Subset.antisymm
    · rintro _ ⟨q, ⟨Y, hY0, rfl⟩, rfl⟩
      obtain ⟨y₂', hy₂'⟩ := Submodule.Quotient.mk_surjective _
        (p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)))
      have hl := linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.1 he (fun j => Y (Sum.inl j)) hY0
      have hs := p.2.2.1 _ _ hy₂'.symm
      refine ⟨Sum.elim (fun j => Y (Sum.inl j)) y₂', fun a => hY0 a, ?_⟩
      dsimp only
      refine Prod.ext ?_ (Prod.ext rfl ?_)
      · rw [hθ, hl, ← hy₂', mk_elim]
      · exact hs.symm
    · rintro _ ⟨Y₂, hY0, rfl⟩
      obtain ⟨y', hy'⟩ := Submodule.Quotient.mk_surjective _
        (p.1.2.symm (Submodule.Quotient.mk fun j => Y₂ (Sum.inr j)))
      have hp2 : p.1.2 (Submodule.Quotient.mk y') = Submodule.Quotient.mk fun j => Y₂ (Sum.inr j) := by
        rw [hy', LinearEquiv.apply_symm_apply]
      have hs := p.2.2.1 _ _ hp2
      have hl := linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.1 he (fun j => Y₂ (Sum.inl j)) hY0
      refine ⟨(Submodule.Quotient.mk (Sum.elim (fun j => Y₂ (Sum.inl j)) y'), ↑(Y₂ (Sum.inl (Fin.last r))),
        LocCntCommon.lamStarC cj (Z₁.map O.subtype) fun b => ↑(y' b)),
        ⟨Sum.elim (fun j => Y₂ (Sum.inl j)) y', fun a => hY0 a, rfl⟩, ?_⟩
      dsimp only
      refine Prod.ext ?_ (Prod.ext rfl ?_)
      · rw [hθ]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [hl, hp2, hsplit]
      · exact hs.symm
  · apply Set.Subset.antisymm
    · rintro _ ⟨q, ⟨Y, hY0, rfl⟩, rfl⟩
      obtain ⟨y₂, hy₂⟩ := Submodule.Quotient.mk_surjective _
        (p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)))
      have hr := linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.2 hes (fun j => Y (Sum.inr j)) hY0
      have hl := LocCnt0LAlg.lam_keep O hZ₁ hZ₂ (p.1.1 : LocCntCommon.MbMod Z₁ →ₗ[O] LocCntCommon.MbMod Z₂)
        hb _ _ (by exact hy₂.symm)
      refine ⟨Sum.elim y₂ (fun j => Y (Sum.inr j)), fun b => hY0 b, ?_⟩
      dsimp only
      refine Prod.ext ?_ (Prod.ext ?_ rfl)
      · rw [hθ, hr, ← hy₂, mk_elim]
      · exact hl.symm
    · rintro _ ⟨Y₂, hY0, rfl⟩
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
        (p.1.1.symm (Submodule.Quotient.mk fun j => Y₂ (Sum.inl j)))
      have hp1 : p.1.1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk fun j => Y₂ (Sum.inl j) := by
        rw [hy, LinearEquiv.apply_symm_apply]
      have hl := LocCnt0LAlg.lam_keep O hZ₁ hZ₂ (p.1.1 : LocCntCommon.MbMod Z₁ →ₗ[O] LocCntCommon.MbMod Z₂)
        hb _ _ (by exact hp1)
      have hr := linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.2 hes (fun j => Y₂ (Sum.inr j)) hY0
      refine ⟨(Submodule.Quotient.mk (Sum.elim y (fun j => Y₂ (Sum.inr j))),
        LocCntCommon.lamC (Z₁.map O.subtype) (fun a => ↑(y a)), ↑(Y₂ (Sum.inr (Fin.last r)))),
        ⟨Sum.elim y (fun j => Y₂ (Sum.inr j)), fun b => hY0 b, rfl⟩, ?_⟩
      dsimp only
      refine Prod.ext ?_ (Prod.ext ?_ rfl)
      · rw [hθ]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [hr, hp1, hsplit]
      · exact hl.symm
  · intro m
    refine Submodule.Quotient.induction_on _ m (fun y => ?_)
    rw [iL_mk, hθ]
    have h0 : (Submodule.Quotient.mk (fun j => (Sum.elim y 0 : LocCntCommon.Ix r → O) (Sum.inr j)) :
        LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₁)) = 0 := Submodule.Quotient.mk_zero _
    rw [h0, map_zero, map_zero, add_zero]
    rfl
  · intro m
    refine Submodule.Quotient.induction_on _ m (fun y => ?_)
    rw [iR_mk, hθ]
    have h0 : (Submodule.Quotient.mk (fun j => (Sum.elim 0 y : LocCntCommon.Ix r → O) (Sum.inl j)) :
        LocCntCommon.MbMod Z₁) = 0 := Submodule.Quotient.mk_zero _
    rw [h0, map_zero, map_zero, zero_add]
    rfl

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

theorem stepPairG_holds : StepPairG := stepPairG_of_fwd_bwd fwdEx bwdEx

theorem algAll_holds : Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU.AlgAll := algAll_of stepPairG_holds

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
