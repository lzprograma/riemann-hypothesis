module

import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.ThetaMbeUFalseOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.MemPerpSpanIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.AdjLast
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.OmPMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.CoordU
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GraphTransport4
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.DlRSwapZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CoordGHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.Common
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.HSmulSubRight
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScaleFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobalCountOfSplitMode
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.HSumRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.GraphTransport
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem h_om'_f'U (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (b : Fin (r + 1)) :
    H.h (H.om' f f') (f' b) = if b = Fin.last r then -algebraMap F E T' * H.Dl f f' r else 0 := by
  unfold HermSp.om'
  rw [h_sum_left]
  obtain ⟨h0, hl⟩ := hF'
  split_ifs with hb
  · subst hb
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [hl, adj_last]
      ring
    · intro c _ hc
      rw [h0 c (Fin.last r) (Or.inl hc), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · apply Finset.sum_eq_zero
    intro c _
    rw [h0 c b (Or.inr hb), mul_zero]

theorem h_om'_om'U (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') :
    H.h (H.om' f f') (H.om' f f') = M.L.cj (H.Dl f f' r) * (-algebraMap F E T' * H.Dl f f' r) := by
  rw [show H.h (H.om' f f') (H.om' f f') =
      H.h (H.om' f f') (∑ b, (H.Zhat f f').adjugate b (Fin.last r) • f' b) from rfl, h_sum_right]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [h_om'_f'U H f f' T' hF', ite_eq_left rfl, adj_last]
  · intro b _ hb
    rw [h_om'_f'U H f f' T' hF', ite_eq_right hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mem_X_ofU (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1)))
    (hG : IsUnit (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f f' r * M.L.cj (H.Dl f f' r))))
    (v : V) (hv : v ∈ Submodule.span E (Set.range (Sum.elim f f')))
    (h1 : ∀ a, H.h v (f a) = 0) (h2 : H.h (H.om' f f') v = 0) : v ∈ H.X f := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hv
  have hvxy : v = (∑ a, c (Sum.inl a) • f a) + ∑ b, c (Sum.inr b) • f' b := by
    rw [← hc, Fintype.sum_sum_type]
    rfl
  rw [hvxy] at h1 h2
  rw [hvxy]
  have key1 : ∀ a, Matrix.mulVec (H.Zhat f f') (fun b => c (Sum.inr b)) a =
      if a = Fin.last r then algebraMap F E T * c (Sum.inl (Fin.last r)) else 0 := by
    intro a
    have h := h1 a
    rw [HermSp.h_add_left, h_sum_left, h_sum_left] at h
    have hs : ∑ i, c (Sum.inl i) * H.h (f i) (f a) =
        if a = Fin.last r then c (Sum.inl (Fin.last r)) * -algebraMap F E T else 0 := by
      split_ifs with ha
      · subst ha
        rw [Finset.sum_eq_single (Fin.last r)]
        · rw [hF.2]
        · intro i _ hi
          rw [hF.1 i (Fin.last r) (Or.inl hi), mul_zero]
        · intro h'
          exact absurd (Finset.mem_univ _) h'
      · apply Finset.sum_eq_zero
        intro i _
        rw [hF.1 i a (Or.inr ha), mul_zero]
    have hw : Matrix.mulVec (H.Zhat f f') (fun b => c (Sum.inr b)) a =
        ∑ b, c (Sum.inr b) * H.h (f' b) (f a) := by
      simp only [Matrix.mulVec, dotProduct, HermSp.Zhat, Matrix.of_apply]
      exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
    rw [hw]
    rw [hs] at h
    split_ifs with ha
    · rw [ite_eq_left ha] at h
      linear_combination h
    · rw [ite_eq_right ha, zero_add] at h
      exact h
  have key2 : ∀ b, H.Dl f f' (r + 1) * c (Sum.inr b) =
      (H.Zhat f f').adjugate b (Fin.last r) * (algebraMap F E T * c (Sum.inl (Fin.last r))) := by
    intro b
    have hm : Matrix.mulVec (H.Zhat f f').adjugate (Matrix.mulVec (H.Zhat f f') (fun b => c (Sum.inr b))) =
        H.Dl f f' (r + 1) • (fun b => c (Sum.inr b)) := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, dl_full]
    have hb := congrFun hm b
    rw [funext key1] at hb
    rw [Pi.smul_apply, smul_eq_mul] at hb
    rw [← hb]
    simp [Matrix.mulVec, dotProduct]
  have hxl : c (Sum.inl (Fin.last r)) = 0 := by
    rw [h_add_right, h_sum_right, h_sum_right] at h2
    have s1 : ∑ a, M.L.cj (c (Sum.inl a)) * H.h (H.om' f f') (f a) =
        M.L.cj (c (Sum.inl (Fin.last r))) * H.Dl f f' (r + 1) := by
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [h_om'_f, ite_eq_left rfl, dl_full]
      · intro i _ hi
        rw [h_om'_f, ite_eq_right hi, mul_zero]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    have s2 : ∑ b, M.L.cj (c (Sum.inr b)) * H.h (H.om' f f') (f' b) =
        M.L.cj (c (Sum.inr (Fin.last r))) * (-algebraMap F E T' * H.Dl f f' r) := by
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [h_om'_f'U H f f' T' hF', ite_eq_left rfl]
      · intro i _ hi
        rw [h_om'_f'U H f f' T' hF', ite_eq_right hi, mul_zero]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    rw [s1, s2] at h2
    have k := key2 (Fin.last r)
    rw [adj_last] at k
    have kc := congrArg M.L.cj k
    rw [map_mul, map_mul, map_mul, AlgEquiv.commutes] at kc
    rw [map_mul] at hG
    have hX : M.L.cj (c (Sum.inl (Fin.last r))) *
        (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
          algebraMap F E T * algebraMap F E T' * (H.Dl f f' r * M.L.cj (H.Dl f f' r))) = 0 := by
      linear_combination M.L.cj (H.Dl f f' (r + 1)) * h2 + (algebraMap F E T' * H.Dl f f' r) * kc
    have hX0 := hG.mul_left_eq_zero.mp hX
    have := congrArg M.L.cj hX0
    rwa [M.L.cj_cj, map_zero] at this
  have hy : ∀ b, c (Sum.inr b) = 0 := by
    intro b
    have k := key2 b
    rw [hxl, mul_zero, mul_zero] at k
    exact hD.mul_right_eq_zero.mp k
  have hy0 : ∑ b, c (Sum.inr b) • f' b = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    rw [hy b, zero_smul]
  rw [hy0, add_zero, Fin.sum_univ_castSucc, hxl, zero_smul, add_zero]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem nu_mul (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD : IsUnit (H.Dl f f' (r + 1))) :
    H.h (omP H f f') (omP H f f') * (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1))) =
      -algebraMap F E T' * (H.Dl f f' r * M.L.cj (H.Dl f f' r)) := by
  rw [omP, H.h_smul_left, h_smul_right, h_om'_om'U H f f' T' hF']
  have h1 : Ring.inverse (H.Dl f f' (r + 1)) * H.Dl f f' (r + 1) = 1 := Ring.inverse_mul_cancel _ hD
  have h2 : M.L.cj (Ring.inverse (H.Dl f f' (r + 1))) * M.L.cj (H.Dl f f' (r + 1)) = 1 := by
    rw [← map_mul, h1, map_one]
  linear_combination (-algebraMap F E T' * (H.Dl f f' r * M.L.cj (H.Dl f f' r)) *
    M.L.cj (Ring.inverse (H.Dl f f' (r + 1))) * M.L.cj (H.Dl f f' (r + 1))) * h1 +
    (-algebraMap F E T' * (H.Dl f f' r * M.L.cj (H.Dl f f' r))) * h2

theorem eta_unit (f f' : Fin (r + 1) → V) (T T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD : IsUnit (H.Dl f f' (r + 1)))
    (hG : IsUnit (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f f' r * M.L.cj (H.Dl f f' r)))) :
    IsUnit (1 + algebraMap F E T * H.h (omP H f f') (omP H f f')) := by
  have key : (1 + algebraMap F E T * H.h (omP H f f') (omP H f f')) *
      (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1))) =
      H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
        algebraMap F E (T * T') * (H.Dl f f' r * M.L.cj (H.Dl f f' r)) := by
    rw [map_mul]
    linear_combination (algebraMap F E T) * nu_mul H f f' T' hF' hD
  have : IsUnit ((1 + algebraMap F E T * H.h (omP H f f') (omP H f f')) *
      (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)))) := by rw [key]; exact hG
  exact isUnit_of_mul_isUnit_left this

theorem decompU (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1)))
    (hG : IsUnit (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f f' r * M.L.cj (H.Dl f f' r))))
    (u : V) (hu : u ∈ Submodule.span E (Set.range (Sum.elim f f'))) (hX : u ∈ H.perp (H.X f))
    (α β : E)
    (hα : α * (1 + algebraMap F E T * H.h (omP H f f') (omP H f f')) =
      H.h u (omP H f f') - H.h (omP H f f') (omP H f f') * H.h u (f (Fin.last r)))
    (hβ : β = H.h u (f (Fin.last r)) + algebraMap F E T * α) :
    u - (α • f (Fin.last r) + β • omP H f f') ∈ H.X f := by
  have hom'eq : H.om' f f' = H.Dl f f' (r + 1) • omP H f f' := by
    unfold omP
    rw [smul_smul, Ring.mul_inverse_cancel _ hD, one_smul]
  apply mem_X_ofU H f f' T T' hF hF' hD hG
  · refine Submodule.sub_mem _ hu (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ (omP_mem_span H f f')))
    exact Submodule.subset_span ⟨Sum.inl (Fin.last r), rfl⟩
  · intro a
    rw [_root_.Formalism.L2.SG.LsDatumA.h_sub_left, HermSp.h_add_left, HermSp.h_smul_left, HermSp.h_smul_left,
      h_omP_f H f f' hD a]
    by_cases ha : a = Fin.last r
    · subst ha
      rw [ite_eq_left rfl, hF.2, hβ]
      ring
    · rw [ite_eq_right ha, hF.1 (Fin.last r) a (Or.inr ha)]
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr ha
      rw [(mem_perpX_iff H f u).mp hX i]
      ring
  · have hw : H.h (u - (α • f (Fin.last r) + β • omP H f f')) (omP H f f') = 0 := by
      rw [_root_.Formalism.L2.SG.LsDatumA.h_sub_left, HermSp.h_add_left, HermSp.h_smul_left, HermSp.h_smul_left,
        h_z_omP H f f' hD, hβ]
      linear_combination -hα
    rw [hom'eq, HermSp.h_smul_left, H.h_herm _ (omP H f f'), hw, map_zero, mul_zero]

theorem mkW_decompU (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1)))
    (hG : IsUnit (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f f' r * M.L.cj (H.Dl f f' r))))
    (u : ↥(H.perp (H.X f))) (hu : (u : V) ∈ Submodule.span E (Set.range (Sum.elim f f'))) (α : E)
    (hα : α * (1 + algebraMap F E T * H.h (omP H f f') (omP H f f')) =
      H.h u (omP H f f') - H.h (omP H f f') (omP H f f') * H.h u (f (Fin.last r))) :
    H.mkW f u = α • H.mkW f ⟨f (Fin.last r), z_mem H f T hF⟩ +
      (H.h u (f (Fin.last r)) + algebraMap F E T * α) • H.mkW f ⟨omP H f f', omP_mem H f f' hD⟩ := by
  have hmem := decompU H f f' T T' hF hF' hD hG (u : V) hu u.2 α
    (H.h u (f (Fin.last r)) + algebraMap F E T * α) hα rfl
  rw [← map_smul, ← map_smul, ← map_add (f := _)]
  simp only [HermSp.mkW, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  simpa using hmem

theorem nu_eq (f₁ f₁' f₂ f₂' : Fin (r + 1) → V) (T' : F) (hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H f₁' T')
    (hF₂' : Formalism.MainNotions.ThinScalesBound.FrameK H f₂' T') (hD₁ : IsUnit (H.Dl f₁ f₁' (r + 1))) (hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)))
    (hrel : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    H.h (omP H f₁ f₁') (omP H f₁ f₁') = H.h (omP H f₂ f₂') (omP H f₂ f₂') := by
  have e₁ := nu_mul H f₁ f₁' T' hF₁' hD₁
  have e₂ := nu_mul H f₂ f₂' T' hF₂' hD₂
  have crel : M.L.cj (H.Dl f₁ f₁' r) * M.L.cj (H.Dl f₂ f₂' (r + 1)) =
      M.L.cj (H.Dl f₂ f₂' r) * M.L.cj (H.Dl f₁ f₁' (r + 1)) := by
    rw [← map_mul, ← map_mul, hrel]
  have hN : IsUnit ((H.Dl f₁ f₁' (r + 1) * M.L.cj (H.Dl f₁ f₁' (r + 1))) *
      (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1)))) :=
    (hD₁.mul (hD₁.map M.L.cj)).mul (hD₂.mul (hD₂.map M.L.cj))
  apply hN.mul_right_cancel
  linear_combination (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1))) * e₁ -
    (H.Dl f₁ f₁' (r + 1) * M.L.cj (H.Dl f₁ f₁' (r + 1))) * e₂ -
    algebraMap F E T' * (M.L.cj (H.Dl f₁ f₁' r) * M.L.cj (H.Dl f₂ f₂' (r + 1))) * hrel -
    algebraMap F E T' * (H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) * crel

theorem mkW_transport {f₁ f₁' f₂ f₂' : Fin (r + 1) → V} {T T' : F}
    (hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H f₁ T) (hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H f₁' T')
    (hF₂ : Formalism.MainNotions.ThinScalesBound.FrameK H f₂ T) (hF₂' : Formalism.MainNotions.ThinScalesBound.FrameK H f₂' T')
    (hD₁ : IsUnit (H.Dl f₁ f₁' (r + 1))) (hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)))
    (hG₁ : IsUnit (H.Dl f₁ f₁' (r + 1) * M.L.cj (H.Dl f₁ f₁' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f₁ f₁' r * M.L.cj (H.Dl f₁ f₁' r))))
    (hG₂ : IsUnit (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f₂ f₂' r * M.L.cj (H.Dl f₂ f₂' r))))
    (hν : H.h (omP H f₁ f₁') (omP H f₁ f₁') = H.h (omP H f₂ f₂') (omP H f₂ f₂'))
    (φ : H.Wb f₁ ≃ₗ[E] H.Wb f₂)
    (hz : φ (H.mkW f₁ ⟨f₁ (Fin.last r), z_mem H f₁ T hF₁⟩) = H.mkW f₂ ⟨f₂ (Fin.last r), z_mem H f₂ T hF₂⟩)
    (ho : φ (H.mkW f₁ ⟨omP H f₁ f₁', omP_mem H f₁ f₁' hD₁⟩) = H.mkW f₂ ⟨omP H f₂ f₂', omP_mem H f₂ f₂' hD₂⟩)
    (u₁ : ↥(H.perp (H.X f₁))) (hu₁ : (u₁ : V) ∈ Submodule.span E (Set.range (Sum.elim f₁ f₁')))
    (u₂ : ↥(H.perp (H.X f₂))) (hu₂ : (u₂ : V) ∈ Submodule.span E (Set.range (Sum.elim f₂ f₂')))
    (c1 : H.h u₂ (f₂ (Fin.last r)) = H.h u₁ (f₁ (Fin.last r)))
    (c2 : H.h u₂ (omP H f₂ f₂') = H.h u₁ (omP H f₁ f₁')) :
    H.mkW f₂ u₂ = φ (H.mkW f₁ u₁) := by
  have e1 := eta_unit H f₁ f₁' T T' hF₁' hD₁ hG₁
  obtain ⟨α, hα₁⟩ : ∃ α : E, α * (1 + algebraMap F E T * H.h (omP H f₁ f₁') (omP H f₁ f₁')) =
      H.h u₁ (omP H f₁ f₁') - H.h (omP H f₁ f₁') (omP H f₁ f₁') * H.h u₁ (f₁ (Fin.last r)) :=
    ⟨(H.h u₁ (omP H f₁ f₁') - H.h (omP H f₁ f₁') (omP H f₁ f₁') * H.h u₁ (f₁ (Fin.last r))) *
      Ring.inverse (1 + algebraMap F E T * H.h (omP H f₁ f₁') (omP H f₁ f₁')),
      by rw [mul_assoc, Ring.inverse_mul_cancel _ e1, mul_one]⟩
  have hα₂ : α * (1 + algebraMap F E T * H.h (omP H f₂ f₂') (omP H f₂ f₂')) =
      H.h u₂ (omP H f₂ f₂') - H.h (omP H f₂ f₂') (omP H f₂ f₂') * H.h u₂ (f₂ (Fin.last r)) := by
    rw [← hν, c1, c2]
    exact hα₁
  rw [mkW_decompU H f₂ f₂' T T' hF₂ hF₂' hD₂ hG₂ u₂ hu₂ α hα₂, c1,
    mkW_decompU H f₁ f₁' T T' hF₁ hF₁' hD₁ hG₁ u₁ hu₁ α hα₁, map_add, map_smul, map_smul, hz, ho]

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

section Parts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem unit_gramCU {f f' : Fin (r + 1) → V} {T T' : F}
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD1 : IsUnit (H.Dl f f' (r + 1))) (hGd : IsUnit (H.Gdet f f' T T')) :
    IsUnit (gramC (M.L.cj : E →+* E) (H.Zhat f f') (algebraMap F E T) (algebraMap F E T')).det := by
  apply _root_.Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU.unit_gramC_of <;> assumption

theorem unit_gramHU {g : SplitG M.L} (hs : M.split = some g) {t : Term V M r}
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T')
    (hD1 : IsUnit (H.Dl t.f t.f' (r + 1))) (hGd : IsUnit (H.Gdet t.f t.f' t.T t.T')) :
    IsUnit (gramH H (H.MMfam t)).det := by
  set qi := algebraMap F E ((g.q : F)⁻¹) with hqi
  let B : Matrix (Ix r) (Ix r) E := Matrix.fromBlocks 1 0 (-qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))
    (qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))
  have hfam : H.MMfam t = fun i => ∑ j, B i j • Sum.elim t.f t.f' j := by
    rw [mmfam_some H hs]
    funext i
    rcases i with a | a
    · simp [B, Fintype.sum_sum_type, Matrix.one_apply]
    · simp [B, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, add_comm, neg_smul]
      rfl
  have hqu : IsUnit qi := by
    refine ⟨⟨qi, algebraMap F E (g.q : F), qi_mul_q g, ?_⟩, rfl⟩
    rw [mul_comm]; exact qi_mul_q g
  have hB : IsUnit B.det := by
    simp only [B]
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_smul, Matrix.det_one, mul_one]
    exact hqu.pow _
  have hV : gramH H (Sum.elim t.f t.f') = gramC (M.L.cj : E →+* E) (H.Zhat t.f t.f')
      (algebraMap F E t.T) (algebraMap F E t.T') := by
    rw [gramC_eq H _ _ _ _ hF hF']
    ext i j; rfl
  have hG := unit_gramCU H hF hF' hD1 hGd
  rw [hfam, gramH_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hV]
  have hBc : IsUnit (B.map M.L.cj).det := by
    have : (B.map M.L.cj).det = M.L.cj B.det := by
      rw [show (B.map M.L.cj) = (M.L.cj : E →+* E).mapMatrix B from rfl, ← RingHom.map_det]; rfl
    rw [this]; exact hB.map _
  exact (hB.mul hG).mul hBc

theorem gdet_eq (f f' : Fin (r + 1) → V) (T T' : F) :
    H.Gdet f f' T T' = H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f f' r * M.L.cj (H.Dl f f' r)) := rfl

theorem gdet_swap (f f' : Fin (r + 1) → V) (T T' : F) : H.Gdet f' f T' T = H.Gdet f f' T T' := by
  rw [gdet_eq, gdet_eq, dl_swap_full, dl_swap_r, M.L.cj_cj, M.L.cj_cj, mul_comm T' T]
  ring

theorem gamR_sepU {g : SplitG M.L} {t₁ : Term V M r} {f₂ f₂' : Fin (r + 1) → V}
    (hg₁ : GoodG H g t₁) (hg₂ : GoodG H g (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r))
    (hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T')) (hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T'))
    (hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1))
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂')
    (hz : φ (H.mkW t₁.f ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩) = H.mkW f₂ ⟨_, z_mem H f₂ t₁.T hg₂.2.1⟩)
    (ho : φ (H.mkW t₁.f ⟨_, omP_mem H t₁.f t₁.f' hg₁.2.2.2.1⟩) =
      H.mkW f₂ ⟨_, omP_mem H f₂ f₂' hg₂.2.2.2.1⟩)
    (hz' : φ' (H.mkW t₁.f' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩) =
      H.mkW f₂' ⟨_, z_mem H f₂' t₁.T' hg₂.2.2.1⟩)
    (ho' : φ' (H.mkW t₁.f' ⟨_, omP_mem H t₁.f' t₁.f (unit_swap H t₁.f t₁.f' hg₁.2.2.2.1)⟩) =
      H.mkW f₂' ⟨_, omP_mem H f₂' f₂ (unit_swap H f₂ f₂' hg₂.2.2.2.1)⟩) :
    ∀ p ∈ GamR H t₁ (algebraMap F E (g.q : F)),
      ∀ p₂ ∈ GamR H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) (algebraMap F E (g.q : F)),
      PcG H hg₂ p₂.2.2.1 = PcG H hg₁ p.2.2.1 → PcG' H hg₂ p₂.2.2.2 = PcG' H hg₁ p.2.2.2 →
      p₂.2.2.1 = φ p.2.2.1 ∧ p₂.2.2.2 = φ' p.2.2.2 := by
  rintro _ ⟨u₁, u₁', u₁'', hu₁, hu₁', -, rfl⟩ _ ⟨u₂, u₂', u₂'', hu₂, hu₂', -, rfl⟩ hc hc'
  simp only [PcG, PcG', coordW_mk, Prod.mk.injEq] at hc hc'
  have hν := nu_eq H t₁.f t₁.f' f₂ f₂' t₁.T' hg₁.2.2.1 hg₂.2.2.1 hg₁.2.2.2.1 hg₂.2.2.2.1 hrel
  have hrel' : H.Dl t₁.f' t₁.f r * H.Dl f₂' f₂ (r + 1) = H.Dl f₂' f₂ r * H.Dl t₁.f' t₁.f (r + 1) := by
    rw [dl_swap_r H t₁.f t₁.f', dl_swap_full H f₂ f₂', dl_swap_r H f₂ f₂', dl_swap_full H t₁.f t₁.f',
      ← map_mul, ← map_mul, hrel]
  have hν' := nu_eq H t₁.f' t₁.f f₂' f₂ t₁.T hg₁.2.1 hg₂.2.1 (unit_swap H _ _ hg₁.2.2.2.1)
    (unit_swap H _ _ hg₂.2.2.2.1) hrel'
  constructor
  · exact mkW_transport H hg₁.2.1 hg₁.2.2.1 hg₂.2.1 hg₂.2.2.1 hg₁.2.2.2.1 hg₂.2.2.2.1
      (by rw [← gdet_eq]; exact hG₁) (by rw [← gdet_eq]; exact hG₂) hν φ hz ho ⟨u₁, hu₁⟩
      (mem_span_of_sharpG H hg₁ u₁) ⟨u₂, hu₂⟩ (mem_span_of_sharpG H hg₂ u₂) hc.1 hc.2
  · exact mkW_transport H hg₁.2.2.1 hg₁.2.1 hg₂.2.2.1 hg₂.2.1 (unit_swap H _ _ hg₁.2.2.2.1)
      (unit_swap H _ _ hg₂.2.2.2.1)
      (by rw [← gdet_eq, gdet_swap]; exact hG₁) (by rw [← gdet_eq, gdet_swap]; exact hG₂) hν' φ' hz' ho'
      ⟨u₁', hu₁'⟩ (by rw [span_swap]; exact mem_span_of_sharpG H hg₁ u₁') ⟨u₂', hu₂'⟩
      (by rw [span_swap]; exact mem_span_of_sharpG H hg₂ u₂') hc'.2 hc'.1

end Parts

theorem coordGU_holds : CoordGU := by
  intro F _ _ _ E _ _ _ _ M g hs r n V _ _ H hn t₁ f₂ f₂' φ φ' hyp hU2 hR
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hyp.1.1.2.1.2.1, hyp.1.1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hyp.1.1.2.2.1.2.1, hyp.1.1.2.2.1.2.2.1⟩
  have hT : t₁.T ∈ 𝒪[F] := hyp.1.1.2.1.2.2.2.1
  have hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1) :=
    hyp.2.2.2.1.2.2.2.2.2
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := by
    have hG : H.Gdet t₁.f t₁.f' t₁.T t₁.T' ≠ 0 := hyp.1.1.2.2.2.2.1
    apply isUnit_of_cj_fixed g _ hG
    rw [gdet_eq]
    simp only [map_sub, map_mul, M.L.cj_cj, M.L.cj.commutes]
    ring
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have key := gdet_rel (M := M) (H.Dl t₁.f t₁.f' (r + 1)) (H.Dl t₁.f t₁.f' r) (H.Dl f₂ f₂' (r + 1))
      (H.Dl f₂ f₂' r) (algebraMap F E (t₁.T * t₁.T')) hrel
    have hB : IsUnit (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1))) := hU2.mul (hU2.map M.L.cj)
    have : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' *
        (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1)))) := by
      rw [gdet_eq, key]; exact hB.mul (by rw [← gdet_eq]; exact hG₁)
    exact isUnit_of_mul_isUnit_left this
  have hg₁ : GoodG H g t₁ := ⟨hs, hF₁, hF₁', dl_succ_unit hyp,
    unit_gramHU H hs hF₁ hF₁' (dl_succ_unit hyp) hG₁⟩
  have hg₂ : GoodG H g (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) :=
    ⟨hs, hyp.2.1, hyp.2.2.1, hU2, unit_gramHU H hs hyp.2.1 hyp.2.2.1 hU2 hG₂⟩
  have hTT := (hyp.1.1.2.2.2.2.2 g hs).2.1
  have hI := hyp.2.2.2.1
  have hmm : MMInt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) := mmInt_G H hg₂ hT hTT hR
  have eZ := sends_one H φ _ _ (z_mem H t₁.f t₁.T hF₁) (z_mem H f₂ t₁.T hyp.2.1) hyp.2.2.2.2.1
  have eZ' := sends_one H φ' _ _ (z_mem H t₁.f' t₁.T' hF₁') (z_mem H f₂' t₁.T' hyp.2.2.1)
    hyp.2.2.2.2.2
  have eO := sends_omP H φ hg₁.2.2.2.1 hU2 hI.2.2.2.1
  have eO' := sends_omP' H φ' hg₁.2.2.2.1 hU2 hI.2.2.2.2.1
  have hGam := fun θ : DDt H t₁ ≃ₗ[M.L.O] DDt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) =>
    graph_transport4 (PsiG H hg₁).toEquiv (PsiG H hg₂).toEquiv θ.toEquiv φ φ' (PcG H hg₁) (PcG H hg₂)
      (PcG' H hg₁) (PcG' H hg₂) (GamR H t₁ (algebraMap F E (g.q : F))) (GamR H _ (algebraMap F E (g.q : F)))
      _ _ (gamR_image H hg₁) (gamR_image H hg₂)
      (coordW_comp H φ hI.1 _ _ _ _ _ _ _ _ eZ eO)
      (coordW_comp H φ' hI.2.1 _ _ _ _ _ _ _ _ eO' eZ')
      (gamR_sepU H hg₁ hg₂ hG₁ hG₂ hrel φ φ' eZ eO eZ' eO')
  have key : ∀ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r),
      θ ∈ Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' ↔
        (PsiG H hg₁).symm.trans (θ.trans (PsiG H hg₂)) ∈
          ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F)) (algebraMap F E ((g.q : F)⁻¹))
            (H.Zhat t₁.f t₁.f') (H.Zhat f₂ f₂') (algebraMap F E t₁.T) (algebraMap F E t₁.T') := by
    intro θ
    constructor
    · rintro ⟨_, _, hD', _, hG⟩
      exact ⟨(isomD_iffG H hg₁ hg₂ θ).1 hD', (hGam θ).1 (hG g hs)⟩
    · rintro ⟨hD', hG⟩
      refine ⟨hU2, hmm, (isomD_iffG H hg₁ hg₂ θ).2 hD', fun h => ?_, fun g' hg' => ?_⟩
      · rw [hs] at h; cases h
      · rw [hs] at hg'
        cases hg'
        exact (hGam θ).2 hG
  refine Nat.card_congr
    { toFun := fun θ => ⟨(PsiG H hg₁).symm.trans (θ.1.trans (PsiG H hg₂)), (key θ.1).1 θ.2⟩
      invFun := fun θc => ⟨(PsiG H hg₁).trans (θc.1.trans (PsiG H hg₂).symm), (key _).2 (by
        convert θc.2 using 1
        ext x
        simp)⟩
      left_inv := fun θ => by
        apply Subtype.ext; apply LinearEquiv.ext; intro x; simp
      right_inv := fun θc => by
        apply Subtype.ext; apply LinearEquiv.ext; intro x; simp }

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem thetaPresentation_of_split (M : Model F E) (g : SplitG M.L) (hs : M.split = some g)
    (r n : ℕ) : ThetaPresentation M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp hunit Z₁ Z₂ e₁ e₂
  have hg := hyp.1
  have hrel := hyp.2.2.2.1.2.2.2.2.2
  have hzz : ∀ a b, HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a b ∈ M.R := by
    intro a b
    have := (Z₂ a b).2
    rw [show ((Z₂ a b : M.R) : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a b from
      congrFun (congrFun e₂ a) b] at this
    exact this
  have hG1 : IsUnit (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1)) - algebraMap F E (t₁.T * t₁.T') *
      (H.Dl t₁.f t₁.f' r * M.L.cj (H.Dl t₁.f t₁.f' r))) := by
    have hG : H.Gdet t₁.f t₁.f' t₁.T t₁.T' ≠ 0 := hg.1.2.2.2.2.1
    unfold HermSp.Gdet HermSp.normE at hG
    apply isUnit_of_cj_fixed g _ hG
    simp only [map_sub, map_mul, M.L.cj_cj, cj_alg]
    ring
  rw [coordGU_holds F E M g hs r n V H hn t₁ f₂ f₂' φ φ' hyp hunit hzz]
  refine algGAllT_holds F E M g hs r t₁.T t₁.T' (hg.1.2.2.2.2.2 g hs).1 (hg.1.2.2.2.2.2 g hs).2.1 _ _ Z₁ Z₂ e₁ e₂
    ?_ ?_ ?_ ?_ ?_ hyp.1.1.2.1.2.2.2.1
  · rw [← dl_full]; exact dl_succ_unit hyp
  · rw [← dl_full]; exact hunit
  · rw [← dl_full, ← dl_full, ← dl_eq_det, ← dl_eq_det]
    linear_combination hrel.symm
  · rw [← dl_full, ← dl_eq_det]
    exact hG1
  · rw [← dl_full, ← dl_eq_det]
    have key := gdet_rel (M := M) (H.Dl t₁.f t₁.f' (r + 1)) (H.Dl t₁.f t₁.f' r) (H.Dl f₂ f₂' (r + 1))
      (H.Dl f₂ f₂' r) (algebraMap F E (t₁.T * t₁.T')) hrel
    have hA : IsUnit (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1))) :=
      (dl_succ_unit hyp).mul ((dl_succ_unit hyp).map M.L.cj)
    have hB : IsUnit (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1))) := hunit.mul (hunit.map M.L.cj)
    have : IsUnit ((H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1)) - algebraMap F E (t₁.T * t₁.T') *
        (H.Dl f₂ f₂' r * M.L.cj (H.Dl f₂ f₂' r))) * (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1)))) := by
      rw [key]; exact hB.mul hG1
    exact isUnit_of_mul_isUnit_left this

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

namespace Formalism.L2.SG.LocalCountModules

theorem thetaPresentation_holds {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : LocCntCommon.ThetaPresentation M r n := by
  cases hs : M.split with
  | none =>
    exact UnitaryGroupMassFormula.ThetaMbeU.thetaPresentation_of_nonsplit
      UnitaryGroupMassFormula.ThetaMbeU.coordU_holds UnramifiedPairingAlgebraic.algAll_holds M hs r n
  | some g => exact UnitaryGroupMassFormula.LocCntUG.thetaPresentation_of_split M g hs r n

end Formalism.L2.SG.LocalCountModules
