module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PcIntGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfIso
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntegralClosureRankAndResidueTrdegLe
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ModularBoundZeroHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobalCountOfModule
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.DetUpdateRowLastSingle
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.DetAddCor

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
  Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc
open Formalism.L2.SG.LocalCountModules.LocCntCommon
open Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

namespace Formalism.L2.SG.Pf.PCount

variable {D : D7} (Zd : LocDat D)

/-- A common corner shift preserves marked presentations. Equal normalized leading minors
identify their marked isomorphisms with isomorphisms of the shifted cokernels. -/
private theorem card_isoMbe_shifted {p : PlF D}
    (Z₁ Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (Zd.M p).R) (c : (Zd.M p).R)
    (h₁ : IsUnit (Z₁.map (Zd.M p).R.subtype + cornE p c).det)
    (h₂ : IsUnit (Z₂.map (Zd.M p).R.subtype + cornE p c).det)
    (hrel : leadM (Z₁.map (Zd.M p).R.subtype) D.R.rS * (Z₂.map (Zd.M p).R.subtype + cornE p c).det =
      leadM (Z₂.map (Zd.M p).R.subtype) D.R.rS * (Z₁.map (Zd.M p).R.subtype + cornE p c).det) :
    Nat.card (IsoMbe Z₁ Z₂) = nIsoO Zd.M p
      (clsOf (Zd.M p) (Z₁.map (Zd.M p).R.subtype + cornE p c))
      (clsOf (Zd.M p) (Z₂.map (Zd.M p).R.subtype + cornE p c)) := by
  have map_shift (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (Zd.M p).R) :
      (Z + cornerM _ c).map (Zd.M p).R.subtype = Z.map (Zd.M p).R.subtype + cornE p c := by
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, cornerM, cornE, Matrix.of_apply]
    split <;> rfl
  let W₁ : (Zd.M p).Mat (D.R.rS + 1) := ⟨Z₁ + cornerM _ c, (map_shift Z₁) ▸ h₁⟩
  let W₂ : (Zd.M p).Mat (D.R.rS + 1) := ⟨Z₂ + cornerM _ c, (map_shift Z₂) ▸ h₂⟩
  have head (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (Zd.M p).R) :
      headDet (Zd.M p) (Z + cornerM _ c) = leadM (Z.map (Zd.M p).R.subtype) D.R.rS := by
    unfold headDet
    rw [map_shift, show cornE p (c : (D.s.atP p).Ep) = cornerM _ (c : (D.s.atP p).Ep) from rfl,
      head_add_cornerM, leadM, dite_eq_left (Nat.le_succ _)]
    rfl
  rw [← map_shift Z₁, ← map_shift Z₂, clsOf_map (Zd.M p) W₁, clsOf_map (Zd.M p) W₂]
  change _ = (Zd.M p).nIso _ _
  rw [nIso_mk_out (Zd.M p) W₁ W₂, ← card_isoMbe_shift Z₁ Z₂ c]
  apply Nat.card_congr (isoEquiv (Z₁ := W₁) (Z₂ := W₂) ?_)
  simpa only [W₁, W₂, head, map_shift] using hrel

theorem partnerCount_holds_all : PartnerIsomorphismCount Zd := by
  intro p T T' w w' t₁ f₂' φ φ' hk _ _ hyp h1 h2 hint2
  let H := locH Zd p
  let P₁ := H.ZZplus t₁
  let P₂ := Loc.HermSp.ZZplusOf (Zd.M p) (H.Zhat t₁.f f₂') t₁.T t₁.T'
  have hint1 := intGenP_holds Zd p t₁ hyp.1
  let Z₁ := Matrix.of fun a b => (⟨P₁ a b, hint1 a b⟩ : (Zd.M p).R)
  let Z₂ := Matrix.of fun a b => (⟨P₂ a b, hint2 a b⟩ : (Zd.M p).R)
  have count (hu : IsUnit (H.Dl t₁.f f₂' (D.R.rS + 1))) :
      Nat.card (locSet Zd p t₁ f₂' φ φ') = Nat.card (IsoMbe Z₁ Z₂) :=
    (LsDatumA.latSide_holds (Zd.M p) _ _ (Zd.agree p).1 _ H (finrank_Vp p) t₁ t₁.f f₂' φ φ' hyp).trans
      (LocalCountModules.thetaPresentation_holds (Zd.M p) _ _ _ H (finrank_Vp p) t₁ t₁.f f₂' φ φ' hyp hu Z₁ Z₂ rfl rfl)
  have hK := modKind_of Zd (modUnits_of Zd (shUnit_holds D))
  obtain ⟨L₁, U₁, hd₁, ho₁, hP₁⟩ := h1
  obtain ⟨L₂, U₂, hd₂, ho₂, hP₂⟩ := h2
  obtain ⟨hl₁, hu₁⟩ := loUp_of_hyp hd₁ ho₁
  obtain ⟨hl₂, hu₂⟩ := loUp_of_hyp hd₂ ho₂
  have hl1 : leadM P₁ D.R.rS = leadM (modMat Zd.δ T T' p w) D.R.rS := by
    rw [show P₁ = _ from hP₁, leadM_mul hl₁ hu₁]
  have hl2 : leadM P₂ D.R.rS = leadM (modMat Zd.δ T T' p w') D.R.rS := by
    rw [show P₂ = _ from hP₂, leadM_mul hl₂ hu₂]
  have hL₁ := leadZZ_holds Zd p (H.Zhat t₁.f t₁.f') t₁.T t₁.T'
  have hL₂ := leadZZ_holds Zd p (H.Zhat t₁.f f₂') t₁.T t₁.T'
  rw [← cornerSh_eq_of_kind Zd.δ T T' p hk]
  change _ = nIsoO Zd.M p (clsOf _ (P₁ + _)) (clsOf _ (P₂ + _))
  by_cases hD : Dmin w D.R.rS = 0
  · have hD' : Dmin w' D.R.rS = 0 := by
      by_contra hn
      simp [kind, hD, hn] at hk
    have hh₁ := hl1.trans ((hK p T T' w).1 hD)
    have hh₂ := hl2.trans ((hK p T T' w').1 hD')
    have hshift : cornerSh Zd.δ T T' p w = 0 := by simp [cornerSh, hD]
    rw [hshift, add_cornE_zero, add_cornE_zero]
    by_cases hp : IsUnit P₂.det
    · have hf : IsUnit (H.Dl t₁.f f₂' (D.R.rS + 1)) := by
        rw [dl_full]
        cases hs : (Zd.M p).split with
        | none => simpa only [P₂, zzplusOf_none hs] using hp
        | some g =>
          exact LocalCountModules.ThetaMbe0GWork.detG_holds _ _ _ g hs _ _ _ _
            (by rw [← dl_eq_det]; exact hL₂.1.2 hh₂) hp
      rw [count hf]
      have hp₁ : IsUnit P₁.det := hL₁.2.2 (hL₁.1.2 hh₁) hyp.1.1.2.2.2.1
      have step := card_isoMbe_shifted Zd Z₁ Z₂ 0
      simp only [Subring.coe_zero, add_cornE_zero] at step
      apply step
      · exact hp₁
      · exact hp
      · change leadM P₁ _ * _ = leadM P₂ _ * _
        rw [hh₁, hh₂, zero_mul, zero_mul]
    · have hc : clsOf (Zd.M p) P₂ = none := by
        unfold clsOf
        exact dite_eq_right fun h => hp h.2
      rw [hc, show ∀ o, nIsoO Zd.M p o none = 0 from fun o => by cases o <;> rfl, Nat.card_eq_zero]
      exact Or.inl ⟨fun ⟨_, hg, _⟩ => hp (hL₂.2.2 (hL₂.1.2 hh₂) hg.1.2.2.2.1)⟩
  · have hD' : Dmin w' D.R.rS ≠ 0 := by
      intro hz
      simp [kind, hD, hz] at hk
    have hz : zetaOf w = zetaOf w' := by simpa only [kind, hD, hD', ite_false, Option.some.injEq] using hk
    obtain ⟨hh₁, hcol₁, hlast₁, hs⟩ := (hK p T T' w).2 hD
    obtain ⟨hh₂, hcol₂, hlast₂, _⟩ := (hK p T T' w').2 hD'
    rw [← hz] at hlast₂
    let s := blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)
    let c : (Zd.M p).R := nSh s
    have hc : cornerSh Zd.δ T T' p w = (c : (D.s.atP p).Ep) := by simp [cornerSh, hD, c, s]
    have hd₁ : (P₁ + (c : (D.s.atP p).Ep) • Ecorner _).det = (s + c) * leadM P₁ D.R.rS :=
      det_shift hl₁ hu₁ hP₁ hcol₁ hlast₁
    have hd₂ : (P₂ + (c : (D.s.atP p).Ep) • Ecorner _).det = (s + c) * leadM P₂ D.R.rS :=
      det_shift hl₂ hu₂ hP₂ hcol₂ hlast₂
    have hPunit₁ : IsUnit (leadM P₁ D.R.rS) := hl1 ▸ hh₁
    have hPunit₂ : IsUnit (leadM P₂ D.R.rS) := hl2 ▸ hh₂
    have hfull := hyp.2.2.2.1.2.2.2.2.2
    have hunit : IsUnit (H.Dl t₁.f f₂' (D.R.rS + 1)) := by
      apply isUnit_of_mul_isUnit_right (x := H.Dl t₁.f t₁.f' D.R.rS)
      rw [hfull]
      exact (hL₂.2.1.2 hPunit₂).mul (dl_succ_unit hyp)
    rw [count hunit, hc]
    apply card_isoMbe_shifted Zd Z₁ Z₂ c
    · rw [show Z₁.map (Zd.M p).R.subtype = P₁ from rfl, cornE_eq, hd₁]
      exact hs.mul hPunit₁
    · rw [show Z₂.map (Zd.M p).R.subtype = P₂ from rfl, cornE_eq, hd₂]
      exact hs.mul hPunit₂
    · change leadM P₁ _ * (P₂ + _).det = leadM P₂ _ * (P₁ + _).det
      rw [cornE_eq, hd₁, hd₂]
      ring

end Formalism.L2.SG.Pf.PCount
