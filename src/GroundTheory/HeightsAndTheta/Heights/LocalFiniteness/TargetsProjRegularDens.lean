module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.TargetsProjFullRankMeetsRegular
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBallVolume
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem MahlerSectionOfConst.proof (h1 : DefectAverage.Statement) (h2 : AdmissibleAENrm.Statement)
    (h3 : BallVolume.Statement) : MahlerSectionOfConst.Statement := by
  intro e hconst n δ h Z f u data hu
  set K := mahlerDefect h e Z f u with hK
  have hrel : ∀ W ∈ Z.support, IsRelevant W := fun W hW => (data.prime W hW).isRelevant
  have hae : (fun v => mahlerDefect h e Z f (nrmv h v)) =ᵐ[volume.restrict (ballH h)] fun _ => K := by
    filter_upwards [h2 n h Z hrel] with v hv
    exact hconst n δ h Z f (nrmv h v) u data hv hu
  have havg : ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) = K := by
    rw [average_congr hae]
    obtain ⟨hpos, hfin⟩ := h3 n h
    exact setAverage_const hpos.ne' hfin.ne K
  have hmean := (h1 n e δ h Z f data).2
  rw [havg] at hmean
  have hK' : K = mahler h e (specFirst f u) - cycleIntegral h Z e (fsLog h u) := rfl
  linarith
end GroundTheory.Heights₂.Heights -- clump:auto
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

theorem IsChowFormCycle.ne_zero {n k : ℕ} {Z : ProjCycle ℂ n} {f : MvPolynomial (Fin k × Fin n) ℂ}
    (hf : IsChowFormCycle Z k f) : f ≠ 0 := by
  obtain ⟨c, hc, g, hg, rfl⟩ := hf
  refine mul_ne_zero ?_ ?_
  · rw [Ne, MvPolynomial.C_eq_zero]; exact hc
  · rw [Finset.prod_ne_zero_iff]
    intro W hW
    exact pow_ne_zero _ (hg W hW).1

theorem DefectAverage.proof (h1 : MahlerAverageSplit.Statement) (h2 : CycleAverage.Statement) :
    DefectAverage.Statement := by
  intro n e δ h Z f hZ
  obtain ⟨hi1, hm1⟩ := h1 n e δ h f hZ.chow.ne_zero hZ.homog
  obtain ⟨hi2, hm2⟩ := h2 n e δ h Z f hZ
  have hi : IntegrableOn (fun v => mahlerDefect h e Z f (nrmv h v)) (ballH h) := by
    unfold mahlerDefect; exact hi1.sub hi2
  refine ⟨hi, ?_⟩
  have hsub : ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) =
      (⨍ v in ballH h, mahler h e (specFirst f (nrmv h v))) -
        ⨍ v in ballH h, cycleIntegral h Z e (fsLog h (nrmv h v)) := by
    simp only [setAverage_eq, mahlerDefect]
    rw [integral_sub hi1 hi2, smul_sub]
  rw [hsub, ← hm1, hm2]
  ring

end GroundTheory.Heights₂.Heights
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem CycleAverage.proof (h1 : ConeAverage.Statement) : CycleAverage.Statement := by
  intro n e δ h Z f hd
  obtain ⟨c, hc, g, hg, hf⟩ := hd.chow
  have hf0 : C c * ∏ W ∈ Z.support, g W ^ Z W ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  have hhom : Heights.IsMultiHomog δ (C c * ∏ W ∈ Z.support, g W ^ Z W) := hf ▸ hd.homog
  obtain ⟨δW, hδW, hsum⟩ :=
    exists_degrees_of_chowFormCycle (Nat.succ_pos e) Z c g hg hhom hf0
  have hW : ∀ W ∈ Z.support,
      IntegrableOn (fun v => coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) ∧
        ⨍ v in ballH h, coneIntegral h W e (fsLog h (nrmv h v)) =
          -(δW W * (harmonic (n - 1) : ℝ)) / 2 :=
    fun W hm => h1 n e (δW W) h W (g W) (hd.prime W hm) (hg W hm) (hδW W hm)
  have hint : ∀ W ∈ Z.support,
      IntegrableOn (fun v => (Z W : ℝ) * coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) :=
    fun W hm => (hW W hm).1.const_mul _
  unfold cycleIntegral
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [setAverage_eq, integral_finsetSum _ hint, Finset.smul_sum]
  have hterm : ∀ W ∈ Z.support,
      (volume.real (ballH h))⁻¹ • ∫ v in ballH h, (Z W : ℝ) * coneIntegral h W e (fsLog h (nrmv h v)) =
        (Z W : ℝ) * (-(δW W * (harmonic (n - 1) : ℝ)) / 2) := by
    intro W hm
    rw [integral_const_mul, ← (hW W hm).2, setAverage_eq, smul_eq_mul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hδ : (δ : ℝ) = ∑ W ∈ Z.support, (Z W : ℝ) * (δW W : ℝ) := by
    rw [← hsum]; push_cast; rfl
  rw [hδ, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun W _ => ?_
  ring

end

end GroundTheory.Heights₂.Heights
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.CycleAverage : GroundTheory.Heights₂.Heights.CycleAverage.Statement :=
  @GroundTheory.Heights₂.Heights.CycleAverage.proof GroundTheory.Heights₂.Heights.AutoClose.ConeAverage
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.DefectAverage : GroundTheory.Heights₂.Heights.DefectAverage.Statement :=
  @GroundTheory.Heights₂.Heights.DefectAverage.proof GroundTheory.Heights₂.Heights.AutoClose.MahlerAverageSplit GroundTheory.Heights₂.Heights.AutoClose.CycleAverage
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.MahlerSectionOfConst : GroundTheory.Heights₂.Heights.MahlerSectionOfConst.Statement :=
  @GroundTheory.Heights₂.Heights.MahlerSectionOfConst.proof GroundTheory.Heights₂.Heights.AutoClose.DefectAverage GroundTheory.Heights₂.Heights.AutoClose.AdmissibleAENrm GroundTheory.Heights₂.Heights.BallVolume.proof
end -- clump:auto
end -- clump:auto
