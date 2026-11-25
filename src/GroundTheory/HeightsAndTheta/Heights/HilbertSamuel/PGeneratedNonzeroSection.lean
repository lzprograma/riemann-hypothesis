module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedNonzeroSection
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartLatQCech
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedNonzeroSection

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

private def evLHom {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω}
    {T : Submonoid (MRingOver ℚ ι)} (hT : ∀ t ∈ T, aeval y t ≠ 0) :
    LocalizedModule T (MRingOver ℚ ι ⧸ GenOnFibres.idealOver y ℚ) →+* Ω where
  toFun := ChartLatQCech.val y T
  map_one' := by
    rw [show (1 : LocalizedModule T (MRingOver ℚ ι ⧸ GenOnFibres.idealOver y ℚ)) =
      LocalizedModule.mk 1 1 by rw [OreLocalization.one_def], ChartLatQCech.val_mk hT]
    simp
  map_mul' x x' := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
    induction x' using LocalizedModule.induction_on with
    | h m' s' =>
    rw [LocalizedModule.mk_mul_mk, ChartLatQCech.val_mk hT, ChartLatQCech.val_mk hT,
      ChartLatQCech.val_mk hT]
    simp only [Submonoid.coe_mul, map_mul]
    field_simp [hT s s.2, hT s' s'.2]
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, ChartLatQCech.val_mk hT]
    simp
  map_add' := ChartLatQCech.val_add T

theorem exists_section {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (n : K → ℤ)
    (hG : KH.GeneratedV ℚ (KH.genIdeal y) n) : ∃ s ∈ chartLat y n 1, s ≠ 0 := by
  classical
  by_cases hall : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0
  swap
  · push Not at hall
    obtain ⟨k, hk⟩ := hall
    exact ⟨1, fun c hc => absurd (hk (c k)) (hc k), one_ne_zero⟩
  choose c₀ hc₀ using hall
  obtain ⟨r, z, u, hz, -, hsum⟩ := hG (ZeroCocycleSection.chartCell c₀)
  have hT₀ : ∀ t ∈ KH.cellMon ℚ (ZeroCocycleSection.chartCell c₀).1, aeval y t ≠ 0 :=
    ChartLatQCech.cellMon_aevalQ_ne (ZeroCocycleSection.chartCell_good hc₀)
  let f : LocalizedModule (KH.cellMon ℚ (ZeroCocycleSection.chartCell c₀).1)
      (MRingOver ℚ ι ⧸ KH.genIdeal y) →+* Ω := evLHom (y := y) hT₀
  have h1 := congrArg f hsum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one] at h1
  obtain ⟨j, hj⟩ : ∃ j, ChartLatQCech.val y _ (z j (ZeroCocycleSection.chartCell c₀)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∑ j, f (u j * z j (ZeroCocycleSection.chartCell c₀)) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [map_mul]
        show f (u j) * ChartLatQCech.val y _ (z j (ZeroCocycleSection.chartCell c₀)) = 0
        rw [hcon j, mul_zero]
    exact zero_ne_one (h0.symm.trans h1)
  have hZ := hz j
  have hZd := (Submodule.mem_inf.mp hZ).2
  rw [Submodule.restrictScalars_mem, LinearMap.mem_ker] at hZd
  have hZc := (Submodule.mem_inf.mp hZ).1
  unfold KH.cechCc at hZc
  rw [Submodule.mem_pi] at hZc
  have hsQ : ChartLatQCech.val y _ (z j (ZeroCocycleSection.chartCell c₀)) ∈ chartLatQ y n 1 := by
    intro c hc
    simp only [Nat.cast_one, one_mul]
    rw [ChartLatQCech.val_chart_eq hZd hc₀ hc]
    exact ChartLatQCech.val_mul_mem_chartRingQ hc (hZc (ZeroCocycleSection.chartCell c) (Set.mem_univ _))
  obtain ⟨D, hD1, hDmem⟩ := ChartDenominator.proof K ι Ω y n 1 _ hsQ
  exact ⟨(D : Ω) * ChartLatQCech.val y _ (z j (ZeroCocycleSection.chartCell c₀)), hDmem,
    mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hj⟩

end GeneratedNonzeroSection

theorem GeneratedNonzeroSection.proof : GeneratedNonzeroSection.Statement := by
  intro K _ _ ι _ _ Ω _ _ y n hG
  exact GeneratedNonzeroSection.exists_section y n hG

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
