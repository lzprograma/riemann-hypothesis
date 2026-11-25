module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocAwaySpec
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section
set_option maxSynthPendingDepth 1
noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Classical in
theorem LocAwaySpec.proof : LocAwaySpec.Statement := by
  intro R _ Φ _ φ S hrep
  choose f g hg hfg using hrep
  let E := ∏ c ∈ S, g c
  have hE : IsUnit (φ E) := by
    simpa only [E, map_prod] using (Finset.prod_ne_zero_iff.mpr fun c (_ : c ∈ S) => hg c).isUnit
  refine ⟨E, hE, ?_, ?_⟩
  · intro c hc
    let u := (isUnit_of_dvd_unit (map_dvd (algebraMap R (Localization.Away E))
      (Finset.dvd_prod_of_mem g hc)) (IsLocalization.Away.algebraMap_isUnit E)).unit
    refine ⟨algebraMap R (Localization.Away E) (f c) * ↑u⁻¹, ?_⟩
    simpa only [u, map_mul, map_units_inv, IsUnit.unit_spec, IsLocalization.Away.lift_eq,
      ← div_eq_mul_inv] using (hfg c).symm
  · intro B _ ψ hψ hker z hz
    rw [RingHom.mem_ker] at hz ⊢
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers E) z
    apply ((IsLocalization.map_units (Localization.Away E) s).map
      (IsLocalization.Away.lift E hψ : Localization.Away E →+* B)).mul_left_eq_zero.mp
    rw [← map_mul, hs, IsLocalization.Away.lift_eq]
    exact hker (RingHom.mem_ker.mpr (by
      simpa only [map_mul, IsLocalization.Away.lift_eq, hz, zero_mul] using
        congrArg (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) hs.symm))

end GroundTheory.Heights₂.Heights.Inter
