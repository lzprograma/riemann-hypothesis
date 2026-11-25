module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCharZeroAt
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf
open Formalism.MainNotions.G

theorem settingCZ : SettingCharZeroAt := by
  unfold SettingCharZeroAt
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS
  refine ⟨?_, ?_⟩
  · letI : CharZero W := by
      rcases CharP.char_is_prime_or_zero W (ringChar W) with hq | hq
      · exfalso
        by_cases h : ringChar W = p
        · exact hS.p_unif.ne_zero (h ▸ CharP.cast_eq_zero W (ringChar W))
        · apply hS.p_unif.1
          simpa only [ZMod.coe_unitOfCoprime, map_natCast] using
            (ZMod.unitOfCoprime p ((Nat.coprime_primes hS.prime hq).mpr (Ne.symm h))).isUnit.map
              (ZMod.castHom (dvd_refl (ringChar W)) W)
      · letI : CharP W 0 := hq ▸ ringChar.charP W
        exact CharP.charP_to_charZero W
    letI := hS.frac_alt
    exact (RingHom.charZero_iff ι.injective).mp
      (charZero_of_injective_algebraMap (IsFractionRing.injective W Qq))
  · apply (IsLocalRing.mem_maximalIdeal _).mp
    rw [← map_natCast jO p]
    change (p : W) ∈ (IsLocalRing.maximalIdeal O).comap jO
    rw [IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
      jO (RingHom.IsIntegral.of_finite hS.finite) (IsLocalRing.maximalIdeal O))]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hS.p_unif.1

end Formalism.MainNotions.ColumnSystems.Pf
