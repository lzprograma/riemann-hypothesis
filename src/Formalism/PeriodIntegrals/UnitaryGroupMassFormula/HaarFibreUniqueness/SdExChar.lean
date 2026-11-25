module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.AdditiveCharacterNontrivial
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.CompletePartialOrder

@[expose] public section

noncomputable section

namespace PI.OmFibreUniq.W.SdChar

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter NumberField IsDedekindDomain

theorem eq_one_of_pow_near (w : ℂ) (hw : ‖w‖ = 1) (h : ∀ m : ℕ, ‖w ^ m - 1‖ < 1) : w = 1 := by
  apply PI.OmFibreUniq.W.Sd.eq_one_of_pow_near <;> assumption

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  (ψ0 : Fv F v → ℂ) (hψc : Continuous ψ0) (hψa : ∀ r s, ψ0 (r + s) = ψ0 r * ψ0 s)
  (hψn : ∀ r, ‖ψ0 r‖ = 1)

include hψa hψn in
theorem psi_zero : ψ0 0 = 1 := by
  have h := hψa 0 0
  rw [add_zero] at h
  have hne : ψ0 0 ≠ 0 := by
    intro h0
    have := hψn 0
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have h2 : ψ0 0 * (ψ0 0 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hne)


include hψa hψn in
theorem psi_natCast_mul (m : ℕ) (t : Fv F v) : ψ0 ((m : Fv F v) * t) = ψ0 t ^ m := by
  induction m with
  | zero => simp [psi_zero v ψ0 hψa hψn]
  | succ m ih =>
    rw [Nat.cast_succ, add_mul, one_mul, hψa, ih, pow_succ]

def Aset : Set (Fv F v) := {t | ∀ c ∈ v.adicCompletionIntegers F, ψ0 (c * t) = 1}

include hψc hψa hψn in
theorem Aset_mem_nhds : Aset v ψ0 ∈ 𝓝 (0 : Fv F v) := by
  have h0 : ψ0 0 = 1 := psi_zero v ψ0 hψa hψn
  have hU : {x | ‖ψ0 x - 1‖ < 1} ∈ 𝓝 (0 : Fv F v) := by
    apply (isOpen_lt (hψc.sub continuous_const).norm continuous_const).mem_nhds
    simp [h0]
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU
  apply Filter.mem_of_superset (Valued.mem_nhds_zero.mpr ⟨γ, subset_rfl⟩)
  intro t ht c hc
  have hin : ∀ c' ∈ v.adicCompletionIntegers F, ‖ψ0 (c' * t) - 1‖ < 1 := by
    intro c' hc'
    apply hγ
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valuation.restrict_le_one_iff] at hc'
    simp only [Set.mem_setOf_eq, map_mul]
    calc Valued.v.restrict c' * Valued.v.restrict t ≤ 1 * Valued.v.restrict t := by gcongr
      _ = Valued.v.restrict t := one_mul _
      _ < _ := ht
  apply eq_one_of_pow_near _ (hψn _)
  intro m
  rw [← psi_natCast_mul v ψ0 hψa hψn, ← mul_assoc]
  exact hin _ (mul_mem (natCast_mem _ m) hc)

include hψa hψn in
theorem Aset_bdd (hnt : ∃ y, ψ0 y ≠ 1) :
    ∃ y0 : Fv F v, y0 ≠ 0 ∧ ∀ t ∈ Aset v ψ0, ∃ s ∈ v.adicCompletionIntegers F, t = y0 * s := by
  obtain ⟨y, hy⟩ := hnt
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (psi_zero v ψ0 hψa hψn)
  refine ⟨y, hy0, fun t ht => ⟨t / y, ?_, by field_simp⟩⟩
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  by_cases ht0 : t = 0
  · simp [ht0]
  rcases le_total (Valued.v (t / y)) 1 with hle | hge
  · exact hle
  · exfalso
    apply hy
    have hne : Valued.v (t / y) ≠ 0 := (Valuation.ne_zero_iff _).2 (div_ne_zero ht0 hy0)
    have hc : y / t ∈ v.adicCompletionIntegers F := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← inv_div, map_inv₀]
      calc (Valued.v (t / y))⁻¹ = (Valued.v (t / y))⁻¹ * 1 := (mul_one _).symm
        _ ≤ (Valued.v (t / y))⁻¹ * Valued.v (t / y) := by gcongr
        _ = 1 := inv_mul_cancel₀ hne
    have := (show ∀ c ∈ v.adicCompletionIntegers F, ψ0 (c * t) = 1 from ht) _ hc
    rwa [div_mul_cancel₀ _ ht0] at this

end PI.OmFibreUniq.W.SdChar
