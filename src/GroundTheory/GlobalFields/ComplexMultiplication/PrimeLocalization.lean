module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain

noncomputable section

variable (L : Type*) [Field L] [NumberField L]

def localizationAt (v : HeightOneSpectrum (𝓞 L)) : Subalgebra (𝓞 L) L :=
  Localization.subalgebra.ofField L v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors

variable {L}

instance (v : HeightOneSpectrum (𝓞 L)) : IsLocalization.AtPrime (localizationAt L v) v.asIdeal :=
  Localization.subalgebra.isLocalization_ofField _ _ _

instance (v : HeightOneSpectrum (𝓞 L)) : IsDiscreteValuationRing (localizationAt L v) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) v.ne_bot _

theorem mem_localizationAt_iff {v : HeightOneSpectrum (𝓞 L)} {x : L} :
    x ∈ localizationAt L v ↔ ∃ a s : 𝓞 L, s ∉ v.asIdeal ∧
      x = algebraMap (𝓞 L) L a * (algebraMap (𝓞 L) L s)⁻¹ := by
  unfold localizationAt Localization.subalgebra.ofField
  rw [← SetLike.mem_coe, Subalgebra.coe_copy]
  simp only [Set.mem_ofPred_eq, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_compl_iff, SetLike.mem_coe, exists_prop]

theorem finite_setOf_mem_asIdeal {b : 𝓞 L} (hb : b ≠ 0) :
    {v : HeightOneSpectrum (𝓞 L) | b ∈ v.asIdeal}.Finite :=
  (Ideal.finite_factors (I := Ideal.span {b}) (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])).subset
    fun _ hv => Ideal.dvd_span_singleton.mpr hv

theorem eventually_mem_localizationAt (x : L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite, x ∈ localizationAt L v := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  refine Filter.eventually_cofinite.mpr
    ((finite_setOf_mem_asIdeal (nonZeroDivisors.ne_zero hb)).subset fun v hv => ?_)
  by_contra h
  exact hv (mem_localizationAt_iff.mpr ⟨a, b, h, div_eq_mul_inv _ _⟩)


theorem eventually_isUnit_localizationAt {x : L} (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ h : x ∈ localizationAt L v, IsUnit (⟨x, h⟩ : localizationAt L v) := by
  filter_upwards [eventually_mem_localizationAt x, eventually_mem_localizationAt x⁻¹] with v h h'
  exact ⟨h, (Submonoid.isUnit_iff_of_ne_zero hx).2 h'⟩

end

end GroundTheory.Global
