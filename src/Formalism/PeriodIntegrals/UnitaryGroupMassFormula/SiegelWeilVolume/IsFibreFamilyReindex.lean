module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibDis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqZeroOfSetIntegral
import Aesop.Main
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.CompletePartialOrder
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll

@[expose] public section

noncomputable section

namespace PI.VolStabSW.DensGen

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}

theorem ae_fib (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X}
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (b : X) :
    ∀ᵐ v ∂(fib b), f' v = b :=
  PI.AprimeInfW.DG.ae_fib hfib hff' hι b

theorem fib_set_nonneg [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hρ0 : ∀ v, 0 ≤ ρ v) (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν :=
  PI.AprimeInfW.DG.fib_set_nonneg hfib hf' hff' hι ρ hρc hρs hρU hρ0 S hS hSB

theorem fib_set [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν :=
  PI.AprimeInfW.DG.fib_set hfib hf' hff' hι ρ hρc hρs hρU S hS hSB

theorem eq_zero_of_setIntegral [LocallyCompactSpace X] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] (D : X → ℝ) (W : Set X) (b0 : X) (hW : W ∈ 𝓝 b0)
    (hD : ContinuousOn D W) (h0 : ∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) :
    D b0 = 0 :=
  PI.AprimeInfW.DG.eq_zero_of_setIntegral D W b0 hW hD h0

end PI.VolStabSW.DensGen

namespace PI.DegenerateSiegelWeil.FibUniq

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib1 fib2 : X → Measure V}

theorem integral_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (φ : V → ℝ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (b : X) :
    ∫ v, φ v ∂(fib1 b) = ∫ v, φ v ∂(fib2 b) :=
  PI.AprimeInfW.FU.integral_eq h1 h2 hf' hff' hι φ hφc hφs hφU b

theorem fin_cpt {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U)
    (b : X) (K : Set V) (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ :=
  PI.AprimeInfW.FU.fin_cpt h hU b K hK hKU

theorem open_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (O : Set V) (hO : IsOpen O)
    (hOU : O ⊆ U) (b : X) : fib1 b O = fib2 b O :=
  PI.AprimeInfW.FU.open_eq h1 h2 hf' hff' hι O hO hOU b

theorem fib_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hU : IsOpen U) : fib1 = fib2 :=
  PI.AprimeInfW.FU.fib_eq h1 h2 hf' hff' hι hU

end PI.DegenerateSiegelWeil.FibUniq

namespace PI.DegenerateSiegelWeil.Scale

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal NNReal

section Reindex

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

theorem isFibreFamily_reindex (e : V ≃ₜ V) (h : X ≃ₜ X) {f' : V → X}
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (heh : ∀ v, f' (e v) = h (f' v)) (hU : e ⁻¹' U = U) {cμ cν : ℝ≥0∞}
    (hμ : μ.map e = cμ • μ) (hν : ν.map h.symm = cν • ν)
    (hfib : IsFibreFamily μ f ι U ν univ fib) :
    IsFibreFamily ((cμ * cν) • μ) f ι U ν univ
      (fun b => (fib (h.symm b)).map e.toMeasurableEquiv) := by
  obtain ⟨h1, h2, h3⟩ := hfib
  have hme : ⇑e.toMeasurableEquiv = ⇑e := rfl
  have hμ' : μ.map e.toMeasurableEquiv = cμ • μ := hμ
  have hν' : ν.map h.symm.toMeasurableEquiv = cν • ν := hν
  have hpre : ∀ b, e ⁻¹' (f ⁻¹' {ι b} ∩ U) = f ⁻¹' {ι (h.symm b)} ∩ U := by
    intro b
    ext v
    have hUv : e v ∈ U ↔ v ∈ U := by
      conv_rhs => rw [← hU]
      exact Iff.rfl
    simp only [mem_preimage, mem_inter_iff, mem_singleton_iff, hff', heh, hι.eq_iff, hUv]
    rw [h.eq_symm_apply]
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · rw [MeasurableEquiv.map_apply, preimage_compl, hme, hpre]
    exact h1 (h.symm b)
  · rw [Measure.restrict_smul, lintegral_smul_measure]
    have hφe : Measurable (φ ∘ e) := hφ.comp e.continuous.measurable
    have key1 : ∫⁻ v in U, (φ ∘ e) v ∂μ = cμ * ∫⁻ v in U, φ v ∂μ := by
      have h0 : ∫⁻ v in U, φ v ∂(μ.map e.toMeasurableEquiv) = ∫⁻ v in U, (φ ∘ e) v ∂μ := by
        rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, hme, hU]
        rfl
      rw [← h0, hμ', Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    have key2 : ∫⁻ b, ∫⁻ v, φ v ∂(fib (h.symm b)).map e.toMeasurableEquiv ∂ν =
        cν * ∫⁻ b, ∫⁻ v, (φ ∘ e) v ∂fib b ∂ν := by
      simp only [lintegral_map_equiv]
      rw [← smul_eq_mul, ← lintegral_smul_measure, ← hν', lintegral_map_equiv]
      rfl
    rw [key2, ← h2 _ hφe, key1, smul_eq_mul]
    ring
  · have hφe_c : Continuous (φ ∘ e) := hφc.comp e.continuous
    have hφe_s : HasCompactSupport (φ ∘ e) := hφs.comp_homeomorph e
    have hsub : tsupport (φ ∘ e) ⊆ e ⁻¹' tsupport φ :=
      closure_minimal (fun v hv => subset_tsupport φ hv) ((isClosed_tsupport φ).preimage e.continuous)
    have hφe_U : tsupport (φ ∘ e) ⊆ U := by
      intro v hv
      rw [← hU]
      exact hφU (hsub hv)
    obtain ⟨hi, hcont⟩ := h3 _ hφe_c hφe_s hφe_U
    refine ⟨fun b _ => ?_, ?_⟩
    · rw [integrable_map_equiv]
      exact hi _ (mem_univ _)
    · have hfun : (fun b => ∫ v, φ v ∂(fib (h.symm b)).map e.toMeasurableEquiv) =
          (fun b' => ∫ v, (φ ∘ e) v ∂fib b') ∘ h.symm := by
        funext b
        simp only [Function.comp_apply, integral_map_equiv]
        rfl
      rw [hfun]
      exact ((continuousOn_univ.1 hcont).comp h.symm.continuous).continuousOn

theorem isFibreFamily_smul {B : Set X} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hfib : IsFibreFamily μ f ι U ν B fib) :
    IsFibreFamily (c • μ) f ι U ν B (fun b => c • fib b) := by
  obtain ⟨h1, h2, h3⟩ := hfib
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · simp only [Measure.smul_apply, h1 b, smul_zero]
  · rw [Measure.restrict_smul, lintegral_smul_measure, h2 φ hφ, smul_eq_mul, ← lintegral_const_mul' _ _ hc]
    simp only [lintegral_smul_measure, smul_eq_mul]
  · obtain ⟨hi, hcont⟩ := h3 φ hφc hφs hφU
    refine ⟨fun b hb => (hi b hb).smul_measure hc, ?_⟩
    simp only [integral_smul_measure, smul_eq_mul]
    exact continuousOn_const.mul hcont

end Reindex

section Uniq

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

theorem fib_reindex_eq (e : V ≃ₜ V) (h : X ≃ₜ X) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hUo : IsOpen U)
    (heh : ∀ v, f' (e v) = h (f' v)) (hU : e ⁻¹' U = U) {cμ cν : ℝ≥0∞} (hcμ : cμ ≠ ⊤)
    (hcν : cν ≠ ⊤) (hμ : μ.map e = cμ • μ) (hν : ν.map h.symm = cν • ν)
    (hfib : IsFibreFamily μ f ι U ν univ fib) (b : X) :
    (fib (h.symm b)).map e.toMeasurableEquiv = (cμ * cν) • fib b := by
  have hc : cμ * cν ≠ ⊤ := ENNReal.mul_ne_top hcμ hcν
  haveI : IsFiniteMeasureOnCompacts ((cμ * cν) • μ) := IsFiniteMeasureOnCompacts.smul μ hc
  have := PI.DegenerateSiegelWeil.FibUniq.fib_eq (isFibreFamily_reindex e h hff' hι heh hU hμ hν hfib)
    (isFibreFamily_smul hc hfib) hf' hff' hι hUo
  exact congrFun this b

theorem fib_map_fixed (e : V ≃ₜ V) (h : X ≃ₜ X) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hUo : IsOpen U)
    (heh : ∀ v, f' (e v) = h (f' v)) (hU : e ⁻¹' U = U) {cμ cν : ℝ≥0∞} (hcμ : cμ ≠ ⊤)
    (hcν : cν ≠ ⊤) (hμ : μ.map e = cμ • μ) (hν : ν.map h.symm = cν • ν)
    (hfib : IsFibreFamily μ f ι U ν univ fib) (b : X) (hb : h b = b) :
    (fib b).map e.toMeasurableEquiv = (cμ * cν) • fib b := by
  have hb' : h.symm b = b := h.symm_apply_eq.2 hb.symm
  have := fib_reindex_eq e h hf' hff' hι hUo heh hU hcμ hcν hμ hν hfib b
  rwa [hb'] at this

end Uniq

end PI.DegenerateSiegelWeil.Scale
