module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibDis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqZeroOfSetIntegral

@[expose] public section

noncomputable section

namespace PI.VolStabS.FibUniq

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal

section Gen

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
    ∫ v, φ v ∂(fib1 b) = ∫ v, φ v ∂(fib2 b) := by
  have c1 := (h1.2.2 φ hφc hφs hφU).2
  have c2 := (h2.2.2 φ hφc hφs hφU).2
  have h0 : ∀ S, IsCompact S → S ⊆ univ →
      ∫ b in S, (∫ v, φ v ∂(fib1 b) - ∫ v, φ v ∂(fib2 b)) ∂ν = 0 := by
    intro S hS _
    rw [integral_sub ((c1.mono (subset_univ S)).integrableOn_compact hS)
      ((c2.mono (subset_univ S)).integrableOn_compact hS),
      ← PI.VolStabS.DensGen.fib_set h1 hf' hff' hι φ hφc hφs hφU S hS (subset_univ S),
      ← PI.VolStabS.DensGen.fib_set h2 hf' hff' hι φ hφc hφs hφU S hS (subset_univ S), sub_self]
  exact sub_eq_zero.1 (PI.VolStabS.DensGen.eq_zero_of_setIntegral (ν := ν)
    (fun b => ∫ v, φ v ∂(fib1 b) - ∫ v, φ v ∂(fib2 b)) univ b univ_mem (c1.sub c2) h0)

theorem fin_cpt {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U)
    (b : X) (K : Set V) (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ := by
  obtain ⟨g, hg1, hgc, hgs, _⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  have hI := (h.2.2 g g.continuous hgc hgs).1 b (mem_univ b)
  calc fib b K = ∫⁻ v, K.indicator 1 v ∂(fib b) := (lintegral_indicator_one hK.measurableSet).symm
    _ ≤ ∫⁻ v, ENNReal.ofReal (g v) ∂(fib b) := lintegral_mono fun v => by
        by_cases hv : v ∈ K
        · simp [indicator_of_mem hv, hg1 hv]
        · simp [indicator_of_notMem hv]
    _ < ⊤ := hI.lintegral_lt_top

theorem open_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (O : Set V) (hO : IsOpen O)
    (hOU : O ⊆ U) (b : X) : fib1 b O = fib2 b O := by
  apply +allowSynthFailures _root_.PI.AprimeInfW.FU.open_eq <;> assumption

theorem fib_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hU : IsOpen U) : fib1 = fib2 := by
  apply +allowSynthFailures _root_.PI.AprimeInfW.FU.fib_eq <;> assumption

end Gen

section Tens

open scoped TensorProduct
open PI.VolStabS PI.VolStabS.TensAllW

theorem fib_eq_tens {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (fib1 fib2 : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E))
    (h1 : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib1)
    (h2 : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib2) : fib1 = fib2 :=
  fib_eq h1 h2 (continuous_gramH R σ hσ J hJ) (fun _ => rfl) Subtype.val_injective
    (isOpen_linIndep (Module.finBasis F E) R hU hL)

end Tens

end PI.VolStabS.FibUniq
