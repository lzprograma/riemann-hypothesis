module
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousPsiVOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousTrESymm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensFibV

@[expose] public section
noncomputable section
namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

theorem piu_inv_not_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (piu v)⁻¹ ∉ v.adicCompletionIntegers F := by
  intro h
  obtain ⟨k, hk⟩ := (tube v (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v)
    (show {x : Fv F v | x ≠ 1} ∈ 𝓝 (0 : Fv F v) from isOpen_ne.mem_nhds zero_ne_one)).exists
  apply hk _ (pow_mem h k)
  simp [smul_eq_mul, mul_inv_cancel₀ (pow_ne_zero k (piu_ne v))]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)
theorem finrank_pos' : 0 < Module.finrank F E := Module.finrank_pos

theorem exists_not_mem_oev : ∃ t0 : Fv F v ⊗[F] E, t0 ∉ OEv (E := E) v := by
  classical
  let i0 : Fin (Module.finrank F E) := ⟨0, finrank_pos'⟩
  obtain ⟨k, hk⟩ := (tube v
    ((isCompact_oev (E := E) v).image ((continuous_apply i0).comp (continuous_trE v)))
    (show (v.adicCompletionIntegers F : Set (Fv F v)) ∈ 𝓝 (0 : Fv F v) from
      (Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _))).exists
  refine ⟨(trE (E := E) v).symm (Pi.single i0 (piu v ^ (k + 1))⁻¹), fun h => piu_inv_not_mem v ?_⟩
  rw [show (piu v)⁻¹ = piu v ^ k • (piu v ^ (k + 1))⁻¹ by
    rw [smul_eq_mul, pow_succ]; field_simp [piu_ne v]]
  exact hk _ ⟨_, h, by simp⟩
variable [SecondCountableTopology (Fv F v ⊗[F] E)]
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
