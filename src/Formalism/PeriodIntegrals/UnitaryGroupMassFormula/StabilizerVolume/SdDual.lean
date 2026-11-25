module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

@[expose] public section

noncomputable section

namespace PI.VolStabS

namespace SdDualW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

export PI.VolStabSW.SdDualW (latSub crd_smul sigR_smul BR_smul_left BR_add_right BR_smul_right)

section Nondeg

variable [FiniteDimensional F E]

export PI.VolStabSW.SdDualW (trace_one_tmul)


end Nondeg

section Dual

variable [FiniteDimensional F E] (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)

export PI.VolStabSW.SdDualW (eT eT_mem sum_eT BR_expand phiL)

include b in
theorem dualAt_alt
    (hN : ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, (∀ X, BR (Fv F v) σ J X Y = 0) → Y = 0) :
    DualAt v (BR (Fv F v) σ J (n := a)) := by
  apply PI.VolStabSW.SdDualW.dualAt_alt <;> assumption

end Dual

section NondegBR

variable [FiniteDimensional F E]

export PI.VolStabSW.SdDualW (nondeg_BR)

end NondegBR

section Herm

variable [FiniteDimensional F E]

export PI.VolStabSW.SdDualW (latA isOpen_latA isCompact_latA latS iota iota_mem pairHerm_iota dualAt_H)

end Herm

end SdDualW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW

def DualHV : Prop := InCtx fun F E _ _ _ _ _ σ _M _J a _X0 _hT =>
  ∀ v : HeightOneSpectrum (𝓞 F), DualAt v (pairHerm (Fv F v) σ a)

theorem dualLatV_of (hH : DualHV) : DualLatV := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  refine ⟨?_, hH F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v⟩
  exact SdDualW.dualAt_alt v (Module.finBasis F E) σ J
    (fun Y hY => SdDualW.nondeg_BR v σ hσ J hJ.2 Y hY)

theorem dualHV_holds : DualHV := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact SdDualW.dualAt_H v (Module.finBasis F E) σ (sigma_invol σ hCM.2.2.2) a

theorem dualLatV_holds : DualLatV := dualLatV_of dualHV_holds

theorem sdUniq_of_inf (hI : SdTestInf) : SdUniq := sdUniq_of_dual hI dualLatV_holds

end PI.VolStabS
