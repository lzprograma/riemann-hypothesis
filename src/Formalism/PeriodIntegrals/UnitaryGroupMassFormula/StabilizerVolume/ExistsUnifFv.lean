module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.FibExGram
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExistsUnifFv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVDxSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfCo
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.EventuallySmulSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct

section HermMod

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

export PI.VolStabSW (sigR_algebraMap hR_smul_left hR_smul_right)

instance hermSMul (σ : E →ₐ[F] E) (n : ℕ) : SMul R (HermR R σ n) :=
  ⟨fun t S => ⟨t • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), by
    intro a b
    have h := S.2 a b
    simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap]
    rw [h]⟩⟩

export PI.VolStabSW (coe_hermSMul)

instance hermModule (σ : E →ₐ[F] E) (n : ℕ) : Module R (HermR R σ n) :=
  Function.Injective.module R (HermR R σ n).subtype Subtype.coe_injective (fun _ _ => rfl)

end HermMod

export PI.VolStabSW (exists_unif_Fv)

theorem gramFilt_of (hDx : DxOpen) : GramFilt := by
  intro F E _ _ _ _ σ hσ M J hJ hdet a ha1 _ v d b x hx
  letI : FiniteDimensional F E := Module.Finite.of_basis b
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  letI : NumberField E :=
    { to_charZero := inferInstance
      to_finiteDimensional := Module.Finite.trans F E }
  exact PI.VolStabSW.OmFibG.gramFilt_gen σ hσ M J hJ hdet a ha1 v d b x hx

end PI.VolStabS
