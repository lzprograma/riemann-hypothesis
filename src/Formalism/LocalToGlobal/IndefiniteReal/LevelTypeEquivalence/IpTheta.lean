module

import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

variable {D : D7}

section Basic

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem thetaO_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := by
  apply Formalism.IndefR.Fock.CCR.theta_add <;> assumption

theorem thetaO_smul {f : WO S T → ℂ} (c : ℂ) (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by

  obtain ⟨U1, hU1, h1⟩ := hf.level
  constructor
  · intro γ w
    simp only [Pi.smul_apply, smul_eq_mul, hf.quasi]
    ring
  · refine ⟨U1, hU1, fun u hu hfin => ?_⟩
    funext x
    have e1x := congrFun (h1 u hu hfin) x
    simp only [heisO, Pi.smul_apply, smul_eq_mul] at e1x ⊢
    rw [mul_left_comm, e1x]
  · exact hf.cont.const_smul c
  · intro k L hL hfin w
    exact (hf.smooth k L hL hfin w).const_smul c

end Basic

end Formalism.IndefR.Eqv

end
