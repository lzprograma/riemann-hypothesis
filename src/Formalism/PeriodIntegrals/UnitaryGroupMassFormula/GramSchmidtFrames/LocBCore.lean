module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.SMulVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.XiHermitianCofactorDet
import Mathlib.Tactic.Lemma
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound

@[expose] public section

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section locb

variable {k r : ℕ}

def omS (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  prW k r z' ((Hpk k r * gᴴ * Hpk k r) *ᵥ xcofL k r z z' g)

lemma omS_eq (z z' : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    omW' k r z z' g = omS k r z z' g := by
  rw [omW', omS, _root_.PI.PolynomialProperness.GN.inv_eq hg]

lemma s_omS (z z' : Fin (2 * r + k + 1) → ℂ) {s : Set (B.Mat k r)} : Sm (fun g => omS k r z z' g) s := by
  unfold omS
  have h1 : Sm (fun g : B.Mat k r => Hpk k r * gᴴ * Hpk k r) s :=
    s_mmul (s_mmul contDiffOn_const (s_ct contDiffOn_id)) contDiffOn_const
  exact s_prW z' (s_mulVec h1 (s_xcofL z z' contDiffOn_id))

end locb

end PI.UnitaryGroupMassFormula.GsFr
