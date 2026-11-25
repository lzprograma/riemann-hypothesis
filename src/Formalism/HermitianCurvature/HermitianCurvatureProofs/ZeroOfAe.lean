module

import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Mathlib.Tactic.TypeStar

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section



namespace Formalism.FourierDecayAlt.P

namespace UnipotentHaarMeasurability

variable {k r : ℕ}

local notation "MX" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
local notation "UHk" => Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)

theorem uh_meas : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
  apply _root_.Formalism.MainNotions.BesselShellMomentBounds.measurableSet_UH <;> assumption

end UnipotentHaarMeasurability

end Formalism.FourierDecayAlt.P
