module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GrowthUnitaryGroupRpowNegIntegrable
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.MeasurableSpace

@[expose] public section

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.QuantumDeterminants

theorem gN_nonneg_bessel_integrability {k r : ℕ} (x : Formalism.FourierDecayAlt.B.Mat k r) : 0 ≤ Formalism.FourierDecayAlt.B.gN x := Real.sqrt_nonneg _

theorem growth_group_bound : Formalism.FourierDecayAlt.ThreeDimData.GrowthG := by
  apply _root_.GlobalTheory.gN_rpow_neg_integrable_haar <;> assumption

end Formalism.FourierDecayAlt.P
