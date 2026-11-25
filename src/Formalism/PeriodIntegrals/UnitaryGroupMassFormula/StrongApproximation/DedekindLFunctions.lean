module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.LocSmall
public import Lemmata.Cancellation.EnnrealVolumeRatioStepCancel
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField

namespace PI.StrongApproxE

namespace DedekindLFunctions

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

alias sa := _root_.Bl.VolumeRatioCancellation.goal1

end DedekindLFunctions

theorem strong_approximation_finite_places : DedSA := by
  intro F _ _ T a c hc
  exact DedekindLFunctions.sa (R := 𝓞 F) (K := F) T a c hc

end PI.StrongApproxE
