module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertRIndexSteps
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCurveCharts
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionIndexNorm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveSectionQuotFinite
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace SectionQuotientFinite

theorem aeval_ne_zero {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
    {s : MRing (fun _ : Unit => T)} (hs : IsMultiHomog s (fun _ => 1))
    (hsP : s ∉ mCoordIdeal y) : aeval y s ≠ 0 :=
  Targets.CurveSectionQuotientFinite.aeval_ne_zero (K := Unit) (ι := fun _ => T) y hs hsP

end SectionQuotientFinite

theorem SectionQuotFinite.closed : SectionQuotFinite.Statement :=
  fun T _ K' _ _ y s hy hs hsP =>
    Targets.CurveSectionQuotFinite.proof Unit (fun _ => T) K' y s (fun _ => 1) hy hs hsP

end

end GroundTheory.Heights₂.Heights
