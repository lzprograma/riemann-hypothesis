module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ServedPrimeProperties
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoeffProdRename

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix

namespace GlobalTheory.TwU.XdInert

theorem gidx_facts : ∀ (D : D7) (T p : ℕ), GIdx D.host T p →
    5 ≤ p ∧ GL3Theta.InertK D p ∧ Nat.Coprime T p ∧ ∀ i, p ≠ D.host.g i := by
  intro D T p h
  obtain ⟨hp, h5, hc, hn, hl, hT⟩ := h
  refine ⟨h5, ?_, ?_, ?_⟩
  · exact (GlobalTheory.TwU.Served.served_facts D p hp hc hn).2.1
  · exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hT).symm
  · intro i hi
    exact hl (hi ▸ D.host.g_level i)

end GlobalTheory.TwU.XdInert
