module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.LocMod.LinTheta

theorem isThetaFunO_placeModel (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (ΛS : Lat S) (ΛT : Lat T)
    (e : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (he : IsSplitIdem D e) (hf : IsThetaFunO ψ S T f₀)
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm)
    (Φ : WO S T → ℂ)
    (hΦ : IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) Φ) : IsThetaFunO ψ S T (Tm Φ) := by
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT
  exact GlobalTheory.DiagLiftFix.isTheta_placeModel hψ inferInstance inferInstance he.1 he.2.1 (_root_.GlobalTheory.PlaceModelSum.infPart_split he) hf Tm hTm Φ hΦ

end GlobalTheory.LocMod.LinTheta
