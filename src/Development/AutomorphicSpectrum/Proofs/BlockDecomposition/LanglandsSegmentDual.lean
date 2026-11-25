module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientSegmentProductEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProduct
import GroundTheory.LocalFields.PadicLogSeries

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegLDual

theorem lSegDual : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (_ : GlobalTheory.Published.IrreducibleAdmissibleGL) (_ : GlobalTheory.Published.SegmentRepresentation), LSegDual k := by
  intro k _ _ _ _ hA hZ Δ N V _ _ π hπ
  obtain ⟨hd, hco⟩ := id hπ
  have hsm : IsSmooth π := hco.isSubquotient.isSmooth (isSmooth_prodIrr _ hd)
  obtain ⟨hirr, f, hf, -⟩ := hco
  have hci : (contra π).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k N) (hA k N V π hsm hirr) hirr
  obtain ⟨hd', ⟨e⟩⟩ := _root_.GlobalTheory.CompanionTheory.SegIncDual.contra_prodIrr_term hA Δ hd
  have hinj : Function.Injective (GlobalTheory.ContraRefl.contraMap f) := fun a b h => Subtype.ext (LinearMap.ext fun v => by
    obtain ⟨w, rfl⟩ := hf v
    exact LinearMap.congr_fun (congrArg Subtype.val h) w)
  exact _root_.GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec hA hZ (segDual Δ) hd' (contra π) (isSmooth_smoothRep _) hci
    (e.toIntertwiningMap.comp (GlobalTheory.ContraRefl.contraMap f))
    (e.toLinearEquiv.injective.comp hinj)

end GlobalTheory.CompanionTheory.SegLDual

end
