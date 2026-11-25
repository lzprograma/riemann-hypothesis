module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import GroundTheory.LocalFields.PadicLogSeries
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.ProdFL

theorem hasFiniteLength_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) : HasFiniteLength (prodIrr x hd) :=
  _root_.GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)
    (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA x))

alias main := _root_.GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr

end GlobalTheory.CompanionTheory.ProdFL

end
