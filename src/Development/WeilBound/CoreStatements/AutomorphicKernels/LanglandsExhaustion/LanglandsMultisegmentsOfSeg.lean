module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.EmbeddingMiddleFactorTriple
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExhaustionOfThree
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.LUnlinkedIrrOfSeg

@[expose] public section

namespace PositivityTheory.Exh

theorem standardCosocleGL_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.StandardCosocleGL :=
  standardCosocle_of hZ (lUnlinkedIrr_of_seg hZ)

theorem langlandsExhaustionGL_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.LanglandsExhaustionGL := by
  have hU := lUnlinkedIrr_of_seg hZ
  exact exhaustion_of_three hZ hU fun k _ _ _ _ =>
    ⟨CompanionTheory.Exh.midP' k irreducibleAdmissibleGL, CompanionTheory.Exh.refineP' k,
      CompanionTheory.Exh.swapP' k (GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm k irreducibleAdmissibleGL (hU k))⟩

theorem langlandsMultisegments_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.LanglandsMultisegments :=
  multisegments_of hZ (lUnlinkedIrr_of_seg hZ) (langlandsExhaustionGL_of_seg hZ)

end PositivityTheory.Exh
