module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.CuspEmbP
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.ExhaustionOfSteps
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IrreducibleAdmissibleGL
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IsLAddSegmentOfInjectiveOfNotPrecedes
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtPOfFineUniq
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.NotAboveTransGenSelf
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.SquareIntegrableSegments.SegmentReordering.CsOrderfree
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Mathlib.Topology.Algebra.Group.Units
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocle
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsExhaustionGl
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsFactorsDualReverseOrdered
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSegmentDual
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductHasSocle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.EmbeddingMiddleFactorTriple
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.LUnlinkedIrrOfSeg
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffle

section -- clump:auto
@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace CompanionTheory.Exh

variable (hZ : GlobalTheory.Published.SegmentRepresentation) (hI : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.LUnlinkedIrr k)

include hZ hI in
theorem standardCosocle_of : GlobalTheory.Published.StandardCosocleGL := by
  have hA := irreducibleAdmissibleGL
  intro k _ _ _ _ _ 𝔪 h N x hd hx
  obtain ⟨Γ, hΓ, hL⟩ := _root_.GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual hA (_root_.GlobalTheory.CompanionTheory.SegLDual.lSegDual hA hZ) 𝔪 x hx
  obtain ⟨hd', ⟨e⟩⟩ := _root_.GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr hA x hd
  obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered hA (_root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ) (hI k) (_root_.GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm k hA (hI k)) Γ (fun a => dualCl (x a)) hd' hΓ hL
  exact _root_.GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra hA (prodIrr x hd) (isSmooth_prodIrr x hd) (_root_.GlobalTheory.CompanionTheory.ProdFL.main hA x hd) τ
    (hτ.of_equiv (Representation.Equiv.refl _) e.symm)

include hI in
theorem lOrderFree_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : LOrderFree k :=
  CompanionTheory.PfEss.Zc2.cs_orderfree irreducibleAdmissibleGL (_root_.GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm k irreducibleAdmissibleGL (hI k))

include hI in
theorem lSocleGL_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : LSocleGL k :=
  _root_.GlobalTheory.CompanionTheory.LSocle.lSocleGL irreducibleAdmissibleGL (_root_.GlobalTheory.CompanionTheory.GKLocalProof.gkLocal irreducibleAdmissibleGL) (lOrderFree_of hI k)

include hZ hI in
theorem exhaustion_of_three (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], MidP k ∧ RefineP k ∧ SwapP k) : GlobalTheory.Published.LanglandsExhaustionGL := by
  have hA := irreducibleAdmissibleGL
  refine exhaustion_of_steps fun k _ _ _ _ _ => ?_
  obtain ⟨hM, hR, hS⟩ := H k
  have hC := cuspEmbP_of_refine k hR
  exact ⟨hM, hR, hS, hC, suppP k, juxtP_of_fineUniq hA hM hR hS hC (_root_.GlobalTheory.CompanionTheory.CuspShuffle.inShW_of_wd hA (_root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ)) (_root_.GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec hA hZ),
    linkP, minP, peelGoodP (standardCosocle_of hZ hI) (lSocleGL_of hI k) hR⟩

include hZ hI in
theorem multisegments_of (hE : GlobalTheory.Published.LanglandsExhaustionGL) : GlobalTheory.Published.LanglandsMultisegments :=
  _root_.GlobalTheory.CompanionTheory.LanglandsMultiseg.langlandsMultisegments_of_clauses irreducibleAdmissibleGL (lSocleGL_of hI) (fun _ _ _ _ _ => _root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet irreducibleAdmissibleGL hZ) (lOrderFree_of hI) hE

end CompanionTheory.Exh

end
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

namespace CompanionTheory.Exh

theorem standardCosocleGL_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.StandardCosocleGL :=
  standardCosocle_of hZ (lUnlinkedIrr_of_seg hZ)

theorem langlandsExhaustionGL_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.LanglandsExhaustionGL :=
  exhaustion_of_three hZ (lUnlinkedIrr_of_seg hZ) fun k _ _ _ _ =>
    ⟨midP' k irreducibleAdmissibleGL, refineP' k,
      swapP' k (_root_.GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm k irreducibleAdmissibleGL (lUnlinkedIrr_of_seg hZ k))⟩

theorem langlandsMultisegments_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.LanglandsMultisegments :=
  multisegments_of hZ (lUnlinkedIrr_of_seg hZ) (langlandsExhaustionGL_of_seg hZ)

end CompanionTheory.Exh
end -- clump:auto
end -- clump:auto
