module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem lowerLeftValuation_eq_zero_all_stages_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ValLL0 (Dof x) (cfOf x) := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x => ?_
  exact valLL0_colW w x.o.Z
end GlobalTheory.HeightCounting.Up
end
end
