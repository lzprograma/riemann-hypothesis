module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.WtDegConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvariance
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds

@[expose] public section

namespace UpperTheory.Gal.TranscendenceTraces

theorem adic : Adic := adic_holds _root_.GlobalTheory.EtC.a8

theorem all_holds : Weights ∧ Torsion ∧ Adic := ⟨weights_holds, torsion_holds, adic⟩

end UpperTheory.Gal.TranscendenceTraces
