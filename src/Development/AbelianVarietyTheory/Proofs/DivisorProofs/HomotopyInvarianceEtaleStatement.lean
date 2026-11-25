module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceEtale

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

alias _root_.GlobalTheory.T.homotopy_invariance_etale_alt := _root_.GlobalTheory.EtC.HomotopyInv.homotopy_invariance_etale
