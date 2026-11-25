module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFilteredColimitRingsFinitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

theorem GlobalTheory.EtC.pairingProperties : GlobalTheory.EtC.B1 := by
  intro q J _ _ D c hc n i
  have h := _root_.GlobalTheory.EtC.RingContH.main (ZMod q) (tw q i) (_root_.GlobalTheory.EtC.tw_finitary q i) J D c hc n
  exact ⟨fun x _ => h.1 x, fun j y _ hy => h.2 j y hy⟩
