module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorIsFinitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistRingFunctorPreservesFilteredColimits

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem UpperTheory.Cb.tateTwist_finitary :
    ∀ (q : ℕ) (i : ℤ), Finitary (R := ZMod q) (tw q i) := by
  intro q i
  exact _root_.GlobalTheory.ofRings_finitary (ZMod q) (twF q i) (_root_.GlobalTheory.EtC.TwistFiltered.twF_preservesFilteredColimits q i)
