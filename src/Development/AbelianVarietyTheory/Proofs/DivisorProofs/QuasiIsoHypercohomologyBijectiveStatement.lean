module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijective

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.quasiIso_hypercohomology_bijective : GlobalTheory.EtC.A1 := by
  first | (exact @GlobalTheory.EtC.quasiIso_hypercohomology_bijective')
