module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnity

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

alias _root_.GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity := _root_.GlobalTheory.EtC.PrimLoc.prim_loc
