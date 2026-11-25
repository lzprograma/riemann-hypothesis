module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultisetSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

alias UpperTheory.V.AlgRepEndIrreducible.msetSep := _root_.UpperTheory.Reformulated.B.MultisetSeparation.msetSep
