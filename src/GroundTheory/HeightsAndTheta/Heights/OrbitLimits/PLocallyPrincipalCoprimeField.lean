module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsInvertibleIndexMulSteps
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLocallyPrincipalCoprime
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt

theorem LocallyPrincipalCoprimeField.proof : LocallyPrincipalCoprimeField.Statement :=
  fun _ _ _ B M ι _ a hfin hBM haM hden hloc hM s hs =>
    LocallyPrincipalCoprime.proof_of_charZero B M ι a hfin hBM haM hden hloc hM s hs

end GroundTheory.Heights₂.Heights.Targets
