module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv

@[expose] public section

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem HomogeneousComponentMul.proof : HomogeneousComponentMul.Statement := by
  intro σ R _ p a m d hp
  let _ := MvPolynomial.gradedAlgebra (σ := σ) (R := R)
  simp_rw [← decomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_of_left_mem (homogeneousSubmodule σ R) d (b := a)
    ((mem_homogeneousSubmodule m p).mpr hp)

end

end GroundTheory.Heights₂.Heights.RestTerms
