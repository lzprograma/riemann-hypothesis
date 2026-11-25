module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem component_mul_multiHomog {R : Type*} [CommRing R] {K : Type} [DecidableEq K]
    {ι : K → Type} (y f : MRing ι R) (b s : K → ℕ) (hf : IsMultiHomog f s) :
    weightedHomogeneousComponent (blockWeight ι) b y * f =
      weightedHomogeneousComponent (blockWeight ι) (b + s) (y * f) := by
  classical
  let _ := weightedGradedAlgebra R (blockWeight ι)
  simp_rw [← weightedDecomposition.decompose'_apply]
  exact (DirectSum.coe_decompose_mul_add_of_right_mem (weightedHomogeneousSubmodule R (blockWeight ι))
    (a := y) (i := b) ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf)).symm

theorem ColonMultiHomog.proof : ColonMultiHomog.Statement := by
  intro R _ K _ ι I f s hI hf y hy b
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy ⊢
  rw [component_mul_multiHomog y f b s hf]
  exact hI _ hy _

end GroundTheory.Heights₂.Heights.NumbersDVR
