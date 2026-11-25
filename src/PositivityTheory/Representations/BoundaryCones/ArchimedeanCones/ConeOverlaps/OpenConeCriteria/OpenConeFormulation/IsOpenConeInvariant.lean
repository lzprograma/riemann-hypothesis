module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer
import Mathlib.Analysis.Matrix.Hermitian

@[expose] public section

noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.KcHalf2₂

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt

theorem isOpen_cone_of_hbFacts {n : ℕ} (hH : HbFacts) : IsOpen (cone n) := by
  refine isOpen_iff_mem_nhds.2 fun v₀ hv₀ => ?_
  change (hOf v₀).PosDef at hv₀
  refine ((isCompact_sphere (0 : Fin n → ℂ) 1).eventually_forall_of_forall_eventually
    (P := fun v x => 0 < (star x ⬝ᵥ (hOf v *ᵥ x)).re) ?_).mono ?_
  · intro x hx
    apply ContinuousAt.eventually_lt continuousAt_const
    · unfold hOf
      fun_prop
    · exact (Complex.pos_iff.1 <| hv₀.dotProduct_mulVec_pos (Metric.ne_of_mem_sphere hx one_ne_zero)).1
  · intro v hv
    have hHerm := (hH n).2.2.2.2.1 v
    refine PosDef.of_dotProduct_mulVec_pos hHerm fun x hx => Complex.pos_iff.2
      ⟨?_, (hHerm.im_star_dotProduct_mulVec_self x).symm⟩
    specialize hv (‖x‖⁻¹ • x)
      (mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm (𝕜 := ℝ) hx))
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul] at hv
    simpa [Complex.smul_re, smul_eq_mul, hx] using hv

end PositivityTheory.KcHalf2₂
