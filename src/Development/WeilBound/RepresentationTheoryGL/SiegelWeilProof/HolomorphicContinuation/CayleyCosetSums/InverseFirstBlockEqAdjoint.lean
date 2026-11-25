module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolLeadHol
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulConjTransposeEq

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem inverse_first_block_eq_adjoint {x : M2 n} (hx : InG x) : ub1 x = (u1 x)ᴴ :=
  _root_.PositivityTheory.Rg.Sw.LVs.inverse_first_block_eq_of_group hx

theorem secFz : SecFz := by
  intro n m e w y
  have hg : InG (mR y) := y.2
  have key : ∀ r : ℝ, 0 ≤ r → ((r⁻¹ : ℝ) : ℂ) ^ w = (r : ℂ) ^ (-w) := by
    intro r hr
    rw [Complex.ofReal_inv, Complex.inv_cpow, Complex.cpow_neg]
    rw [Complex.arg_ofReal_of_nonneg hr]
    exact Real.pi_ne_zero.symm
  simp only [fz, F0, f0, hLoc, inverse_first_block_eq_adjoint hg, det_conjTranspose]
  rw [key _ (by positivity), Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp

end PositivityTheory.Rg.Sw.HSt
