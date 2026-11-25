module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussC

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem isSiegel_I : IsSiegel (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold IsSiegel
  have hs : -(Complex.I / 2) * (Complex.I - star Complex.I) = 1 := by
    rw [Complex.star_def, Complex.conj_I]
    linear_combination (-1 : ℂ) * Complex.I_sq
  rw [conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul, hs, one_smul]
  exact Matrix.PosDef.one

theorem toBlocks₁₁_mul (M N : M2 n) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ := by
  have := congrArg toBlocks₁₁ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₁₁] using this

theorem toBlocks₁₂_mul (M N : M2 n) : (M * N).toBlocks₁₂ = M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂ := by
  have := congrArg toBlocks₁₂ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₁₂] using this

theorem toBlocks₂₁_mul (M N : M2 n) : (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ := by
  have := congrArg toBlocks₂₁ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₂₁] using this

theorem toBlocks₂₂_mul (M N : M2 n) : (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  have := congrArg toBlocks₂₂ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₂₂] using this

theorem mR_mul (y y' : GR n) : mR (y * y') = mR y * mR y' := rfl

theorem inG_mR (y : GR n) : InG (mR y) := y.2

theorem num_den_mul (M N : M2 n) (Z W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) = N.toBlocks₁₁ * Z + N.toBlocks₁₂) :
    (M * N).toBlocks₁₁ * Z + (M * N).toBlocks₁₂ = (M.toBlocks₁₁ * W + M.toBlocks₁₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) ∧
    (M * N).toBlocks₂₁ * Z + (M * N).toBlocks₂₂ = (M.toBlocks₂₁ * W + M.toBlocks₂₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) := by
  rw [toBlocks₁₁_mul, toBlocks₁₂_mul, toBlocks₂₁_mul, toBlocks₂₂_mul]
  constructor
  · have e : (M.toBlocks₁₁ * W + M.toBlocks₁₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) =
        M.toBlocks₁₁ * (W * (N.toBlocks₂₁ * Z + N.toBlocks₂₂)) +
          M.toBlocks₁₂ * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) := by noncomm_ring
    rw [e, hW]
    noncomm_ring
  · have e : (M.toBlocks₂₁ * W + M.toBlocks₂₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) =
        M.toBlocks₂₁ * (W * (N.toBlocks₂₁ * Z + N.toBlocks₂₂)) +
          M.toBlocks₂₂ * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) := by noncomm_ring
    rw [e, hW]
    noncomm_ring

end PositivityTheory.Rg.Sw.Glob.GaussH
