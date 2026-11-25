module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Decomp

@[expose] public section

noncomputable section

open scoped Matrix Classical
open NumberField MeasureTheory PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem herm_smul_one' {n : ℕ} (t : ℝ) :
    ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

end PositivityTheory.SiegelWeilFormula

end
