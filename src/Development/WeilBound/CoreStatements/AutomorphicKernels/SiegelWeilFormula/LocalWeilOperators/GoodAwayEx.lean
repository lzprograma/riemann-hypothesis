module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction

@[expose] public section

noncomputable section

open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def mLoc {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : M2 n := Matrix.fromBlocks a 0 0 (aᴴ)⁻¹

def nbLoc {n : ℕ} (c : Matrix (Fin n) (Fin n) ℂ) : M2 n := Matrix.fromBlocks 1 0 c 1

end PositivityTheory.SiegelWeilFormula

end
