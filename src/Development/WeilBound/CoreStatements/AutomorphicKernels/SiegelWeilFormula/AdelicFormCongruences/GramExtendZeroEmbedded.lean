module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties
public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB
import Mathlib.Tactic.Linter.Style

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Afc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def gE {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (σ : E →ₐ[F] E) {k : ℕ} (X : Matrix (Fin m) (Fin k) E) : Matrix (Fin k) (Fin k) E :=
  Xᵀ * J * X.map σ

theorem gE_apply {m k : ℕ} (J : Matrix (Fin m) (Fin m) E) (X : Matrix (Fin m) (Fin k) E) (i j : Fin k) :
    gE J σ X i j = ∑ b, (∑ a, X a i * J a b) * σ (X b j) := by
  simp [gE, Matrix.mul_apply]

theorem isUnit_neg_two_pow (k : ℕ) : IsUnit ((((-2 : ℤ) : AE F E)) ^ k) := by
  have h : ((-2 : ℤ) : AE F E) = inclR (F := F) (AF F) ((-2 : ℤ) : E) := (map_intCast _ _).symm
  rw [h]
  exact ((isUnit_iff_ne_zero.2 (by norm_num : ((-2 : ℤ) : E) ≠ 0)).map _).pow k

end PositivityTheory.SiegelWeilFormula.Afc

end
