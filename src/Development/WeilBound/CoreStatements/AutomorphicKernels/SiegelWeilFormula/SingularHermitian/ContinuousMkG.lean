module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TsContinuousNU
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KSing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section GRpt

variable {n : ℕ}

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp [JJ, Matrix.fromBlocks_multiply]

def invG (M : M2 n) : M2 n := -(JJ n * Mᴴ * JJ n)

theorem invG_mul {M : M2 n} (hM : InG M) : invG M * M = 1 := by
  unfold invG
  have h : JJ n * Mᴴ * JJ n * M = JJ n * (Mᴴ * JJ n * M) := by simp only [Matrix.mul_assoc]
  rw [neg_mul, h, hM, JJ_mul_JJ, neg_neg]

theorem mul_invG {M : M2 n} (hM : InG M) : M * invG M = 1 := mul_eq_one_comm.1 (invG_mul hM)

def mkG (M : M2 n) (hM : InG M) : GR n := ⟨⟨M, invG M, mul_invG hM, invG_mul hM⟩, hM⟩

def toGR' (M : M2 n) : GR n := if h : InG M then mkG M h else 1

theorem mR_mkG (M : M2 n) (hM : InG M) : mR (mkG M hM) = M := rfl

theorem mkG_mR (y : GR n) : mkG (mR y) y.2 = y := Subtype.ext (Units.ext rfl)

theorem toGR'_of {M : M2 n} (hM : InG M) : toGR' M = mkG M hM := dite_eq_left hM

theorem toGR'_mR (y : GR n) : toGR' (mR y) = y := (toGR'_of (M := mR y) y.2).trans (mkG_mR y)

theorem continuous_mR : Continuous (mR : GR n → M2 n) := Units.continuous_val.comp continuous_subtype_val

theorem continuous_mkG : Continuous (fun p : {M : M2 n | InG M} => mkG p.1 p.2) := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  show Continuous fun p : {M : M2 n | InG M} => invG p.1
  unfold invG
  exact ((continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul continuous_const).neg

theorem mR_mul' (y y' : GR n) : mR (y * y') = mR y * mR y' := rfl

end GRpt

end PositivityTheory.SiegelWeilFormula.KSing

end
