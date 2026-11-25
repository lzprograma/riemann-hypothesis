module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.BddOfPer

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KSing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

set_option linter.unusedSectionVars false

namespace UnitaryGroupBasics

theorem finOne_idem : finOne F * finOne F = finOne F :=
  Prod.ext (show (0 : Ainf F) * 0 = 0 from mul_zero _) (show (1 : Af F) * 1 = 1 from mul_one _)

theorem fin_mul {p q r : Type} [Fintype q] (X : Matrix p q (AE F E)) (Y : Matrix q r (AE F E)) :
    finOne F • (X * Y) = (finOne F • X) * (finOne F • Y) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, finOne_idem]

theorem cA_inclR (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem mapc_mul {p q r : Type} [Fintype q] (X : Matrix p q (AE F E)) (Y : Matrix q r (AE F E)) :
    (X * Y).map (cA σ) = X.map (cA σ) * Y.map (cA σ) := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

end UnitaryGroupBasics

namespace UnitaryGroupBasics

variable {n : ℕ}

theorem det_ne_of_inG {g : M2 n} (hg : InG g) : g.det ≠ 0 := by
  intro h0
  have e := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at e
  have hJ : JJ n * JJ n = -1 := by
    simp [JJ, Matrix.fromBlocks_multiply]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]
  have h2 := congrArg Matrix.det hJ
  rw [Matrix.det_mul, ← e, zero_mul, Matrix.det_neg] at h2
  simp at h2

def mkGR (g : M2 n) (hg : InG g) : GR n := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g (det_ne_of_inG hg), hg⟩

theorem continuous_herm' : Continuous (herm : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ) := by
  unfold herm
  fun_prop

theorem herm_conjTranspose' (x : Fin n → Fin n → ℝ) : (herm x)ᴴ = herm x := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  apply Complex.ext <;> simp [herm] <;> ring

theorem nU_mul_neg (H : Matrix (Fin n) (Fin n) ℂ) : nU H * nU (-H) = 1 := by
  simp [nU, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem continuous_nr (nr : (Fin n → Fin n → ℝ) → GR n) (hnr : ∀ x, mR (nr x) = nU (herm x)) : Continuous nr := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KSing.cont_nr <;> assumption

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end UnitaryGroupBasics

namespace UnitaryGroupBasics

theorem fin_toBlocks₁₂ {n : ℕ} (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
    finOne F • X.toBlocks₁₂ = (finOne F • X).toBlocks₁₂ := rfl

theorem toBlocks₁₂_one {n : ℕ} {α : Type} [Zero α] [One α] :
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) α).toBlocks₁₂ = 0 := by
  ext i j; simp [Matrix.toBlocks₁₂]

end UnitaryGroupBasics


end PositivityTheory.SiegelWeilFormula.KSing

end
