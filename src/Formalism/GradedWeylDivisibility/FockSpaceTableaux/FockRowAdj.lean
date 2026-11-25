module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockSubAdj
import Mathlib.Tactic.Lemma

@[expose] public section

open MvPolynomial Formalism.REAL

noncomputable section

namespace Formalism.GradedWeylDivisibility

def LFocks_rowMat {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ :=
  fun v w => if v.2 = w.2 then g v.1 w.1 else 0

lemma LFocks_rowAct_eq_sub {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    rowAct ℂ (n := n) g = sub (LFocks_rowMat g) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [rowAct, sub, aeval_X, LFocks_rowMat]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single v.2]
  · simp
  · intro s _ hs; simp [Ne.symm hs]
  · simp

lemma LFocks_rowMat_conjTranspose {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    (LFocks_rowMat (n := n) g).conjTranspose = LFocks_rowMat g.conjTranspose := by
  ext v w
  simp only [Matrix.conjTranspose_apply, LFocks_rowMat]
  by_cases h : v.2 = w.2
  · rw [ite_eq_left h.symm, ite_eq_left h]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, star_zero]

theorem fischerInnerRowActionAdjoint : FockRowAdj := by
  intro r n g f h
  rw [LFocks_rowAct_eq_sub, LFocks_rowAct_eq_sub, LFocks_subAdj, LFocks_rowMat_conjTranspose]

end Formalism.GradedWeylDivisibility
