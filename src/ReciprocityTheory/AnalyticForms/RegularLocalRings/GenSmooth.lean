module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

theorem gs_exists_rows_det_ne_zero {K : Type*} [Field K] {t r : ℕ} (M : Matrix (Fin t) (Fin r) K)
    (hM : ∀ c : Fin r → K, M.mulVec c = 0 → c = 0) :
    ∃ a : Fin r → Fin t, (M.submatrix a id).det ≠ 0 := by
  classical
  obtain ⟨κ, a, _, hsp, hli⟩ := exists_linearIndependent' K M.row
  let b := Pi.basisFun K (Fin r)
  let B := Module.Basis.mk hli (by
    rw [hsp]
    by_contra h
    obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_of_le_not_ge le_top h)
    apply hf (b.ext fun k => ?_)
    suffices hc : (fun j => f (b j)) = 0 by simpa using congrFun hc k
    refine hM _ (funext fun i => ?_)
    calc
      _ = f (M i) := by
        simpa [b, Matrix.mulVec, dotProduct, smul_eq_mul] using congrArg f (b.sum_repr (M i))
      _ = 0 := hker (Submodule.subset_span ⟨i, rfl⟩))
  let e := b.indexEquiv B
  refine ⟨a ∘ e, ?_⟩
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_row_iff_isUnit]
  exact hli.comp e e.injective

end ReciprocityTheory.AnForm.R
