module

public import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.Qi39.EB.{u_1, u_2} :
    {m : Type u_1} → {n : Type u_2} → Matrix m n ℂ → ℝ → Prop :=
    fun {m : Type u_1} {n : Type u_2} (A : Matrix m n ℂ) (c : ℝ) ↦ ∀ (i : m) (j : n), ‖A i j‖ ≤ c

theorem UpperTheory.Reformulated.B.Qi39.det_norm_le.{u_1} :
    ∀ {n : Type u_1} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) {m : ℝ},
      UpperTheory.Reformulated.B.Qi39.EB A m → ‖A.det‖ ≤ (↑(Fintype.card n).factorial : ℝ) * m ^ Fintype.card n := by
  intro n _ _ A m h
  rw [Matrix.det_apply]
  calc
    ‖∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A (σ i) i‖
        ≤ ∑ _σ : Equiv.Perm n, m ^ Fintype.card n := by
      refine norm_sum_le_of_le _ fun σ _ => ?_
      rw [norm_units_zsmul, norm_prod]
      calc ∏ i, ‖A (σ i) i‖ ≤ ∏ _i : n, m :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => h (σ i) i)
        _ = m ^ Fintype.card n := by rw [Finset.prod_const, Finset.card_univ]
    _ = (↑(Fintype.card n).factorial : ℝ) * m ^ Fintype.card n := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
