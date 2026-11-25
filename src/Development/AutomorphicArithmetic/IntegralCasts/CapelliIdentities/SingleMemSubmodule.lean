module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Data.Matrix.Mul

@[expose] public section

theorem UpperTheory.Reformulated.B.SingleMemSubmodule.single_mem :
    ∀ {K : Type} [Field K] (d : Fin (3 : ℕ) → K),
    Function.Injective d →
      ∀ (W : Submodule K (Fin (3 : ℕ) → K)),
        (∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) →
          ∀ {v : Fin (3 : ℕ) → K}, v ∈ W → ∀ {i : Fin (3 : ℕ)}, v i ≠ (0 : K) → Pi.single i (1 : K) ∈ W := by
  intro K _ d hd W hW v hv i hi
  have step : ∀ (c : K), ∀ w ∈ W, (fun l => (d l - c) * w l) ∈ W := by
    intro c w hw
    convert W.sub_mem (hW w hw) (W.smul_mem c hw) using 1
    funext l
    simp [Matrix.mulVec_diagonal, smul_eq_mul, sub_mul]
  have iter : ∀ s : Finset (Fin 3), (fun l => (∏ j ∈ s, (d l - d j)) * v l) ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hv
    | insert a s ha ih => simpa [Finset.prod_insert ha, mul_assoc] using step (d a) _ ih
  have hc : (∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j hj =>
      sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hj) (hd h).symm) hi
  have h := W.smul_mem ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹
    (iter (Finset.univ.erase i))
  have e : (Pi.single i (1 : K) : Fin 3 → K)
      = ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹ •
        (fun l => (∏ j ∈ Finset.univ.erase i, (d l - d j)) * v l) := by
    funext l
    rw [Pi.smul_apply, smul_eq_mul]
    rcases eq_or_ne l i with rfl | hl
    · rw [Pi.single_eq_same, inv_mul_cancel₀ hc]
    · have hz : ∏ j ∈ Finset.univ.erase i, (d l - d j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩) (sub_self _)
      rw [Pi.single_eq_of_ne hl, hz, zero_mul, mul_zero]
  rw [e]
  exact h
