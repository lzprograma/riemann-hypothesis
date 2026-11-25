module

public import Formalism.PadicSubsetSums.CentralIdempotents.ResidueAvoidanceOfPrimes
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace Formalism.IrreducibleCountingLemmas.TOP

private theorem tsum_mul_inv_pow_succ_eq_div_sub_one (ℓ : ℕ) (H : ℝ) (hℓ : (2 : ℝ) ≤ ℓ) :
    ∑' j : ℕ, H * ((ℓ : ℝ)⁻¹) ^ (j + 1) = H / ((ℓ : ℝ) - 1) := by
  simp_rw [pow_succ', ← mul_assoc]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (show 1 < (ℓ : ℝ) by linarith))]
  have h0 : (ℓ : ℝ) ≠ 0 := by linarith
  rw [show (1 : ℝ) - (ℓ : ℝ)⁻¹ = ((ℓ : ℝ) - 1) / ℓ by field_simp [h0]]
  field_simp [h0, show (ℓ : ℝ) - 1 ≠ 0 by linarith]

theorem carryFloorLeGeom : SgLe := by
  intro f _ ℓ h H hℓ hH i
  have hgeom : Summable (fun j : ℕ => (H : ℝ) * ((ℓ : ℝ)⁻¹) ^ (j + 1)) := by
    simp_rw [pow_succ', ← mul_assoc]
    exact (summable_geometric_of_lt_one (show 0 ≤ (ℓ : ℝ)⁻¹ by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (show 1 < ℓ by omega)))).mul_left _
  have hle : ∀ j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1) ≤
      (H : ℝ) * ((ℓ : ℝ)⁻¹) ^ (j + 1) := fun j => by
    rw [inv_pow, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hH _) (by positivity)
  refine (Int.floor_le _).trans ?_
  rw [← tsum_mul_inv_pow_succ_eq_div_sub_one ℓ H (by exact_mod_cast hℓ)]
  exact (hgeom.of_nonneg_of_le (fun j => by positivity) hle).tsum_le_tsum hle hgeom

end Formalism.IrreducibleCountingLemmas.TOP
