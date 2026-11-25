module

import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanCup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer

@[expose] public section

noncomputable section

open Finset

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {Y : Type}

def fc {n : ℕ} (i : ℕ) (l : Fin n) : Fin (n + 1) :=
  ⟨if (l : ℕ) < i then (l : ℕ) else (l : ℕ) + 1, by split_ifs <;> omega⟩

theorem fc_val {n : ℕ} (i : ℕ) (l : Fin n) :
    ((fc i l : Fin (n + 1)) : ℕ) = if (l : ℕ) < i then (l : ℕ) else (l : ℕ) + 1 :=
  rfl

theorem succAbove_eq_fc {n : ℕ} (i : Fin (n + 1)) (l : Fin n) : i.succAbove l = fc i l := by
  apply Fin.ext
  rw [fc_val]
  rcases Nat.lt_or_ge (l : ℕ) (i : ℕ) with h | h
  · rw [ite_eq_left h, Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    rfl
  · rw [ite_eq_right (by omega), Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]
    rfl

theorem dc_eq {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Fin (m + 2) → Y) :
    dc F y = ∑ i : Fin (m + 2), (-1 : ℝ) ^ (i : ℕ) * F (fun l => y (fc i l)) := by
  simp only [dc, succAbove_eq_fc]

theorem dc_dc {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : dc (dc F) = 0 := by
  apply PositivityTheory.KB.SplitAffineSpectral.PrismSpan.dc_dc

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
