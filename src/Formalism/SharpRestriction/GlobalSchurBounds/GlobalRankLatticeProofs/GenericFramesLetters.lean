module

public import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices

namespace PrimeReciprocalSums

theorem sum_inv_le (N : ℕ) (hN : 1 ≤ N) : ∑ q ∈ Finset.Icc 1 N, (1 : ℝ) / (q : ℝ) ≤ 1 + Real.log N := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩; clear hN
  suffices h : ∑ q ∈ Finset.Icc 1 (k + 1), (1 : ℝ) / (q : ℝ) ≤ 1 + Real.log ((k : ℝ) + 1) by
    exact_mod_cast h
  induction k with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]; have hy1 : (0 : ℝ) < (n : ℝ) + 1 + 1 := by positivity
    have h1 := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) hy1)
    rw [Real.log_div (by positivity) hy1.ne', show ((n : ℝ) + 1) / ((n : ℝ) + 1 + 1) =
      1 - 1 / ((n : ℝ) + 1 + 1) by rw [eq_sub_iff_add_eq, ← add_div, div_self hy1.ne']] at h1
    push_cast; linarith

theorem hOf_ord (e l : ℕ) (hl : Nat.Coprime l 2) :
    ordH (hOf e l) = orderOf (hcl e (ZMod.unitOfCoprime l (Nat.Coprime.pow_right (e + 2) hl))) := by
  simp only [hOf, dite_eq_left hl, ordH, ← orderOf_iotaH, iotaH_iotaHInv]

end PrimeReciprocalSums

open PrimeReciprocalSums

end Formalism.MainNotions.UnusedSlot33

end
