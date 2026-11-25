module

import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Tactic.Linter.Style

@[expose] public section

namespace Formalism.BasicNotions

open NumberField

variable {R : Ranks}

theorem Host.sqrtMinusD_sq (H : Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem Host.conj_sqrtMinusD (H : Host R) : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply Formalism.MainNotions.UnusedSlot33.HK.conj_b

theorem Host.exists_trace_one (H : Host R) : ∃ c : 𝓞 H.E, (c : H.E) + H.conj c = 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.hyp.2.2.2.1; omega⟩
  set c : H.E := (1 + H.sqrtMinusD) / 2
  have hc : c ^ 2 - c + (m : H.E) = 0 := by
    have e : ((H.d : ℕ) : H.E) + 1 = 4 * (m : H.E) := by exact_mod_cast hm
    have hs := H.sqrtMinusD_sq
    simp only [c]
    linear_combination (1 / 4 : H.E) * hs - (1 / 4 : H.E) * e
  have hint : IsIntegral ℤ c := ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_add, hc]⟩
  refine ⟨⟨c, hint⟩, ?_⟩
  show c + H.conj c = 1
  simp only [c, map_div₀, map_add (f := _), map_one, H.conj_sqrtMinusD, map_ofNat]
  ring

end Formalism.BasicNotions
