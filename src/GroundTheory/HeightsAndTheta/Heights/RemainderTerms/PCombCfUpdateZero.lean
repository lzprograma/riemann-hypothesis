module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb

@[expose] public section

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Comb

theorem CombCfUpdateZero.proof : CombCfUpdateZero.Statement := by
  intro m A hA lam hlam i hpos hcase
  obtain ⟨b, hib, hb⟩ : ∃ b : Fin m, i < b ∧ lam i ≤ lam b := by
    rcases hcase with h0 | hn
    · exact ⟨⟨i + 1, by simp only [stair] at hpos; omega⟩, Nat.lt_succ_self _, by omega⟩
    · by_contra hk
      push Not at hk
      apply hn
      intro a b hab
      simp only [Function.update_apply]
      split_ifs with hb ha ha
      · exact le_rfl
      · exact (Nat.sub_le _ _).trans (hlam (show a ≤ i from hb ▸ hab))
      · specialize hk b (lt_of_le_of_ne (ha ▸ hab) (fun e => hb e.symm))
        omega
      · exact hlam hab
  let j : Fin m := ⟨i.val + 1, Nat.lt_of_le_of_lt hib b.isLt⟩
  have hij : i < j := Nat.lt_succ_self _
  apply cf_eq_zero_of_eq hA hij.ne
  rw [Function.update_self, Function.update_of_ne hij.ne.symm,
    le_antisymm (hlam hij.le) (hb.trans (hlam (show j ≤ b from hib)))]
  simp only [stair, j] at hpos ⊢
  omega

end GroundTheory.Heights₂.Heights.RestTerms
