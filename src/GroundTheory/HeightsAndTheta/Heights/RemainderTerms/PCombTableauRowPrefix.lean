module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb

@[expose] public section

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauRowPrefix.proof : CombTableauRowPrefix.Statement := by
  intro m lam T hT t
  set c := T.symm t
  rw [← show T c = t from by simp [c]]
  refine Eq.trans ?_ (card_range c.1.2)
  refine card_bij (fun p _ => p.1.2) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hrow, hlt⟩ := (mem_filter.mp hp).2
    exact mem_range.mpr (lt_of_not_ge fun hle => (not_lt_of_ge (hT c p hrow.symm.le hle)) hlt)
  · intro p hp q hq hpq
    exact Subtype.ext (Prod.ext ((mem_filter.mp hp).2.1.trans (mem_filter.mp hq).2.1.symm) hpq)
  · intro k hk
    rw [mem_range] at hk
    let p : youngCells lam := ⟨(c.1.1, k), by
      have hc := c.2
      simp only [youngCells, mem_filter, mem_product, mem_univ, true_and, mem_range] at hc ⊢
      exact ⟨by omega, by omega⟩⟩
    refine ⟨p, mem_filter.mpr ⟨mem_univ _, rfl, ?_⟩, rfl⟩
    exact Fin.lt_def.mp (lt_of_le_of_ne (hT p c le_rfl hk.le) fun h =>
      hk.ne (congrArg (fun q : youngCells lam => q.1.2) (T.injective h)))

end GroundTheory.Heights₂.Heights.RestTerms
