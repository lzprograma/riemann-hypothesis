module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb

@[expose] public section

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

noncomputable section

theorem CombTableEqWords.proof (h1 : CombCardYoungCells.Statement)
    (h2 : CombWordOfTableau.Statement) (h3 : CombTableauOfWord.Statement) :
    CombTableEqWords.Statement := by
  intro m lam hlam
  classical
  let toWord (T : {T : youngCells lam ≃ Fin (youngCells lam).card // IsStandard T}) :
      latticeWords (youngCells lam).card lam :=
    ⟨rowWord T.1, (h2 m lam hlam T.1 T.2).1⟩
  have hbij : Function.Bijective toWord := by
    refine ⟨?_, fun w => ?_⟩
    · intro T U hTU
      apply Subtype.ext
      have hsymm : T.1.symm = U.1.symm := by
        refine Equiv.ext fun t => Subtype.ext ?_
        rw [← (h2 m lam hlam T.1 T.2).2 t, ← (h2 m lam hlam U.1 U.2).2 t]
        exact congrArg (fun w => cellOfWord w.1 t) hTU
      simpa using congrArg Equiv.symm hsymm
    · obtain ⟨T, hT, hw⟩ := h3 m lam hlam w.1 w.2
      exact ⟨⟨T, hT⟩, Subtype.ext hw⟩
  let e := Equiv.ofBijective toWord hbij
  show Nat.card {T : youngCells lam ≃ Fin (youngCells lam).card // IsStandard T} = _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, h1 m lam]

end

end GroundTheory.Heights₂.Heights.RestTerms
