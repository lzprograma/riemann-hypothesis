module

public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

theorem UpperTheory.Reformulated.B.Qm10.exists_rows_linearIndependent.{u, u_1, u_2} :
    ∀ {K : Type u_1} [Field K] {r : Type u} {c : Type u_2} [Fintype r] [Fintype c]
    (P : Matrix r c K) {k : ℕ}, k ≤ P.rank → ∃ (I : Fin k → r), LinearIndependent K fun (p : Fin k) ↦ P (I p) := by
  intro K _ r c _ _ P k hk
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K P.row
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card (Fin k) ≤ Fintype.card κ := by
    rw [Fintype.card_fin, ← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row]
    exact hk
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨fun p ↦ a (e p), hli.comp e e.injective⟩
