module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Algebra.Order.AddGroupWithTop

@[expose] public section

theorem UpperTheory.Reformulated.B.Ydd3.withBot_eq_of_le_of_add_one_le :
    ∀ {x : WithBot ℕ∞} {c : ℕ},
      (↑c : WithBot ℕ∞) ≤ x → x + (1 : WithBot ℕ∞) ≤ (↑(c + (1 : ℕ)) : WithBot ℕ∞) → x = (↑c : WithBot ℕ∞) := by
  intro x c h1 h2
  induction x using WithBot.recBotCoe with
  | bot => exact le_antisymm bot_le h1
  | coe y =>
    have h3 : y + 1 ≤ (c : ℕ∞) + 1 := by
      simpa only [ENat.natCast_add, ENat.natCast_one] using (WithBot.coe_le_coe.mp h2)
    exact le_antisymm (WithBot.coe_le_coe.mpr
      ((ENat.add_le_add_iff_right (by simp)).mp h3)) h1
