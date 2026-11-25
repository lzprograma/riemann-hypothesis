module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

@[expose] public section

theorem UpperTheory.Reformulated.B.FinitePlaceSumBound.finitePlace_sum_le.{u_1, u_2} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] (v : NumberField.FinitePlace K) {α : Type u_2} (s : Finset α)
      (f : α → K) {B : ℝ}, (0 : ℝ) ≤ B → (∀ a ∈ s, (v : K → ℝ) (f a) ≤ B) → (v : K → ℝ) (∑ a ∈ s, f a) ≤ B := by
  intro K _ _ v α s f B hB h
  exact Finset.sum_induction f (fun x => v x ≤ B)
    (fun a b ha hb => (NumberField.FinitePlace.add_le v a b).trans (max_le ha hb)) (by simpa using hB) h
