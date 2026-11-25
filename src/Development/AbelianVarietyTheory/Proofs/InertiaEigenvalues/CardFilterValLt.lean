module

import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GlobalTheory.CardFilterLt

theorem card_filter_val_lt : ∀ {n h : ℕ}, h ≤ n → Finset.card {m : Fin n | (↑m : ℕ) < h} = h :=
  fun hh => Fin.card_filter_val_lt.trans (min_eq_right hh)

end GlobalTheory.CardFilterLt
