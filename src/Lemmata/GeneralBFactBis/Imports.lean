module

public import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Monoid
public import Mathlib.Algebra.Order.AddGroupWithTop
import Lemmata.GeneralBFactTerForm.Imports

@[expose] public section

namespace Bl.general_b_fact_bis

/-- Adding one on `WithBot ℕ∞` can be cancelled to recover a natural number. -/
theorem goal1 {x : WithBot ENat} {m : Nat}
    (h : x + 1 = (↑(m + 1) : WithBot ENat)) : x = (m : Nat) := general_b_fact_ter_form.goal1 h

end Bl.general_b_fact_bis
