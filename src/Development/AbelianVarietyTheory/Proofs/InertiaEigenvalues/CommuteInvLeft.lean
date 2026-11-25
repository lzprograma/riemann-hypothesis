module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

namespace GlobalTheory.CommuteInvLeft

theorem commute_inv_left : ∀ {B : Type} [inst : Ring B] {x xi y : B},
    x * xi = (1 : B) → xi * x = (1 : B) → Commute x y → Commute xi y := by
  intro B _ x xi y h1 h2 h
  exact Commute.units_inv_left (u := ⟨x, xi, h1, h2⟩) h

end GlobalTheory.CommuteInvLeft
