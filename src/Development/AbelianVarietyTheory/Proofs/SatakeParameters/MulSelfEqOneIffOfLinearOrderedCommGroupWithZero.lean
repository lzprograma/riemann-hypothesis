module

import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.MemMaxVAIff
public import Formalism.SatakeDualWeyl.StatementF
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.Hk3.Inh

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_two {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (hq : Odd q) : Valued.v (2 : L) = 1 := by
  apply Formalism.IndefR.LocBrg.two_val <;> assumption




end GlobalTheory.Hk3.Inh

end
