module

public import Formalism.ConjugateSelfDual.Statement
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace Formalism.MainNotions.V.Lang

open Formalism.ConjugateSelfDual

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

variable (F Ω) in
def cycZ (l : ℕ) [Fact l.Prime] : G F Ω →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (Ω) l).comp
    (MulSemiringAction.toRingAut (G F Ω) (Ω))


section unram

variable (S : Set (HeightOneSpectrum (𝓞 F)))

end unram

end Formalism.MainNotions.V.Lang
