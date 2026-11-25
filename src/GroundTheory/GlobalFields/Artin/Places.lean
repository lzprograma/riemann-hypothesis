module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField

namespace GroundTheory.Global.Artin

section Action

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

instance : MulAction Gal(L/K) (HeightOneSpectrum (𝓞 L)) where
  smul σ w := ⟨σ • w.asIdeal, Ideal.IsPrime.smul σ, fun h ↦ w.ne_bot (by
    rw [← inv_smul_smul σ w.asIdeal, h, Ideal.smul_bot])⟩
  one_smul w := HeightOneSpectrum.ext (one_smul _ w.asIdeal)
  mul_smul σ τ w := HeightOneSpectrum.ext (mul_smul σ τ w.asIdeal)

end Action

end GroundTheory.Global.Artin
