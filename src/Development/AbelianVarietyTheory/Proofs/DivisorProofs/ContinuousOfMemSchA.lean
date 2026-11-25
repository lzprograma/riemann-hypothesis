module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainTheta
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.WeilM

namespace GlobalTheory.ThKOp


open scoped Classical in
theorem continuous_of_mem_schA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  apply GlobalTheory.ThetaUnfold.schA_continuous <;> assumption

end GlobalTheory.ThKOp
