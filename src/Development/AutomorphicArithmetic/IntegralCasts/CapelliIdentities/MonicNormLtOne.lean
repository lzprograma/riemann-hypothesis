module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLtOne

@[expose] public section

theorem UpperTheory.Reformulated.B.MonicNormLtOne.mc_norm_lt :
    ∀ {l : ℕ} [Fact (Nat.Prime l)] {R : Type}
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R] (y : R →ₐ[ℤ_[l]] PadicAlgCl l),
    ∀ a ∈ IsLocalRing.maximalIdeal R, ‖(y : R → PadicAlgCl l) a‖ < (1 : ℝ) := by
  intro l _ R _ _ _ y a ha
  exact UpperTheory.Reformulated.B.NormLtOne.norm_lt_one (O := ℤ_[l]) y a ha
