module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLtOne

@[expose] public section

theorem UpperTheory.Reformulated.B.Gs5b.cd_norm_lt :
    ∀ {l : ℕ} [Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) {R : Type} [CommRing R] [IsLocalRing R]
      [Algebra (↥c.O) R] (y : R →ₐ[↥c.O] PadicAlgCl l),
      ∀ a ∈ IsLocalRing.maximalIdeal R, ‖(y : R → PadicAlgCl l) a‖ < (1 : ℝ) := by
  intro l _ c R _ _ _ y a ha
  exact UpperTheory.Reformulated.B.NormLtOne.norm_lt_one y a ha
