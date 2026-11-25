module

public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstantCoeffAeval

@[expose] public section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem cycloSimple : CycloSimpleStatement := by
  intro LL S _ _ _ _ m hm ζ E hζ hE0 hE
  obtain ⟨G, hG⟩ := (X_dvd_iff.2 (by
    simpa [constantCoeff_aeval, hE0] using hζ) :
    X ∣ Polynomial.aeval (C ζ * E) (Polynomial.cyclotomic m LL))
  refine ⟨(isUnit_iff_constantCoeff.2 ?_).unit, mul_comm X G ▸ hG⟩
  obtain ⟨Q, hQ⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one m LL
  have hroot := congrArg (Polynomial.aeval ζ) hQ
  apply_fun constantCoeff ∘ derivative ∘ Polynomial.aeval (C ζ * E) at hQ
  have hmu := (Nat.cast_ne_zero.2 hm.ne').isUnit.map (algebraMap LL S)
  simp_all [Function.comp_def, constantCoeff_aeval, Derivation.leibniz, smul_eq_mul,
    sub_eq_zero, ← pow_succ, Nat.sub_add_cancel hm]

end LevelStatements.Lv
