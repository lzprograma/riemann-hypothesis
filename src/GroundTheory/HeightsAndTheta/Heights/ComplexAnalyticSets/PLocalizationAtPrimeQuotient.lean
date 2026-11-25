module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalizationAtPrimeQuotient
public import Mathlib.RingTheory.Localization.LocalizationLocalization

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

theorem LocalizationAtPrimeQuotient.proof : LocalizationAtPrimeQuotient.Statement.{u} := by
  intro A _ I T P _ W _ hP
  let Q := A ⧸ I
  let B := Localization.AtPrime W ⧸ I.map (algebraMap A (Localization.AtPrime W))

  have hsub : (P.comap (algebraMap Q (Localization T))).primeCompl =
      Algebra.algebraMapSubmonoid Q W.primeCompl := by
    subst hP
    exact (Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective (P.comap (algebraMap Q (Localization T)))).symm
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid Q W.primeCompl) (Localization.AtPrime P) := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization T
      (Localization.AtPrime P) P
    rw [IsLocalization.AtPrime, hsub] at this
    exact this
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid Q W.primeCompl)
    (Localization.AtPrime P) B
  refine ⟨e.toRingEquiv, fun a => ?_⟩
  have h2 : algebraMap (Localization T) (Localization.AtPrime P)
      (algebraMap Q (Localization T) (Ideal.Quotient.mk I a)) =
      algebraMap Q (Localization.AtPrime P) (Ideal.Quotient.mk I a) :=
    (IsScalarTower.algebraMap_apply Q (Localization T) (Localization.AtPrime P) _).symm
  rw [h2]
  exact e.commutes (Ideal.Quotient.mk I a)

end

end GroundTheory.Heights₂.Heights
