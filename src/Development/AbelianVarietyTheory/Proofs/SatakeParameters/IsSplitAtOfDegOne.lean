module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section
namespace GlobalTheory.CongEx

open UpperTheory.V.Af

theorem exists_place_over (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∃ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  have hp : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Int.prime_iff_natAbs_prime.2 (by simpa using (Fact.out : l.Prime))).irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 E)) ≤ Ideal.span {(l : ℤ)} := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have : x = 0 := by exact_mod_cast (algebraMap ℤ (𝓞 E)).injective_int (hx.trans (map_zero _).symm)
    rw [this]; exact zero_mem _
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) _ hker
  have hl : ((l : ℕ) : 𝓞 E) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, fun h => ?_⟩, hl⟩
  rw [h] at hQc
  have h0 : (l : ℤ) ∈ Ideal.span {(l : ℤ)} := Ideal.mem_span_singleton_self _
  rw [← hQc] at h0
  change (l : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) ⊥ at h0
  rw [Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 E)).injective_int] at h0
  have := (Fact.out : l.Prime).ne_zero
  simp_all

end GlobalTheory.CongEx

end
