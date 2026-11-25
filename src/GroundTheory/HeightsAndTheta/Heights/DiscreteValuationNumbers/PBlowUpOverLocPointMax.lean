module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpLocRingFrac
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocPointLoc
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
import Mathlib.Algebra.AffineMonoid.UniqueSums

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocPointMax.proof (hfin : BlowUpOverLocFinite.Statement.{u})
    (hiso : BlowUpLocRingIso.Statement.{u}) (hfrac : BlowUpLocRingFrac.Statement.{u}) : BlowUpOverLocPointMax.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW' hW'rel hW'W
  have hW'p : W'.IsPrime := hW'.1.1
  have hbl : blowUpOf P u ≤ W' := le_trans le_sup_left hW'.1.2
  have hmh : IsMultiHomogIdeal W' :=
    MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W'
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'
  have hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W' :=
    iInf₂_le W' ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := hiso O K ι J P u W' hbl
  obtain ⟨hlocT, -⟩ :=
    HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl
  have : IsLocalRing (blowUpLocRing P u W') := φ.isLocalRing
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hWp : W.IsPrime := hWmin.1.1
  let 𝔫 : Ideal (blowUpOverLoc P W u) :=
    (IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)
  have hcomapA : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal :=
    isMaximal_comap_blowUpOverLoc_maximalIdeal hWp hPW hW'p hbl hW'W hBR φ hφ
  obtain ⟨hfinite, -⟩ := hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have : 𝔫.IsPrime := Ideal.comap_isPrime (Subring.inclusion hBR) (IsLocalRing.maximalIdeal _)
  have h𝔫 : 𝔫.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under 𝔫 hcomapA
  refine ⟨hBR, 𝔫, h𝔫, ?_⟩
  letI := (Subring.inclusion hBR).toAlgebra
  have := h𝔫.isPrime
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)
  · rintro ⟨z, hz⟩
    obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hzs⟩ :=
      hfrac O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel W' hW' hW'rel hW'W z hz
    refine ⟨(⟨b, hb⟩, ⟨⟨s, hs⟩, ?_⟩), Subtype.ext hzs⟩
    intro hm
    have hm' := (IsLocalRing.mem_maximalIdeal _).mp hm
    exact hm' (IsUnit.of_mul_eq_one (⟨t, ht⟩ : blowUpLocRing P u W') (Subtype.ext hst))
  · intro a a' h
    exact ⟨1, by rw [Subring.inclusion_injective hBR h]⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
