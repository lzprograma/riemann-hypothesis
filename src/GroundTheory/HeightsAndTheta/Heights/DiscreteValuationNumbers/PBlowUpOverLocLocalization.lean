module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxCentreCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpLocRingFracCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingIso
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingLocal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultiHomogPrimeAvoid
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingFrac
import Mathlib.Algebra.AffineMonoid.UniqueSums

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocLocalization.proof (hfam : BlowUpOverLocFamilyFinite.Statement.{u}) :
    BlowUpOverLocLocalization.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW'p hmh hW'rel hbl hW'W
  have hW'fam : W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W := ⟨hW'p, hmh, hW'rel, hbl, hW'W⟩
  have hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W' := iInf₂_le W' hW'fam
  obtain ⟨e, L, hL, he, hLQ⟩ := MultiHomogPrimeAvoid.proof O (Option K) (extIdx ι J) _
    (hfam O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel) (fun Q hQ => ⟨hQ.1, hQ.2.1, hQ.2.2.1⟩)
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := BlowUpLocRingIso.proof O K ι J P u W' hbl
  obtain ⟨hlocT, -⟩ :=
    HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl
  have : IsLocalRing (blowUpLocRing P u W') := φ.isLocalRing

  have hfrac : ∀ z ∈ blowUpLocRing P u W', ∃ b ∈ blowUpOverLoc P W u, ∃ s ∈ blowUpOverLoc P W u,
      (∃ t ∈ blowUpLocRing P u W', s * t = 1) ∧ z * s = b := fun _ hz =>
    BlowUpLocRingFrac.of_mem hW'p hmh hW'rel hbl hW'W hL he hLQ φ hφ hz

  let 𝔭 : Ideal (blowUpOverLoc P W u) :=
    (IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)
  have h𝔭 : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  refine ⟨hBR, 𝔭, h𝔭, ?_⟩
  letI := (Subring.inclusion hBR).toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)
  · rintro ⟨z, hz⟩
    obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hzs⟩ := hfrac z hz
    refine ⟨(⟨b, hb⟩, ⟨⟨s, hs⟩, ?_⟩), Subtype.ext hzs⟩
    intro hm
    have hm' := (IsLocalRing.mem_maximalIdeal _).mp hm
    exact hm' (IsUnit.of_mul_eq_one (⟨t, ht⟩ : blowUpLocRing P u W') (Subtype.ext hst))
  · intro a a' h
    exact ⟨1, by rw [Subring.inclusion_injective hBR h]⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
