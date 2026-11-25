module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexFormsOnPoints
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPrimeComplexRadical
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexMinimalPrimesContract
public import Mathlib.RingTheory.Nullstellensatz

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem ComplexFormsOnPoints.proof (hR : PrimeComplexRadical.Statement)
    (hM : ComplexMinimalPrimesContract.Statement) : ComplexFormsOnPoints.Statement := by
  intro K _ ι _ P hP hrel F hF
  apply hR (Σ k, ι k) P hP
  rw [← Ideal.sInf_minimalPrimes]
  refine Ideal.mem_sInf.2 fun {Q} hQ => ?_
  choose i hi using hrel
  let g : MRing ι := ∏ k, X ⟨k, i k⟩
  have hmap (f : MRing ι) : map (Int.castRingHom ℂ) f ∈ Q ↔ f ∈ P := by
    rw [← hM (Σ k, ι k) P hP Q hQ, Ideal.mem_comap]
  suffices hv : F * map (Int.castRingHom ℂ) g ∈ vanishingIdeal ℂ (zeroLocus ℂ Q) by
    rw [vanishingIdeal_zeroLocus_eq_radical, hQ.1.1.radical] at hv
    refine (hQ.1.1.mem_or_mem hv).resolve_right fun hg => ?_
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).1 ((hmap g).1 hg)
    exact hi k hk
  rw [mem_vanishingIdeal_iff]
  intro z hz
  change eval z _ = 0
  rw [map_mul]
  by_cases h : ∏ k, z ⟨k, i k⟩ = 0
  · simp [g, map_prod, h]
  · rw [hF z ⟨fun k => ⟨i k, Finset.prod_ne_zero_iff.1 h k (Finset.mem_univ k)⟩,
        fun f hf => hz _ ((hmap f).2 hf)⟩, zero_mul]

end GroundTheory.Heights₂.Heights.HilbertSamuel
