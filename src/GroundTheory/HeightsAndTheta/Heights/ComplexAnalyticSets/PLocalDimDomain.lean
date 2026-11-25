module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalDimDomain
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMaximalIdealHeightFG
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem LocalDimDomain.proof : LocalDimDomain.Statement := by
  intro n e J hJ he q hq
  have := hJ
  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hJM : J ≤ M := fun f hf => RingHom.mem_ker.mpr (hq f hf)
  let m : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := M.map (Ideal.Quotient.mk J)
  have hm : m.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJM)
  have hsub : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ J) M.primeCompl =
      m.primeCompl := by
    have hM : m.comap (Ideal.Quotient.mk J) = M := Ideal.comap_map_mk hJM
    simpa only [Algebra.algebraMapSubmonoid, Ideal.Quotient.algebraMap_eq, hM] using
      Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective m
  have : m.IsPrime := hm.isPrime
  have : IsLocalization.AtPrime (localRingAt J q) m := by
    unfold IsLocalization.AtPrime
    rw [← hsub]
    unfold localRingAt
    infer_instance
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (localRingAt J q),
    NumbersDVR.MaximalIdealHeightFG.proof ℂ (MvPolynomial (Fin n) ℂ ⧸ J) m hm, he]

end GroundTheory.Heights₂.Heights
