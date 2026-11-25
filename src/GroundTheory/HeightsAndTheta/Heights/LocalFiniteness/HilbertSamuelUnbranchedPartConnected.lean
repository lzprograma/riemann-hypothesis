module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTail
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocalizedQuotientIsSimpleModuleOfMul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeEuclMass
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeLocalFlat
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeEuclMass
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleHomLoc
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeLocalFlat
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelGrowthOffHypersurfacePolynomial

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ResidualComparison.proof (hpieces : BlowUpDecomposition.Statement.{u})
    (hdisj : ResidualDisjoint.Statement.{u}) (hcontr : ResidualContraction.Statement.{u}) :
    ResidualComparison.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  obtain ⟨hP', -, hsP', -, hres, hexc, -, -⟩ :=
    hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  have hY₀G' := hdisj O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  have hcmp := hcontr O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  set P' := blowUpOf P (blowUpGens s g f m e) with hP'def
  set G := G'.comap (liftForm (J := BlowUpIdx ι) (ι := ι) (R := O)) with hGdef
  have hP'prime : P'.IsPrime := hP'.multiProj.isPrime
  have hPprime : P.IsPrime := hP.multiProj.isPrime
  have hmul := DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) P'
  have hmul₀ := DivCycleMul.proof O K ι P
  have nm : ∀ x y, x ∉ P' → y ∉ P' → x * y ∉ P' := fun x y hx hy h =>
    (hP'prime.mem_or_mem h).elim hx hy
  have hzero : ∀ x, x ∉ G' → divCycle P' x G' = 0 := fun x hx => by
    by_contra h; exact hx (form_mem_of_divCycle_ne_zero h)

  have hG'supp : G' ∈ (P' ⊔ Ideal.span {liftForm s}).minimalPrimes ∧ IsRelevant G' := by
    by_contra h
    unfold divCycle at hsG'
    rw [dite_eq_right h] at hsG'
    exact lt_irrefl _ hsG'
  have hG'prime : G'.IsPrime := hG'supp.1.1.1
  have hP'G' : P' ≤ G' := le_sup_left.trans hG'supp.1.1.2
  have hlift : ∀ p ∈ P, liftForm (J := BlowUpIdx ι) p ∈ P' := fun p hp => by
    rw [hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm,
      Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have hGprime : G.IsPrime := Ideal.comap_isPrime _ _
  have hPG : P ≤ G := fun p hp => hP'G' (hlift p hp)
  have hGrel : IsRelevant G := fun k => by
    obtain ⟨i, hi⟩ := hG'supp.2 (some k)
    exact ⟨i, fun h => hi (by simpa [hGdef, liftForm] using h)⟩
  have hϖG : (C ϖ : MRing ι O) ∈ G := by
    rw [hGdef, Ideal.mem_comap, liftForm_const]; exact hϖG'

  obtain ⟨u, v, huG, huv⟩ := hD.2 G hGprime hPG hGrel
  have hfP := hD.1.num_not_mem
  have hgP := hD.1.den_not_mem
  have huP : u ∉ P := fun h => huG (hPG h)
  have hvP : v ∉ P := fun hv => by
    have h : u * f ∈ P := by
      rw [show u * f = (u * f - v * g) + v * g by ring]
      exact P.add_mem huv (P.mul_mem_right g hv)
    exact (hPprime.mem_or_mem h).elim huP hfP
  have hdown : ratDiv P f g G = divCycle P v G := by
    have h1 := congrFun (divCycle_congr_of_sub_mem huv) G
    rw [hmul₀ u f hPprime huP hfP, hmul₀ v g hPprime hvP hgP] at h1
    have hu0 : divCycle P u G = 0 := by
      by_contra h; exact huG (form_mem_of_divCycle_ne_zero h)
    simp only [Pi.add_apply] at h1
    unfold ratDiv; omega

  have hluP' : liftForm (J := BlowUpIdx ι) u ∉ P' := fun h => huG (hP'G' h)
  have hlfP' : liftForm (J := BlowUpIdx ι) f ∉ P' := fun h =>
    hexc.1.num_not_mem (by rw [map_mul]; exact P'.mul_mem_right _ h)
  have hlgP' : liftForm (J := BlowUpIdx ι) g ∉ P' := fun h => hexc.1.den_not_mem (P'.mul_mem_right _ h)
  have hluv : liftForm u * liftForm f - liftForm v * liftForm g ∈ P' := by
    rw [← map_mul, ← map_mul, ← map_sub]; exact hlift _ huv
  have hlvP' : liftForm (J := BlowUpIdx ι) v ∉ P' := fun hv => by
    have h : liftForm u * liftForm f ∈ P' := by
      rw [show liftForm u * liftForm f = (liftForm u * liftForm f - liftForm v * liftForm g) +
        liftForm v * liftForm g by ring]
      exact P'.add_mem hluv (P'.mul_mem_right _ hv)
    exact nm _ _ hluP' hlfP' h
  have hup : ratDiv P' (liftForm f) (liftForm g) G' = divCycle P' (liftForm v) G' := by
    have h1 := congrFun (divCycle_congr_of_sub_mem hluv) G'
    rw [hmul _ _ hP'prime hluP' hlfP', hmul _ _ hP'prime hlvP' hlgP'] at h1
    have hu0 := hzero _ huG
    simp only [Pi.add_apply] at h1
    unfold ratDiv; omega

  have hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := hres.1.num_not_mem
  have hlmP' : liftForm (J := BlowUpIdx ι) m ∉ P' := hres.1.den_not_mem
  have hY₀P' : (newVar none : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := fun h => hY₀G' (hP'G' h)
  have hrel := congrFun (divCycle_congr_of_sub_mem (blowUp_relation P s g f m e)) G'
  rw [map_mul, map_mul, hmul _ _ hP'prime (nm _ _ hsP' hlgP') hY₁P',
    hmul _ _ hP'prime (nm _ _ hlfP' hlmP') hY₀P', hmul _ _ hP'prime hsP' hlgP',
    hmul _ _ hP'prime hlfP' hlmP'] at hrel
  have hY₀0 := hzero _ hY₀G'
  simp only [Pi.add_apply] at hrel
  have hv := hcmp v hvP
  refine ⟨G, hϖG, hcmp s hsP, ?_⟩
  unfold ratDiv at hup hdown ⊢
  omega

end GroundTheory.Heights₂.Heights.NumbersDVR
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ResidualDisjoint.proof : ResidualDisjoint.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  set P' := blowUpOf P (blowUpGens s g f m e) with hP'def
  have hPprime : P.IsPrime := hP.multiProj.isPrime
  have hP'prime : P'.IsPrime := RingHom.ker_isPrime _
  have hmul := DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) P'
  have hlm : liftForm (J := BlowUpIdx ι) m ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact hmP h
  have hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker] at h
    simp only [newVar, aeval_X, blowUpSubst, blowUpGens, mul_eq_zero, Polynomial.X_ne_zero, or_false,
      Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h
    exact (hPprime.mem_or_mem h).elim hD.1.num_not_mem hmP
  have hnonneg : ∀ x W, 0 ≤ divCycle P' x W := fun x W => by
    unfold divCycle; split_ifs <;> simp
  have hzero : ∀ x, x ∉ G' → divCycle P' x G' = 0 := fun x hx => by
    by_contra h; exact hx (form_mem_of_divCycle_ne_zero h)
  have hG'supp : G' ∈ (P' ⊔ Ideal.span {liftForm s}).minimalPrimes ∧ IsRelevant G' := by
    by_contra h
    unfold divCycle at hsG'
    rw [dite_eq_right h] at hsG'
    exact (lt_irrefl 0) hsG'
  have hP'G' : P' ≤ G' := le_sup_left.trans hG'supp.1.1.2

  have hY₁G' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' := by
    apply form_mem_of_divCycle_ne_zero (P := P')
    have := hnonneg (liftForm m) G'
    unfold ratDiv at hresG'; omega

  have hYiG' : ∀ i : ∀ k, ι k, (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' := by
    intro i
    by_contra hYi
    have hrel : liftForm (powMonomial e i) * newVar (some none) -
        liftForm m * newVar (some (some i)) ∈ P' := by
      rw [hP'def, blowUpOf, RingHom.mem_ker]
      simp only [map_sub, map_mul, aeval_blowUpSubst_liftForm, newVar, aeval_X, blowUpSubst, blowUpGens]
      ring
    have hYiP' : (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := fun h => hYi (hP'G' h)
    by_cases hp : liftForm (J := BlowUpIdx ι) (powMonomial e i : MRing ι O) ∈ P'
    · have h := P'.sub_mem (P'.mul_mem_right (newVar (some none)) hp) hrel
      rw [sub_sub_cancel] at h
      exact (hP'prime.mem_or_mem h).elim hlm hYiP'
    · have h1 := congrFun (divCycle_congr_of_sub_mem hrel) G'
      rw [hmul _ _ hP'prime hp hY₁P', hmul _ _ hP'prime hlm hYiP'] at h1
      simp only [Pi.add_apply] at h1
      have h2 := hzero _ hYi
      have h3 := hnonneg (liftForm (powMonomial e i)) G'
      unfold ratDiv at hresG'; omega

  obtain ⟨j, hj⟩ := hG'supp.2 none
  change BlowUpIdx ι at j
  rcases j with _ | _ | i
  · exact hj
  · exact absurd hY₁G' hj
  · exact absurd (hYiG' i) hj

end GroundTheory.Heights₂.Heights.NumbersDVR
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFinite.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFinite.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFinite.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalIntegral GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_LocalIntegralClosureFinite GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocNoetherian

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalFlat.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalFlat.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalFlat.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConePolyLocalization

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_DivCycleHomLoc.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingLocal

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualCompare.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ResidualComparison.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ResidualComparison.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces GroundTheory.Heights₂.Heights.NumbersDVR.ResidualDisjoint.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualContraction

theorem GroundTheory.Heights₂.Heights.AutoClose.TubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement :=
  @GroundTheory.Heights₂.Heights.TubeEuclMass.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.TubeCollarMass GroundTheory.Heights₂.Heights.AutoClose.TubeDeepMass
end -- clump:auto
end -- clump:auto
