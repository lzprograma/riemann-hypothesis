module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartProjFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsConeAvoid
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjHomInjective
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import Mathlib.RingTheory.SimpleRing.Principal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartModel

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre segre_rel)
open ComplexSets MvPolynomial Matrix

theorem homogeneousComponent_mem_leadIdeal {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∈ J) {r : ℕ} (hr : f.totalDegree ≤ r) :
    homogeneousComponent r f ∈ leadIdeal J :=
  GoodChartModel.homogeneousComponent_mem_leadIdeal hf hr

theorem eval_linPoly_eq_mulVec {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (r : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly A r) = (A *ᵥ x) r :=
  GoodChartModel.eval_linPoly A r x

theorem SegreChartProjFinite.pow_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hΨ0 : ∀ w, Ψ w 0 = w i)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ segreChartComponents P σ i) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by
  refine GoodChartModel.pow_mem hP hΨ (le_trans ?_ (mem_segreChartComponents.1 hJ).1.2) a
  intro f hf
  rw [projChartIdeal, MvPolynomial.mem_vanishingIdeal_iff] at hf
  rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
  rintro _ ⟨z, hz, hzi, rfl⟩
  exact hf _ ⟨z, hz, (hΨ0 _).trans hzi, rfl⟩

theorem SegreChartProjFinite.proof : SegreChartProjFinite.Statement := by
  intro K _ ι _ P e m σ i Ψ hP hΨ hΨ0 J hJ
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := SegreChartProjFinite.pow_mem hP hΨ hΨ0 hJ a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨FiniteProjHomInjective.proof m e J _ (mem_segreChartComponents.1 hJ).1.1
    (SegreChartDim.proof K ι P e m σ i hP J hJ) hfin, hfin⟩

end GroundTheory.Heights₂.Heights
