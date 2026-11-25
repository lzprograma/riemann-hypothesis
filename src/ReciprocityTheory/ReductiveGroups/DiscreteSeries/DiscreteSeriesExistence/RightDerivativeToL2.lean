module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsSmoothL2OfCasimirEigen
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SquareIntegrableInnerProduct
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SlmPhiCont

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem toL2_mem_smD_of_isSmoothL2 {ε : Fin n → Bool} {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F) :
    toL2 ε F ∈ smD ε (rreg ε) := by
  exact (mem_smD_iff ε (rreg ε) (toL2 ε F)).2 (slm_smooth hF)

theorem rightDerivative_toL2 {ε : Fin n → Bool} {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F) (a b : Fin n) :
    ((smE ε (rreg ε) a b ⟨toL2 ε F, toL2_mem_smD_of_isSmoothL2 hF⟩ : smD ε (rreg ε)) : L2 ε) =
      toL2 ε (Formalism.REAL.Eab ε a b F) := by
  rw [smE_apply (rreg_isURepOn ε), slm_dS hF (SmDerA.inG_cpart1 ε _),
    slm_dS hF (SmDerA.inG_cpart2 ε _)]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, ← add_smul, ← smul_eq_mul, ← Matrix.smul_apply,
    ← Matrix.add_apply, ← SmDerA.cpart_decomp]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro d _ hd
    simp [Ne.symm hd]
  · intro h
    exact absurd (Finset.mem_univ b) h
  · intro c _ hc
    apply Finset.sum_eq_zero
    intro d _
    simp [Ne.symm hc]
  · intro h
    exact absurd (Finset.mem_univ a) h

end ReciprocityTheory.ChartRestriction.DS
