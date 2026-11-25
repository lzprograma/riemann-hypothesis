module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow
public import Mathlib.GroupTheory.FiniteAbelian.Basic

@[expose] public section

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.Tau

theorem t2 : ExistsBoundedBasis := by
  classical
  intro K _ _ n j M B b hM hBM hli hbB hBspan
  let := isNoetherian_of_fg_of_noetherian M hM
  let : Module.Finite (𝓞 K) B := Module.Finite.iff_fg.mpr (.of_le_of_isNoetherian hBM)
  let L := (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype
  let : Module.Finite ℤ (B ⧸ L) := Module.Finite.trans (𝓞 K) _
  apply Module.finite_of_fg_torsion
  intro q
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L q
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hBspan v.property)
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image c)
  refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy⟩, ?_⟩
  change (y : ℤ) • (Submodule.Quotient.mk (p := L) v) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  change y • (v : Fin n → K) ∈ Submodule.span (𝓞 K) (Set.range b)
  rw [← hc, Finset.smul_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [← smul_assoc]
  exact Submodule.smul_mem _
    (⟨y • c a, hint _ (Finset.mem_image_of_mem c (Finset.mem_univ a))⟩ : 𝓞 K)
    (Submodule.subset_span ⟨a, rfl⟩)

end Formalism.L2.SG.Pf.Tau
