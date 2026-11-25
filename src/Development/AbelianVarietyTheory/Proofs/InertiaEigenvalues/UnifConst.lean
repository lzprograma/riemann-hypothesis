module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsZeroTranslationInvariantOfLocallyConst
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.TestFn

theorem unif_const (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (f : X → ℂ)
    (hf : IsTest f) : ∃ V ∈ 𝓝 (0 : X), ∀ x v, v ∈ V → f (x + v) = f x := by
  apply GlobalTheory.isTest_nhds_inv <;> assumption

theorem slice_test {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (T : X × Y → ℂ) (hT : IsTest T) (y : Y) :
    IsTest (fun x => T (x, y)) := by
  refine ⟨hT.1.comp_continuous (Continuous.prodMk_left y), ?_⟩
  have hc : IsCompact (Prod.fst '' tsupport T) := hT.2.image continuous_fst
  refine hc.of_isClosed_subset (isClosed_tsupport _) ?_
  have h1 : IsClosed ((fun x => (x, y)) ⁻¹' tsupport T) := (isClosed_tsupport T).preimage (Continuous.prodMk_left y)
  refine (closure_minimal ?_ h1).trans ?_
  · intro x hx; exact subset_tsupport T hx
  · intro x hx; exact ⟨(x, y), hx, rfl⟩

end GlobalTheory.TestFn
