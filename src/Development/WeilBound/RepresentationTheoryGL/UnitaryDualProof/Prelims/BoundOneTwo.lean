module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeInvariantOfConjInvariantDistributionGL
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast

@[expose] public section

noncomputable section

open Matrix Topology Filter ValuativeRel GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.GelfandKazhdan

namespace PositivityTheory.PfBern.cocyclesToWachVectorsExponent

section Top

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k] {m : ℕ}

variable [T2Space k]



end Top

section Dist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem t2Space_local : T2Space k := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  refine ⟨{y | valuation k y < valuation k x},
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem ((valuation k).ne_zero_iff.2 hx), ?_⟩
  exact fun h => lt_irrefl (valuation k x) h

theorem exists_clopen_local (C : Set k) (hC : IsCompact C) (h0 : (0 : k) ∉ C) :
    ∃ U : Set k, IsClopen U ∧ C ⊆ U ∧ (0 : k) ∉ U := by
  have := t2Space_local (k := k)
  have hCc : Cᶜ ∈ 𝓝 (0 : k) := hC.isClosed.isOpen_compl.mem_nhds h0
  obtain ⟨γ, hγ, hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.1 hCc
  let W : AddSubgroup k :=
    { carrier := {x | valuation k x < γ}
      add_mem' := fun {a b} ha hb =>
        show valuation k (a + b) < γ from lt_of_le_of_lt ((valuation k).map_add a b) (max_lt ha hb)
      zero_mem' := by
        show valuation k 0 < γ
        rw [map_zero]
        exact zero_lt_iff.2 hγ
      neg_mem' := fun {a} ha => by
        show valuation k (-a) < γ
        rw [Valuation.map_neg]
        exact ha }
  have hWn : (W : Set k) ∈ 𝓝 (0 : k) := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ
  have hWo : IsOpen (W : Set k) := AddSubgroup.isOpen_of_mem_nhds W hWn
  refine ⟨(W : Set k)ᶜ, ⟨hWo.isClosed_compl, (AddSubgroup.isClosed_of_isOpen W hWo).isOpen_compl⟩, ?_, ?_⟩
  · intro c hc hcW
    exact hsub hcW hc
  · exact fun h => h W.zero_mem

end Dist

end PositivityTheory.PfBern.cocyclesToWachVectorsExponent

end
