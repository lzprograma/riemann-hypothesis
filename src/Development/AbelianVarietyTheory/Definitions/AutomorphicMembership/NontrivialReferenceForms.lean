module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
public import Formalism.LocalRingCardinality.DataKap
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ModelLamPDef

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.RowsRestModel

namespace GlobalTheory.Mem.Df.Model

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : TC.Laws I) (hX : B.fields.Ok)



theorem exists_ka (B : Base) : ∃ (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ),
    ∀ (C : Cols B) (W : RowsRest B C), W.kaBig = kb → W.kaSmall = ks → ∀ V S N G, DV.KapDef (assemble B C W V S N G) := by
  by_cases h : ∃ (C : Cols B) (W : RowsRest B C) (_ : DivStage B C W) (_ : SStage B C W) (_ : NStage B C W), Nonempty (GJStage B C)
  · obtain ⟨C, W, V, S, N, ⟨G⟩⟩ := h
    obtain ⟨kb, ks, hk⟩ := DV.exists_blocks (assemble B C W V S N G)
    refine ⟨kb, ks, fun C' W' h1 h2 V' S' N' G' j _ _ τ => ⟨fun i => ?_, fun c => ?_⟩⟩
    · show ((W'.kaBig j τ i : ℤ) : ℚ) = _
      rw [h1]
      exact (hk j τ).1 i
    · show ((W'.kaSmall j τ c : ℤ) : ℚ) = _
      rw [h2]
      exact (hk j τ).2 c
  · exact ⟨0, 0, fun C W _ _ V S N G => absurd ⟨C, W, V, S, N, ⟨G⟩⟩ h⟩





end GlobalTheory.Mem.Df.Model

end
