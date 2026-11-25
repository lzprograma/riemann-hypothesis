module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.UnitsDense

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem denseRange_embeddings' : DenseRange fun (x : E) (w : InfinitePlace E) => w.embedding x := by
  have h1 := NumberField.InfiniteAdeleRing.denseRange_algebraMap E
  have hs : Function.Surjective
      (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w) := by
    intro y
    choose x hx using fun w : InfinitePlace E =>
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w) (y w)
    exact ⟨x, funext hx⟩
  have hc : Continuous (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w) :=
    continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have := hs.denseRange.comp h1 hc
  convert this using 1
  funext x w
  change w.embedding x = InfinitePlace.Completion.extensionEmbedding w (algebraMap E (InfiniteAdeleRing E) x w)
  rw [InfiniteAdeleRing.algebraMap_apply]
  have := InfinitePlace.Completion.extensionEmbedding_coe (v := w) ((WithAbs.equiv w.1).symm x)
  simp only [RingEquiv.apply_symm_apply] at this
  rw [← this]
  rfl

end GlobalTheory.UnitsDense
