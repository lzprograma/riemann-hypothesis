module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem memLpSchA {κ : Type} [Fintype κ] (m : MeasurableSpace (κ → AF F)) (hm : m = borel _)
    (μ : @Measure (κ → AF F) m) (hμ : @Measure.IsAddHaarMeasure _ _ _ m μ) {φ : (κ → AF F) → ℂ}
    (hφ : φ ∈ schA F κ) : MemLp φ 2 μ := by
  subst hm
  exact GlobalTheory.WeilM.schA_memLp_two F κ μ hμ φ hφ

variable {d : SD σ}

end PositivityTheory.SiegelWeilFormula.KFP

end
