module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm

@[expose] public section

open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn


theorem _root_.GlobalTheory.T.continuous_standardUnitaryChart_and_symm : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → Continuous κ ∧ Continuous κ.symm := by
  first | exact @GlobalTheory.StdUnn.chart_continuous
