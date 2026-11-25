module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.unitaryLatticeDenominatorHeightBound_proof : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), DenomBound θ V := by
  first | exact @GlobalTheory.SmoothForms.denomBound
