module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryReductionPolynomialHeightBound

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.unitary_reduction_polynomial_height_bound : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam θ → OrthoSmall D.host.E → DenomBound θ V → ∃ (d : ℕ) (C : ℝ) (M : ℕ), 0 < d ∧ ∀ g : GA D V, ∃ γ ∈ GQ V, BddDen V d (γ * g) ∧ normInf θ V γ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ^ M := by
  first | exact @GlobalTheory.SmoothForms.Reduce.reduction
