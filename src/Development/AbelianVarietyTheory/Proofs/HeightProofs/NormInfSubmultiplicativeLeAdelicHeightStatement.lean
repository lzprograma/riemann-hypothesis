module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NormInfSubmultiplicativeLeAdelicHeight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.normInf_submultiplicative_le_adelicHeight : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), (∀ g h : GA D V, normInf θ V (g * h) ≤ normInf θ V g * normInf θ V h) ∧ ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) := by
  first | exact @GlobalTheory.SmoothForms.normInf_mul_le_and_le_height
