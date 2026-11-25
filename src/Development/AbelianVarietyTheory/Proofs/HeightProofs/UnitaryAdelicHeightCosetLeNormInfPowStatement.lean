module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryAdelicHeightCosetLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.unitaryAdelicHeight_coset_le_normInf_pow : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), ∃ M : ℕ, ∀ x : GA D V, ∃ C : ℝ, ∀ g ∈ GinfC V, (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V (x * g) : ℝ) ≤ C * normInf θ V g ^ M := by
  first | exact @GlobalTheory.SmoothForms.HeightCoset.height_le_normInf_pow
