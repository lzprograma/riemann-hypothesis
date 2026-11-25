module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3

theorem _root_.GlobalTheory.T.heisenbergOriented_finite_fixes_fockPolynomialVectors : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsInfFam θ → ∀ sS sT BS BT f, (∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f φ)) → ∀ u : WO S T, u.map (infPart D) = 0 → heisO ψ S T u f = f → ∀ φ, heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT f φ) = pureTensorO ψ θ S T sS sT BS BT f φ := by
  first | exact @GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite
