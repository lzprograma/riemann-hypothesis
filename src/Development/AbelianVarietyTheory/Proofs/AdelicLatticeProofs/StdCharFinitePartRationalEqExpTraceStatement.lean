module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct

theorem _root_.GlobalTheory.T.stdChar_finitePart_rational_eq_exp_trace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ x : D.host.F, ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) x)) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ)) := by
  first | exact @GlobalTheory.StdRat.stdChar_fin_rat
