module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Formalism.LocalRingCardinality.DataHost
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG Polynomial GlobalTheory.SphPar GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.SphGal

def spehInf (d : ℕ) (A : Multiset ℂ) : Multiset ℂ :=
  ∑ j : Fin d, A.map (· + (((d : ℂ) - 1) / 2 - (j : ℕ)))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (M : DSModel V S)

end GlobalTheory.SphGal

end
