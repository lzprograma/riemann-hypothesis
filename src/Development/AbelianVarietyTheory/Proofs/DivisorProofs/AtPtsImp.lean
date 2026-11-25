module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.PieriBlockIdeals.MertensReciprocalElementary
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

namespace GlobalTheory.ExpTie

def parOf {D : D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) : Par where
  k := D.R.k
  m := D.R.m
  t := D.R.t
  f := D.R.f
  n := D.R.n
  Nr := (Vc D j).rank
  L := L.sc.L
  x := L.sc.x
  b' := L.sc.b'
  η := L.etaSz
  S := L.Sc

end GlobalTheory.ExpTie

end
