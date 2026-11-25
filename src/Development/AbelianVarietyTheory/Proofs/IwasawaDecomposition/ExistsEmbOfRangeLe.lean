module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.Mem GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.Rw

theorem isIdG_unique (X : Stages) {px : PreX X.B.toPre} {Pg : Finset (Pl X.toD7.host.E)} (hPg : Pg = (X.B.primes px).vGs)
    {eG eG' : Gc X.B px ≃* G0 Pg X.toD7.R.r} (h : IsPlacewiseIdentity X (px := px) eG) (h' : IsPlacewiseIdentity X (px := px) eG') : eG = eG' := by
  subst hPg
  exact MulEquiv.ext fun g => funext fun P => (h g P.1 P.2 P.2).trans (h' g P.1 P.2 P.2).symm

alias isStdChar_unique := _root_.GlobalTheory.StdAdelicChar.isStdChar_unique

theorem isInfFam_unique {D : D7} {θ θ' : Formalism.IndefR.Datum.InfFam D} (h : IsInfFam θ) (h' : IsInfFam θ') : θ = θ' :=
  Formalism.IndefR.Eqv.infFamUnique_holds D θ θ' h h'


end GlobalTheory.Mem.R3.Rw

end
