module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership

open NumberField IsDedekindDomain Formalism.IndefR.Arith

section Level

open Formalism.BasicNotions Formalism.L2.DIV

variable (D : D7) {LL : Type} [Field LL]

abbrev TypePl : Type := Σ k : Fin 2, D.nd.PlG k

instance finiteLevelGroupFintype : Fintype (G0g D.nd) :=
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  Fintype.ofFinite _

end Level

end GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership
