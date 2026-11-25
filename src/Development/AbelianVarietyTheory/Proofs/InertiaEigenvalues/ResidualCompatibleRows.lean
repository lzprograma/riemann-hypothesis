module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolyEqOfIsRowPar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section

noncomputable section

namespace GlobalTheory.ResLoc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.EigTie (IsRowPar plRed)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)

theorem continuous_qCast {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (ι : Qbar p ≃+* ℂ) {Y : Type} [TopologicalSpace Y]
    {f : Y → Qbar q} (hf : Continuous f) : Continuous fun y => ι.symm (qCast h ι (f y)) := by
  subst h
  simpa [qCast] using hf

def plL {D : D7} (L : LocAll (lay0 D)) (Pl : PlSide D) : PlSide (withLoc L) := ⟨Pl.ι, Pl.ι_w, Pl.plB, Pl.plB_eq, Pl.plκ⟩




end GlobalTheory.ResLoc

end
