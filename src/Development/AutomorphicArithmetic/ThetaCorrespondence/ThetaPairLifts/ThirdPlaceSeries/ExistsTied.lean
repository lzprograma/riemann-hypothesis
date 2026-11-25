module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
noncomputable section
namespace GlobalTheory.HeightCounting.Up.RealOfReading
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie
theorem exists_linked_data_of_agreement {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) {cf : CharFrame D} {nch : NChoice D}
    {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp) (hcf : P.cf = cf) (hC : P.C = nch) (htp : HEq P.tp tp)
    {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (hM : P.M = M) (hrep : HEq P.rep rep)
    (ag : GlobalTheory.NJoin.Agree X M rep) (e0 : GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector X) :
    ∃ T : _root_.GlobalTheory.NRows.LinkedData hL D, T.P = P ∧ HEq T.X.R X.R := by
  subst hcf
  subst hC
  cases eq_of_heq htp
  subst hM
  cases eq_of_heq hrep
  exact ⟨⟨P, X, ag, e0⟩, rfl, HEq.rfl⟩
end GlobalTheory.HeightCounting.Up.RealOfReading
end
end
