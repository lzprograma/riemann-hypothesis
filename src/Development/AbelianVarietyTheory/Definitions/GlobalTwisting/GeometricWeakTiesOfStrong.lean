module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlacesOfCondition
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

@[expose] public section

noncomputable section

namespace GlobalTheory.Fc.S0

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

def RowRat : Prop :=
  StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → CoreP z → GIs2 K w Z.G → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)

end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

def NL (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

end GlobalTheory.Fc.S0

end
