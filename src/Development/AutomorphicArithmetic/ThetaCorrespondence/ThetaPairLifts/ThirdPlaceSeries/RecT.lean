module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

@[expose] public section



section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.DefiniteBC
namespace GlobalTheory.FormDict
def recT_alt {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (T : GlobalTheory.RowTie.WDTie N A)
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : RecMap A :=
  fun w _ σ => (T.e w).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (N.plOm.2 w) (GlobalTheory.LocLanglands.cls (ParLaws.toRep σ)))
end GlobalTheory.FormDict
end
end
