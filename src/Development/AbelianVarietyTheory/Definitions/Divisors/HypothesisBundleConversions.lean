module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport

@[expose] public section

namespace GlobalTheory.Mem.LiteralAutomorphy

def JoinOut : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator ∧ GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport ∧ GlobalTheory.ToricTransport.TwistedTransport ∧
    GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators ∧ GlobalTheory.SqTop.Refl

end GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Fc.S0


end GlobalTheory.Fc.S0
