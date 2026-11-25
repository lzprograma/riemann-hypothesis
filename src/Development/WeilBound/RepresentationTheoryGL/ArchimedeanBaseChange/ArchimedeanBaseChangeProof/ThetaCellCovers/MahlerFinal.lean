module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.Mahler

@[expose] public section

namespace PositivityTheory.Rg.BcB.E1

open D1

theorem mahlerC_holds : MahlerC := mahlerC_of_deg degBasis degAdelic degBdd degRat

alias mahler_holds := _root_.PositivityTheory.Rg.BcB.D1.mahler

end PositivityTheory.Rg.BcB.E1
