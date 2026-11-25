module

public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
public import Development.WeilBound.ThetaLifts.LatticeBasics.CartanBound2
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtIntOf

@[expose] public section

namespace GlobalTheory.ThK.Dbl

theorem hgtEx : HgtEx := hgtEx_of stab2Cpt

theorem hgtInt : HgtInt := hgtInt_of stab2Cpt

end GlobalTheory.ThK.Dbl
