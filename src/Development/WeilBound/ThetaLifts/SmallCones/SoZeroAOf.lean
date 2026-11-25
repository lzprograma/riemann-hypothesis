module

public import Development.WeilBound.ThetaLifts.CTKernel
public import Development.WeilBound.ThetaLifts.SmallCones.SoDefs
public import Development.WeilBound.ThetaLifts.SmallCones.FormSwapZero
public import Development.WeilBound.ThetaLifts.SmallCones.LinExOf
public import Development.WeilBound.ThetaLifts.SmallCones.SoZero

@[expose] public section

namespace PositivityTheory.ThKCT

theorem soEv_of' (hLow : Low) : SoEv := soEv_of linEx_of hLow

theorem soZeroA'_of' (hX : PositivityTheory.ThKG.MixX) (hE : ThetaExp) (hU : EvUniq) : SoZeroA' := soZeroA'_of linEx_of hX hE hU

end PositivityTheory.ThKCT
