module

public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant

@[expose] public section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.UpqHaarRight

alias isMulRightInvariant := _root_.GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure

end GlobalTheory.UpqHaarRight
