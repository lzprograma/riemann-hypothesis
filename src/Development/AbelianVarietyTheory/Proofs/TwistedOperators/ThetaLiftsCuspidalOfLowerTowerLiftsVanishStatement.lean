module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftsCuspidalOfLowerTowerLiftsVanish

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
open GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish : ∀ (D : D7) (X : ProvA), Inputs D X → LowAll D X → CuspAll D X := by
  first | exact @GlobalTheory.PairLift.cuspAll_of_lowAll
