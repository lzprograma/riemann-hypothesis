module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Mathlib.Analysis.Matrix.Order
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder MatrixOrder
open Formalism.BasicNotions.TH GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace PositivityTheory.RL

theorem frameEx : GlobalTheory.RealLift.FrameEx := by
  apply GlobalTheory.RealLift.frameEx_holds

end PositivityTheory.RL
