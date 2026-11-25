module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.WeilBound.ThetaLifts.Reductions.LieScalar2
public import Development.WeilBound.ThetaLifts.Reductions.LocalLift
import Formalism.LocalRingCardinality.DataTheta

@[expose] public section

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.real_lift_lie_second_order : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond :=
  fun _ hD _ _ _ => PositivityTheory.ThKR.lieSecond2 PositivityTheory.ThKR.localLift_holds hD
end
