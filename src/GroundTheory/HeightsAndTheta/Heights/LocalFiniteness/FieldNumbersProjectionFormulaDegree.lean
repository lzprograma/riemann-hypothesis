module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalLengthSum
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFiniteAlgebraLengthSum
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLengthSum
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalMaxIdeals
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleMinimal
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreRelDim
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivPushForwardLocal
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForwardLocal
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivPushForward
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForward
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLengthSum.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLengthSum.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLengthSum.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.FibreFinite.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocalRing GroundTheory.Heights₂.Heights.FieldNumbers.FiniteAlgebraLengthSum.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalMaxIdeals
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLength.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLength.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLength.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLengthSum GroundTheory.Heights₂.Heights.FieldNumbers.FibreRelDim.proof GroundTheory.Heights₂.Heights.FieldNumbers.DivCycleMinimal.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForwardLocal.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForwardLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForwardLocal.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DivCycleMinimal.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocalRing GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLength
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForward.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForwardLocal
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ProjectionFormulaDegree.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.CutRational.full GroundTheory.Heights₂.Heights.FieldNumbers.IntNumBase.full GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaContracted.full GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForward
end -- clump:auto
end -- clump:auto
