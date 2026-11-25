module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqExtension
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviCompHol
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviFSInvariant
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviHolPerturb
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviLogFlat
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionNormSqExtension
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftGraphFactor
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphFactor
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftGraphMetric
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphMetric

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SectionNormSqExtension.closed : SectionNormSqExtension.Statement :=
  SectionNormSqExtension.proof LeviLogFlat.proof LeviHolPerturb.proof LeviCompHol.proof LeviFSInvariant.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

theorem LiftGraphFactor.closed : LiftGraphFactor.Statement :=
  LiftGraphFactor.proof GroundTheory.Heights₂.Heights.HilbertSamuel.SectionNormSqExtension.closed

end GroundTheory.Heights₂.Heights.Targets
end -- clump:auto
end -- clump:auto

section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_LiftGraphMetric : GroundTheory.Heights₂.Heights.Targets.LiftGraphMetric.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.LiftGraphMetric.proof GroundTheory.Heights₂.Heights.Targets.LiftGraphFactor.closed
end -- clump:auto
end -- clump:auto
