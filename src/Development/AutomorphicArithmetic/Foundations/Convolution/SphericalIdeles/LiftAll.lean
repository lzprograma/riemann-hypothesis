module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.Ci
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.GmOfBcfl
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreLift
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftAll
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftStep
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.BcflUnit

@[expose] public section

theorem UpperTheory.ConvolutionTheory.Sph.gm : UpperTheory.ConvolutionTheory.GM.GM := UpperTheory.ConvolutionTheory.GM.gm_of_bcfl PositivityTheory.Rg.Tf.Loc.bcflUnit

theorem UpperTheory.ConvolutionTheory.Sph.liftAll : UpperTheory.ConvolutionTheory.T.LiftAll :=
  UpperTheory.ConvolutionTheory.T.liftAll (UpperTheory.ConvolutionTheory.T.liftStep (UpperTheory.ConvolutionTheory.T.coreLift UpperTheory.ConvolutionTheory.ci UpperTheory.ConvolutionTheory.Sph.gm))
