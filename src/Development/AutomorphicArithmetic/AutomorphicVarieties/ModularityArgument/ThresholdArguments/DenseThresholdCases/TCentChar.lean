module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CentChar

@[expose] public section

theorem UpperTheory.V.Sd.Wc.centChar_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.Wc.CentChar :=
  fun _ => UpperTheory.V.Af.Rn.centChar
