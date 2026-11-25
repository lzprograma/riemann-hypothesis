module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CuspidalMultiplicityOne

@[expose] public section

namespace UpperTheory.V.Af

theorem strongMultOneC : StrongMultiplicityOne.StrongMultOneC :=
  fun E _ _ _ n π π' hs => congrArg GlobalTheory.CuspRep.CuspSub.V
    (PositivityTheory.jumpWindows.smooth_multiplicity_one_holds
      PositivityTheory.JacquetShalikaLocal.minuscule_eigenvalue
      PositivityTheory.JacquetShalikaLocal.satake_eigenvalue_formula E n π π' hs)

end UpperTheory.V.Af
