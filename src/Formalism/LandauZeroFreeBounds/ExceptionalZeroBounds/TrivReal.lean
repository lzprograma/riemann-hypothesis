module

import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LFunctionConj
public import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic.Linter.Style

@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem realCharConj : RealConj := by
  intro q _ χ hχ _ s
  have hinv : χ⁻¹ = χ := (isSelfInv_iff_sq_eq_one.mpr hχ).inv_eq
  simpa only [hinv] using Deduction.LFunction_conj χ s

end Formalism.ZeroFreeDirichlet
