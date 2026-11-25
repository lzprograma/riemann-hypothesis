module

import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatDesc
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.ExtSpan

theorem extOrder_eq_span : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (R' : Type) [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) (g : T → R'), g ∈ extOrder φ A ↔ g ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} := by
  apply PositivityTheory.HtPt.Htat.ext_span

end GlobalTheory.CompanionTheory.Ar.BT.ExtSpan
