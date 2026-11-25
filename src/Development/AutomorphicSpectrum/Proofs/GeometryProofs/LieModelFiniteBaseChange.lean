module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLie

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieProj

alias lie_finite_projective_baseChange := _root_.PositivityTheory.HtPt.Htat.lie_proj

end GlobalTheory.CompanionTheory.Ar.LieProj
