module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem relAmple_powObj_boxLB : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (j : ℕ), Out.RelAmple (Out.powObj P.A j) (Out.boxLB P.L (Out.powPr P.A (n := j))) :=
  fun _ _ P j => relAmple_boxLB _ _ _ j (Out.powIsPowGrp P.A j) P.L P.isLB P.ample

end GlobalTheory
