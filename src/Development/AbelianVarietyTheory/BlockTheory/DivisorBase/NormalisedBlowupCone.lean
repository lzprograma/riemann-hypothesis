module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal

namespace GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Blow

def idealAlong {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] (χ : Sp R ⟶ X) : Ideal R :=
  ((J.comap χ).ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom

end Blow

end GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone
