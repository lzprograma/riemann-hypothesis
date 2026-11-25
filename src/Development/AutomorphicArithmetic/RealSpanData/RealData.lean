module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import ReciprocityTheory.ClassFieldTheory.LocalClassField.HerbrandA

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU

namespace UpperTheory.ComplexUniformization

variable {p : ℕ} [Fact p.Prime]

def TypeAt (D : Datum p) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) : Prop :=
  ∀ c : 𝓞 D.F, (ρ (algebraMap (𝓞 D.F) D.O c)).trace = (D.m : ℂ) * (∑ i, D.tau i (c : D.F) +
    ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F) -
    ∑ i, (starRingEnd ℂ) (D.tau i (c : D.F)))

variable {D : Datum p} {G : HTGroup p}

end UpperTheory.ComplexUniformization
