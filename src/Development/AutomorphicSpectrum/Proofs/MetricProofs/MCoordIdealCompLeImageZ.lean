module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.ImageIdeal

theorem mCoordIdeal_comp_le_imageZ : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K']
    (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K' → K) (v : (Σ k, ι' k) → Σ k, ι k) (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ), IsBlockMap κ v → mCoordIdeal (y ∘ v) ≤ imageZ v (mCoordIdeal y) := by
  intro K _ ι _ K' _ ι' _ κ v Φ _ y hv f hf
  have key : ∀ g : MRing ι', mConeMap y (rename v g) = rename κ (mConeMap (y ∘ v) g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, hv.2.2.1 n]
  have hf' : mConeMap (y ∘ v) f = 0 := hf
  show mConeMap y (rename v f) = 0
  rw [key, hf', map_zero]

end GlobalTheory.CompanionTheory.Ar.PB.FA.ImageIdeal
