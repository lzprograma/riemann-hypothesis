module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ContinuousAtOfClosedRel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiniteSeparatingModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNoetherProjection
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNonvanishingDense
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolyNonvanishDense
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatPrimeDense
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsNear
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsLiftToZeros

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

open GroundTheory.Heights₂.Heights.HilbertSamuel in
theorem nonvanishing_dense : NonvanishingDense.Statement :=
  NonvanishingDense.proof (RatPrimeDense.proof (FiniteSeparatingModel.proof NoetherProjection.proof
    _root_.GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.proof)
    RootsNear.proof RootsBounded.proof PolyNonvanishDense.proof)

open HolomorphicMinorCharts in
theorem r_onto : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e), IsArithVar P (e + 1) → ∀ z ∈ mcPts P, ∃ x, SameOrbit (R.lift x x) z := by
  intro K _ ι _ P J e R hP z hz
  obtain ⟨f, hfJ, hfP⟩ := Set.not_subset.mp R.nondeg
  have hcl := isClosed_minors (U := R.U) (lam := R.lift) (V := fun _ : (Σ k, ι k) → ℂ => Set.univ)
    (mu := fun _ w => w) (fun x => ⟨R.isOpen_U x, R.mem_U x⟩)
    (fun x p => holo_continuousAt (R.holo x p) (R.mem_U x)) R.compat (fun _ => ⟨isOpen_univ, trivial⟩)
    (fun y p => (continuous_apply p).continuousAt) (fun _ _ w _ => so_refl w)
  have hc := isClosedMap_snd_of_compactSpace _ hcl
  have h1 := nonvanishing_dense K ι P (e + 1) f hP hfP hz
  have h2 := closure_minimal (fun w hw => by
    obtain ⟨x, hx⟩ := R.surj w hw.1 fun hJ => hw.2 (hJ.2 f hfJ)
    exact ⟨(x, w), minors_of_so hx, rfl⟩) hc h1
  obtain ⟨⟨x, w⟩, hx, rfl⟩ := h2
  exact ⟨x, so_of_minors hx (R.mem x x (R.mem_U x)).1 hz.1⟩

end PositivityTheory.UnitarySelfGeneration
