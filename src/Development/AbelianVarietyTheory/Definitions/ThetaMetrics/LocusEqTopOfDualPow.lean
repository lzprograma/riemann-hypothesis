module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso

@[expose] public section

noncomputable section

namespace GlobalTheory.AmpleModel

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LBGerm GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}}

variable (K : Type) [Field K] (N : ℕ)

def genericPt : ProjectiveSpectrum (grading K N) where
  asHomogeneousIdeal := ⊥
  isPrime := Ideal.isPrime_bot
  not_irrelevant_le h := by
    have := h (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (X_mem K N 0))
    exact X_ne_zero _ this

instance irreducibleSpace : IrreducibleSpace (PSpace K N) := by
  have h : closure {genericPt K N} = (Set.univ : Set (ProjectiveSpectrum (grading K N))) :=
    Set.eq_univ_of_forall fun x => (ProjectiveSpectrum.le_iff_mem_closure _ _ x).1 (show ⊥ ≤ x.asHomogeneousIdeal from bot_le)
  have h2 : IsIrreducible (Set.univ : Set (ProjectiveSpectrum (grading K N))) := h ▸ isIrreducible_singleton.closure
  exact (irreducibleSpace_def _).2 h2

instance isIntegral : IsIntegral (PSpace K N) := by
  have : ∀ i, IsReduced ((chartCover K N).X i) := fun i =>
    inferInstanceAs (IsReduced (Sp (MvPolynomial {j // j ≠ i} K)))
  have : IsReduced (PSpace K N) := IsReduced.of_openCover _ (chartCover K N)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.AmpleModel
