module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem functionFieldMap_bijective_of_isIso_restrict : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (U : X.Opens), (U : Set X).Nonempty → IsIso (s ∣_ U) → Function.Bijective (functionFieldMap s) := by
  intro X Y _ _ s _ U hU hiso
  have hg : s (genericPoint Y) = genericPoint X := by
    have h := (genericPoint_spec Y).image s.continuous
    rw [Set.image_univ, s.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec X)
  have hmem : genericPoint Y ∈ s ⁻¹ᵁ U := by
    change s (genericPoint Y) ∈ U
    rw [hg]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have h1 : IsIso ((s ∣_ U).stalkMap ⟨genericPoint Y, hmem⟩) :=
    ((isIso_iff_isIso_stalkMap (s ∣_ U)).1 hiso).2 _
  have h2 : IsIso (s.stalkMap (genericPoint Y)) :=
    ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap s U ⟨genericPoint Y, hmem⟩)).mp h1
  have h3 : ∀ (x y : X) (_ : x = y) (h : x ⤳ y), IsIso (X.presheaf.stalkSpecializes h) := by
    rintro x y rfl h
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  unfold functionFieldMap
  have h4 := h3 _ _ hg (hg ▸ specializes_rfl)
  exact ConcreteCategory.bijective_of_isIso _

end GlobalTheory.Discrepancy
