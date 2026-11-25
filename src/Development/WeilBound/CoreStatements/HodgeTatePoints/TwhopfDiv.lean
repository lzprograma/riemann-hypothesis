module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFlatFibresDvr
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseChangeTestOfSurjectiveMulAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionApplyEqOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatOfQuasiFiniteOfFlatFibres
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapLocallyQuasiFinite
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Twhopf


theorem mul_flat : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ N : ℕ, 1 ≤ N → Flat ((𝟙 G) ^ N).left := by
  intro S _ G _ hG N hN
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have hm : IsMonHom ((𝟙 G) ^ N) := GlobalTheory.AbLaw.MulN.isMonHom_mulA G N
  have hq : LocallyQuasiFinite ((𝟙 G) ^ N).left := locallyQuasiFinite_pow_semiAbelian S G hG N hN
  have : QuasiCompact (((𝟙 G) ^ N).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact ((𝟙 G) ^ N).left := QuasiCompact.of_comp _ G.hom
  exact flat_of_flatOver_fields _ G.hom inferInstance (by rw [Over.w]; infer_instance)
    (by rw [Over.w]; infer_instance) hq fun k _ s =>
      GlobalTheory.FibreFlat.flatOver_of_pullback _ s (GlobalTheory.IntDiv.flat_fibre G _ k s)

theorem points_div : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (x : Spec (CommRingCat.of V) ⟶ S) (N : ℕ), 1 ≤ N → ∀ c : Over.mk x ⟶ G, ∃ c' : Over.mk x ⟶ G, c' ^ N = c := by
  intro V _ _ _ _ S _ G _ hG x N hN c
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have hi := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  let φ : G ⟶ G := (𝟙 G) ^ N
  have hφ : mulN G N = φ := by
    have := GlobalTheory.ZJ.OmTest.comp_mulN (𝟙 G) N
    rwa [Category.id_comp] at this
  have hq : LocallyQuasiFinite φ.left := locallyQuasiFinite_pow_semiAbelian S G hG N hN
  have hf : Flat φ.left := mul_flat S G hG N hN
  have : LocallyOfFiniteType (φ.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType φ.left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact (φ.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact φ.left := QuasiCompact.of_comp _ G.hom
  have : IsSeparated (φ.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated φ.left := IsSeparated.of_comp _ G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : LocallyOfFinitePresentation φ.left := inferInstance
  have ho : IsOpen (Set.range φ.left) := φ.left.isOpenMap.isOpen_range
  have hs : Function.Surjective φ.left := by
    have := GlobalTheory.ZJ.OmTest.surjective_mulN G N (by rw [hφ]; exact ho)
    rwa [hφ] at this
  obtain ⟨g, hg⟩ := hs (c.left (IsLocalRing.closedPoint V))
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ.left) (g := c.left) g
    (IsLocalRing.closedPoint V) hg
  obtain ⟨s, hs', -⟩ := GlobalTheory.exists_section_of_quasiFinite_flat V (FractionRing V) _
    (pullback.snd φ.left c.left) z hz
  have e : (s ≫ pullback.fst φ.left c.left) ≫ φ.left = c.left := by
    rw [Category.assoc, pullback.condition, reassoc_of% hs']
  refine ⟨Over.homMk (s ≫ pullback.fst φ.left c.left) ?_, ?_⟩
  · have h1 := Over.w φ
    have h2 := Over.w c
    rw [← h1, ← Category.assoc, e]
    exact h2
  · rw [← Category.comp_id (Over.homMk _ _), ← MonObj.comp_pow]
    exact Over.OverMorphism.ext e

end PositivityTheory.HtPt.Twhopf
