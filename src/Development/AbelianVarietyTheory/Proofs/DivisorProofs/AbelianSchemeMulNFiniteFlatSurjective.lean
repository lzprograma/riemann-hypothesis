module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.DeRham (spOver)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.MulFlatSurj

alias mulN_eq_pow := _root_.GlobalTheory.GrpTangent.mulN_eq_pow

theorem finite_flat_surjective_mulN : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ n : ℕ, 0 < n →
      IsFinite (mulN A n).left ∧ Flat (mulN A n).left ∧ Surjective (mulN A n).left := by
  intro R _ A _ hA n hn
  obtain ⟨h1, h2⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA (Sp R) A hA n hn
  have e : mulN A n = ReciprocityTheory.ChartRestriction.G.Out.mulA A n := mulN_eq_pow A n
  rw [e]
  refine ⟨h1, h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_⟩
  have hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A n)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hf ⊢
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hBc := hB.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ n) hf).2

end GlobalTheory.MulFlatSurj
