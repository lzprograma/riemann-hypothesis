module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallEqOfIntegralDvr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.GCTrait

theorem exists_ext_emb (p : ℕ) [Fact p.Prime] (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W) (fK : FractionRing V →+* FractionRing W)
    (hinj : Function.Injective f) (hloc : IsLocalHom f) (hfin : f.Finite)
    (hc : ∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) (κ : FractionRing V →+* PadicAlgCl p)
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ ι : FractionRing W →+* PadicAlgCl p, ι.comp fK = κ ∧
      ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)) := by
  let : Algebra V W := f.toAlgebra
  let : Algebra (FractionRing V) (FractionRing W) := fK.toAlgebra
  let : Algebra (FractionRing V) (PadicAlgCl p) := κ.toAlgebra
  have : Algebra.IsIntegral V W := ⟨fun w => hfin.to_isIntegral w⟩
  have : IsLocalHom (algebraMap V W) := hloc
  have hint : ∀ w : W, IsIntegral (FractionRing V) (algebraMap W (FractionRing W) w) := fun w =>
    IsIntegral.map_of_comp_eq (algebraMap V (FractionRing V)) (algebraMap W (FractionRing W))
      (RingHom.ext hc) (Algebra.IsIntegral.isIntegral w)
  have : Algebra.IsAlgebraic (FractionRing V) (FractionRing W) := ⟨fun z => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) z
    rw [div_eq_mul_inv]
    exact ((hint a).mul (hint b).inv).isAlgebraic⟩
  let ι : FractionRing W →ₐ[FractionRing V] PadicAlgCl p := IsAlgClosed.lift
  exact ⟨ι.toRingHom, RingHom.ext ι.commutes,
    GlobalTheory.unitBall_eq_of_integral_dvr p V W hinj κ ι.toRingHom
      (fun v => by show ι (algebraMap W (FractionRing W) (f v)) = _; rw [← hc]; exact ι.commutes _) hV⟩

end GlobalTheory.Poinc.GCTrait
