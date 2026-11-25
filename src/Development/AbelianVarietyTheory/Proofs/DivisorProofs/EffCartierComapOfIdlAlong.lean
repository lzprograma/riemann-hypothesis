module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.NormalisedBlowupCone
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdlAlongEqIdealAlong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.NormBlLift

theorem effCartier_comap_of_idlAlong {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (a : Sp R ⟶ X) (f : R) (hf : f ≠ 0) (hJ : idlAlong J a = Ideal.span {f}) :
    FinalTheorems.EffCartier (J.comap a) := by
  rw [idlAlong_eq_idealAlong, GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone.idealAlong] at hJ
  set e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv with he
  have hI : (J.comap a).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {e.symm f} := by
    have h2 := congrArg (Ideal.map e.symm.toRingHom) hJ
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_map] at h2
    have : e.symm.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = RingHom.id _ := by
      ext x; exact e.symm_apply_apply x
    rw [this, Ideal.map_id] at h2
    exact h2
  intro x
  refine ⟨⟨⊤, isAffineOpen_top _⟩, e.symm f, trivial, ?_, hI⟩
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · apply e.injective
    have := congrArg e hz
    rw [map_mul, map_zero, e.apply_symm_apply] at this
    rw [map_zero]; exact (mul_eq_zero.1 this).resolve_left hf
  · apply e.injective
    have := congrArg e hz
    rw [map_mul, map_zero, e.apply_symm_apply] at this
    rw [map_zero]; exact (mul_eq_zero.1 this).resolve_right hf

end GlobalTheory.NormBlLift
