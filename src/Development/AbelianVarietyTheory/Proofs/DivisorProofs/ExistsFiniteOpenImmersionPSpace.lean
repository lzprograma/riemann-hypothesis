module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Normalization
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteIntegralClosureOfIsIntegrallyClosed
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

namespace GlobalTheory.ZMain

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem finite_integralClosure_field (R L : Type*) [CommRing R] [Algebra.FiniteType ℤ R] [Field L]
    [Algebra R L] [Algebra.EssFiniteType R L] : Module.Finite R (integralClosure R L) := by
  rcases CharP.char_is_prime_or_zero L (ringChar L) with hp | h0
  · let p := ringChar L
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharP L p := ringChar.charP L
    let I := RingHom.ker (algebraMap R L)
    let R' := R ⧸ I
    letI : Algebra R' L := (Ideal.Quotient.lift I (algebraMap R L) fun _ h => h).toAlgebra
    haveI : IsScalarTower R R' L := .of_algebraMap_eq fun _ => rfl
    have hinj : Function.Injective (algebraMap R' L) := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    haveI : IsDomain R' := hinj.isDomain _
    haveI : FaithfulSMul R' L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    haveI : CharP R' p := ⟨fun n => by
      rw [← map_eq_zero_iff _ hinj, map_natCast, CharP.cast_eq_zero_iff L]⟩
    letI : Algebra (ZMod p) R' := (ZMod.castHom dvd_rfl R').toAlgebra
    haveI : Algebra.FiniteType ℤ R' := .trans (S := R) inferInstance inferInstance
    haveI : Algebra.FiniteType (ZMod p) R' := .of_restrictScalars_finiteType ℤ (ZMod p) R'
    haveI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing (ZMod p) R'
    haveI : Module.Finite R R' := Module.Finite.of_surjective (Algebra.linearMap R R')
      Ideal.Quotient.mk_surjective
    let F := FractionRing R'
    letI : Algebra F L := FractionRing.liftAlgebra R' L
    haveI : Algebra.EssFiniteType R' L := .of_comp R R' L
    haveI : Algebra.EssFiniteType F L := .of_comp R' F L
    let E := algebraicClosure F L
    haveI : FiniteDimensional F E := finiteDimensional_algebraicClosure_of_essFiniteType F L
    haveI : Module.Finite R' (integralClosure R' E) :=
      NormFin.finite_integralClosure_of_perfectField (ZMod p) R' F E
    haveI : IsScalarTower R' E L := .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply R' F L x, IsScalarTower.algebraMap_apply R' F E x,
        ← IsScalarTower.algebraMap_apply F E L]
    have hmem : ∀ z : integralClosure R' L, (z : L) ∈ E := fun z =>
      mem_algebraicClosure_iff.mpr (z.2.tower_top (A := F)).isAlgebraic
    let ψ : integralClosure R' L →ₗ[R'] integralClosure R' E :=
      { toFun := fun z => ⟨⟨z, hmem z⟩, (isIntegral_algHom_iff (IsScalarTower.toAlgHom R' E L)
            (IsScalarTower.toAlgHom R' E L).toRingHom.injective).mp z.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    haveI : Module.Finite R' (integralClosure R' L) := Module.Finite.of_injective ψ
      fun a b h => Subtype.ext (congrArg (fun w : integralClosure R' E => ((w : E) : L)) h)
    exact finite_integralClosure_of_finite_tower R R' L
  · haveI : CharZero L := (CharP.ringChar_zero_iff_CharZero L).mp h0
    exact finite_integralClosure_of_essFiniteType_field ℤ R L

universe u

end GlobalTheory.ZMain
