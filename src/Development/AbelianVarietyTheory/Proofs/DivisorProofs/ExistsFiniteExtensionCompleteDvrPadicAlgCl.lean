module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallEqOfIntegralDvr

@[expose] public section

open IsLocalRing

namespace GlobalTheory.DvrFinExt

theorem exists_finite_intermediateField (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F Ω]
    [Algebra.IsIntegral F Ω] [Algebra K Ω] (hQ : ∀ q : F, algebraMap F Ω q ∈ (algebraMap K Ω).range)
    (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (y₀ : R →+* Ω) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ ∀ a, y₀ a ∈ L := by
  let e := RingEquiv.ofBijective (algebraMap K Ω).rangeRestrict
    ⟨(algebraMap K Ω).rangeRestrict.injective, (algebraMap K Ω).rangeRestrict_surjective⟩
  let u : F →+* K := e.symm.toRingHom.comp ((algebraMap F Ω).codRestrict _ hQ)
  have hu : (algebraMap K Ω).comp u = (RingHom.id Ω).comp (algebraMap F Ω) :=
    RingHom.ext fun q => congrArg Subtype.val (e.apply_symm_apply _)
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := R)
  have : Finite (y₀ '' (s : Set R)) := (s.finite_toSet.image y₀).to_subtype
  let L := IntermediateField.adjoin K (y₀ '' (s : Set R))
  refine ⟨L, IntermediateField.finiteDimensional_adjoin fun x _ =>
      IsIntegral.map_of_comp_eq u (RingHom.id Ω) hu (Algebra.IsIntegral.isIntegral (R := F) x),
    fun a => ?_⟩
  have hle : Algebra.adjoin ℤ (s : Set R) ≤ (L.toSubalgebra.restrictScalars ℤ).comap y₀.toIntAlgHom :=
    Algebra.adjoin_le fun x hx => IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
  exact hle (hs ▸ Algebra.mem_top)

theorem exists_finite_extension : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range) → ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (y₀ : R →+* PadicAlgCl p), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (maximalIdeal W) W) (_ : CharZero W) (fV : V →+* W) (fK : FractionRing V →+* FractionRing W) (κ' : FractionRing W →+* PadicAlgCl p), Function.Injective fV ∧ IsLocalHom fV ∧ fV.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap W _ (fV a)) ∧ κ'.comp fK = κ ∧ (∀ x, ‖κ' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧ ∀ a, y₀ a ∈ κ'.range := by
  intro p _ V _ _ _ _ hc κ hκ hQ R _ _ y₀
  let : Algebra (FractionRing V) (PadicAlgCl p) := κ.toAlgebra
  obtain ⟨L, _, hy⟩ := exists_finite_intermediateField ℚ_[p] (FractionRing V) (PadicAlgCl p) hQ R y₀
  obtain ⟨W, _, _, _, hcW, _, _, _, hcomp, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  have : CharZero W := charZero_of_injective_ringHom hinj
  let e := FractionRing.algEquiv W L
  let κ' : FractionRing W →+* PadicAlgCl p := L.val.toRingHom.comp e.toRingEquiv.toRingHom
  let fK : FractionRing V →+* FractionRing W :=
    e.symm.toRingEquiv.toRingHom.comp (algebraMap (FractionRing V) L)
  have hfK : ∀ a, fK (algebraMap V _ a) = algebraMap W _ (algebraMap V W a) := fun a =>
    e.injective <| (e.apply_symm_apply _).trans <|
      (congrArg (fun g : V →+* L => g a) hcomp).symm.trans (e.commutes _).symm
  have hκ' : κ'.comp fK = κ :=
    RingHom.ext fun x => congrArg Subtype.val (e.apply_symm_apply (algebraMap (FractionRing V) L x))
  have : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  refine ⟨W, inferInstance, inferInstance, inferInstance, hcW, inferInstance, algebraMap V W, fK,
    κ', hinj, hloc, RingHom.finite_algebraMap.2 hfin, hfK, hκ',
    GlobalTheory.unitBall_eq_of_integral_dvr p V W hinj κ κ' (fun v => ?_) hκ,
    fun a => ⟨e.symm ⟨y₀ a, hy a⟩, congrArg Subtype.val (e.apply_symm_apply ⟨y₀ a, hy a⟩)⟩⟩
  rw [← hfK]
  exact congrArg (fun g : FractionRing V →+* PadicAlgCl p => g (algebraMap V (FractionRing V) v)) hκ'

end GlobalTheory.DvrFinExt
