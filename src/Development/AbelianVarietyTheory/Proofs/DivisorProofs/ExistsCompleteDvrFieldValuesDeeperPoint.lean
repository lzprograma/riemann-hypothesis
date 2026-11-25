module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionCompleteDvrPadicAlgCl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicMemRangeCompleteDvrPadicAlgCl
import Mathlib.Tactic.Linter.Style

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.ValField

theorem exists_fg_values {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (M : RatModel o Ω) {K : Type} [Field K] (y : Sp K ⟶ M.Z) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra.FiniteType ℤ R) (y₀ : R →+* K),
      ∀ E : Subfield K, (∀ r, y₀ r ∈ E) → ∀ a ∈ M.O (y (closedPoint K)), M.val y a ∈ E := by
  set z := y (closedPoint K) with hz
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := z) (U := ⊤) trivial
  have hne : (U : Set M.Z).Nonempty := ⟨z, hzU⟩
  have hr : Set.range y = {z} := RatModel.range_eq_singleton y _
  let φ : M.O z →+* K := RatModel.valHom y z hr
  let y₀ : Γ(M.Z, U) →+* K :=
    φ.comp ((Subalgebra.inclusion (RatModel.ringOn_le_O (M := M) hzU)).toRingHom.comp
      (M.sectionsEquiv U hne).toRingHom)
  have hy₀ : ∀ f, y₀ f = φ ⟨valF M.pt U f, RatModel.valF_mem_O hzU f⟩ := fun f => by
    show φ _ = φ _
    congr 1
    exact Subtype.ext (RatModel.coe_sectionsEquiv U hne f)
  have hft : Algebra.FiniteType ℤ Γ(M.Z, U) := by
    have h1 : (M.s.appLE ⊤ U (by simp)).hom.FiniteType :=
      M.lft.finiteType_appLE (isAffineOpen_top _) hU _
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of o)).commRingCatIsoToRingEquiv.symm.surjective
    have h3 : (algebraMap ℤ o).FiniteType := RingHom.finiteType_algebraMap.2 (ArithBase.ft (o := o) (Ω := Ω))
    have h4 := (h1.comp h2).comp h3
    rw [← RingHom.finiteType_algebraMap]
    convert h4
    exact Subsingleton.elim _ _
  refine ⟨Γ(M.Z, U), inferInstance, hft, y₀, fun E hE a ha => ?_⟩
  let Wo : M.Z.Opens := ⟨{w | a ∈ M.O w}, M.isOpen_setOf_mem_O a⟩
  obtain ⟨f, hfW, hzf⟩ := hU.exists_basicOpen_le (V := Wo) ⟨z, ha⟩ hzU
  have hnef : ((M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hzf⟩
  have har : a ∈ M.ringOn (M.Z.basicOpen f) := RatModel.mem_ringOn.2 fun w hw => hfW hw
  obtain ⟨s, hs⟩ := (RatModel.mem_ringOn_iff_exists hnef).1 har
  letI := hU.isLocalization_basicOpen f
  obtain ⟨n, r, hrn⟩ := IsLocalization.Away.surj f s
  have halg : ∀ g : Γ(M.Z, U), algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen f) g = resG M.Z (M.Z.basicOpen_le f) g :=
    fun _ => rfl
  have he := congrArg (M.res _ hnef) hrn
  rw [map_mul, map_pow, halg, halg, RatModel.res_resG, RatModel.res_resG, RatModel.res_apply, hs,
    RatModel.res_apply, RatModel.res_apply] at he

  have hO : (⟨a, ha⟩ : M.O z) * ⟨valF M.pt U f, RatModel.valF_mem_O hzU f⟩ ^ n =
      ⟨valF M.pt U r, RatModel.valF_mem_O hzU r⟩ := Subtype.ext (by simpa using he)
  have hφ := congrArg φ hO
  rw [map_mul, map_pow, ← hy₀, ← hy₀] at hφ
  have hf0 : y₀ f ≠ 0 := by
    rw [hy₀]
    exact (RatModel.val_ne_zero_iff hr _).2 ((RatModel.isUnit_valF_iff hzU f).2 hzf)
  have hval : M.val y a = y₀ r / y₀ f ^ n := by
    rw [← hφ, mul_div_cancel_right₀ _ (pow_ne_zero _ hf0)]
    rfl
  rw [hval]
  exact div_mem (hE r) (pow_mem (hE f) n)

end GlobalTheory.ValField
