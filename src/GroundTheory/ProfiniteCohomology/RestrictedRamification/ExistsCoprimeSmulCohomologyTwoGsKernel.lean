module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.CupDecompositionGlobal
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerDefs
import GroundTheory.ProfiniteCohomology.Colimit
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.RealPlaces
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.Splitting
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerSplit
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerSplitLayers
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.EqZeroOfCohomologyInflThreeEqZero
import Mathlib.Algebra.Order.Star.Int
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog
public import GroundTheory.GlobalFields.NormResidueSymbol.CyclotomicCompositum
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalDegrees.Layers

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField IsDedekindDomain IntermediateField GroundTheory.Global

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

abbrev gsKernel : Subgroup K.1.fixingSubgroup := (gsRestrict K S).ker

theorem isClosed_gsKernel : IsClosed (gsKernel K S : Set K.1.fixingSubgroup) := by
  have ht2 : T2Space (galUnramifiedOutside K.1 ℚ̄ S) :=
    krullTopology_t2 (K := K.1) (L := maxUnramifiedOutside K.1 ℚ̄ S)
  have : T1Space (galUnramifiedOutside K.1 ℚ̄ S) := @T2Space.t1Space _ _ ht2
  exact (isClosed_singleton (x := (1 : galUnramifiedOutside K.1 ℚ̄ S))).preimage (continuous_gsRestrict K S)

theorem mem_gsKernel_iff (σ : K.1.fixingSubgroup) :
    σ ∈ gsKernel K S ↔ ∀ x ∈ maxUnramifiedOutside K.1 ℚ̄ S, (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) x = x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x hx
    have := congrArg (fun τ : galUnramifiedOutside K.1 ℚ̄ S =>
      ((τ ⟨x, hx⟩ : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) h
    rw [gsRestrict_apply] at this
    exact this
  · intro h
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [gsRestrict_apply]
    exact h x x.2

theorem exists_finiteSubfield_of_isOpen (U : Subgroup K.1.fixingSubgroup)
    (hU : IsOpen (U : Set K.1.fixingSubgroup)) (hNU : gsKernel K S ≤ U) :
    ∃ (L : FiniteSubfield) (_ : Fact (K ≤ L)), (∀ x ∈ L.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) ∧
      U = L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  let U' : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄) := U.map K.1.fixingSubgroup.subtype
  have hKo : IsOpen (K.1.fixingSubgroup : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := K.1.fixingSubgroup_isOpen
  have hU'o : IsOpen (U' : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
    have e : (U' : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) = Subtype.val '' (U : Set K.1.fixingSubgroup) := by
      ext σ
      simp [U', Subgroup.coe_map]
    rw [e]
    exact hKo.isOpenMap_subtype_val _ hU
  have hU'c : IsClosed (U' : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := Subgroup.isClosed_of_isOpen _ hU'o
  let L' : IntermediateField ℚ ℚ̄ := IntermediateField.fixedField U'
  have hfix : L'.fixingSubgroup = U' := InfiniteGalois.fixingSubgroup_fixedField ⟨U', hU'c⟩
  have hfin : FiniteDimensional ℚ L' := (InfiniteGalois.isOpen_iff_finite L').1 (hfix ▸ hU'o)
  let L : FiniteSubfield := ⟨L', hfin⟩
  have hmemU' : ∀ τ : K.1.fixingSubgroup, (τ : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ U' ↔ τ ∈ U := fun τ =>
    Subgroup.mem_map_iff_mem K.1.fixingSubgroup.subtype_injective
  have hKL : K ≤ L := by
    intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨τ, -, rfl⟩ := Subgroup.mem_map.1 hσ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 τ.2 x hx
  refine ⟨L, ⟨hKL⟩, fun x hx => ?_, ?_⟩
  · let KS' : IntermediateField ℚ ℚ̄ := (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ
    have hx' : x ∈ IntermediateField.fixedField KS'.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have hσK : σ ∈ K.1.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _
          ((maxUnramifiedOutside K.1 ℚ̄ S).algebraMap_mem (⟨y, hy⟩ : K.1))
      have hσN : (⟨σ, hσK⟩ : K.1.fixingSubgroup) ∈ gsKernel K S :=
        (mem_gsKernel_iff K S _).2 fun y hy =>
          (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ y hy
      have hσU' : σ ∈ U' := (hmemU' ⟨σ, hσK⟩).2 (hNU hσN)
      exact (IntermediateField.mem_fixedField_iff _ _).1 hx σ hσU'
    rw [InfiniteGalois.fixedField_fixingSubgroup KS'] at hx'
    exact hx'
  · ext τ
    rw [Subgroup.mem_subgroupOf, ← hmemU', ← hfix]

theorem isZero_cohomology_one_gsKernel :
    IsZero (cohomology (Rep.res (gsKernel K S).subtype (unitsLimitRep K)) 1) := by
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun a b => ?_⟩
  suffices h : ∀ y : cohomology (Rep.res (gsKernel K S).subtype (unitsLimitRep K)) 1, y = 0 by
    rw [h a, h b]
  intro y
  obtain ⟨U, hU, hNU, y', rfl⟩ :=
    exists_isOpen_cohomologyResLE_eq (unitsLimitRep K) (gsKernel K S) (isClosed_gsKernel K S) 1 y
  obtain ⟨L, hL, -, rfl⟩ := exists_finiteSubfield_of_isOpen K S U hU hNU
  have hz : Subsingleton (cohomology (Rep.res (L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).subtype
      (unitsLimitRep K)) 1) :=
    ModuleCat.subsingleton_of_isZero (isZero_cohomology_one_res_subgroupOf (K := K) (E := L))
  rw [Subsingleton.elim y' 0, map_zero]

section SubgroupOf

variable {K}

abbrev unitsSubgroupOfMap (L : FiniteSubfield) [Fact (K ≤ L)] (n : ℕ) :
    cohomology (Rep.res (L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).subtype (unitsLimitRep K)) n ⟶
      cohomology (unitsLimitRep L) n :=
  cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe
      (IntermediateField.fixingSubgroup_le (Fact.out : K ≤ L))).symm.toMonoidHom
    (continuous_subgroupOfEquivOfLe_symm _) (resSubgroupOfHom _ unitsRep) n

theorem unitsSubgroupOfMap_injective (L : FiniteSubfield) [Fact (K ≤ L)] (n : ℕ) :
    Function.Injective (unitsSubgroupOfMap (K := K) L n).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

theorem fixingSubgroup_subgroupOf_mono {L E : FiniteSubfield} (h : L ≤ E) :
    E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup ≤ L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup :=
  fun _ hσ => IntermediateField.fixingSubgroup_le h hσ

theorem cohomologyResLE_comp_unitsSubgroupOfMap {L E : FiniteSubfield} [Fact (K ≤ L)] [Fact (K ≤ E)]
    [Fact (L ≤ E)] (n : ℕ) :
    cohomologyResLE (unitsLimitRep K) (fixingSubgroup_subgroupOf_mono (K := K) (Fact.out : L ≤ E)) n ≫
      unitsSubgroupOfMap E n = unitsSubgroupOfMap L n ≫ unitsResField L E n := by
  rw [cohomologyResLE_eq, ← cohomologyMapAlong_comp, unitsResField, ← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_congr _ _ _ _ (by ext; rfl) (fun _ => rfl) n

end SubgroupOf

theorem exists_coprime_smul_cohomology_two_gsKernel {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (y : cohomology (Rep.res (gsKernel K S).subtype (unitsLimitRep K)) 2) :
    ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0 := by
  obtain ⟨U, hU, hNU, y', rfl⟩ :=
    exists_isOpen_cohomologyResLE_eq (unitsLimitRep K) (gsKernel K S) (isClosed_gsKernel K S) 2 y
  obtain ⟨L, hL, hLS, rfl⟩ := exists_finiteSubfield_of_isOpen K S U hU hNU
  set yL := (unitsSubgroupOfMap L 2).hom y'
  have htor := isTorsion_cohomology (unitsLimitRep L) (by norm_num : 1 ≤ 2) yL
  set M := addOrderOf yL
  have hM : M ≠ 0 := (IsOfFinAddOrder.addOrderOf_pos htor).ne'
  set a := M.factorization ℓ
  set M' := M / ℓ ^ a
  have hMN : ℓ ^ a * M' = M := Nat.ordProj_mul_ordCompl_eq_self M ℓ
  have hcop : Nat.Coprime M' ℓ := (Nat.coprime_ordCompl hℓ hM).symm
  have hz : ℓ ^ a • (M' • yL) = 0 := by
    rw [smul_smul, hMN]
    exact addOrderOf_nsmul_eq_zero yL
  obtain ⟨E, hE, b, hEb, hres⟩ := exists_unitsResField_eq_zero_of_pow_nsmul L hℓ (M' • yL) a hz
  have hES : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
    have hle : E.1 ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ := by
      rw [hEb]
      refine sup_le (fun x hx => hLS x hx) fun x hx => ?_
      exact mem_maxUnramifiedOutside_of_mem_rootsOfUnityField hℓ hS b x hx
    exact fun x hx => hle hx
  have : Fact (K ≤ E) := ⟨hL.out.trans hE.out⟩
  have hNE : gsKernel K S ≤ E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
      (mem_gsKernel_iff K S σ).1 hσ x (hES x hx)
  have hEL := fixingSubgroup_subgroupOf_mono (K := K) hE.out

  have hr : (cohomologyResLE (unitsLimitRep K) hEL 2).hom (M' • y') = 0 := by
    apply unitsSubgroupOfMap_injective E 2
    have e := congrArg (fun φ => ModuleCat.Hom.hom φ (M' • y'))
      (cohomologyResLE_comp_unitsSubgroupOfMap (K := K) (L := L) (E := E) 2)
    refine e.trans ?_
    change (unitsResField L E 2).hom ((unitsSubgroupOfMap L 2).hom (M' • y')) = _
    rw [map_nsmul, hres, map_zero]
  refine ⟨M', hcop, ?_⟩
  rw [← map_nsmul, ← cohomologyResLE_comp (unitsLimitRep K) hEL hNE 2, ConcreteCategory.comp_apply, hr,
    map_zero]

end

end GroundTheory.ProfCoh
