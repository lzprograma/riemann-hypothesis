module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIndepBridge
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.AboveLRes

section Res

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω]
  [Algebra K L] [IsScalarTower K L Ω]

def decRes (A : ValuationSubring Ω) : ↥(Dec (F := L) A) →* ↥(Dec (F := K) A) where
  toFun g := ⟨AlgEquiv.restrictScalars K (g : G L Ω), by
    have hg := mem_Dec.mp g.2
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    conv_rhs => rw [← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end Res

end GlobalTheory.AboveLRes

noncomputable section

namespace GlobalTheory.AboveLRes

section Bridge

variable {l : ℕ} [Fact l.Prime] {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem exists_bridge (Bw : LocBridge l K Ω (Dec (F := K) A) O) (hj : Induces Bw) (S : FinExt l) :
    ∃ (LL' : FinExt l) (Bw' : LocBridge l L Ω (Dec (F := L) A) ↥(OL LL')), Bw'.j = Bw.j ∧ S.1 ≤ Bw'.LL.1 ∧ Bw.Kw.1 ≤ Bw'.Kw.1 := by
  let jL := Bw.j.comp (algebraMap L Ω)
  let K' : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range jL),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range jL⟩
  have := K'.2
  let N : FinExt l := ⟨IntermediateField.normalClosure ℚ_[l] ↥K'.1 (PadicAlgCl l),
    normalClosure.is_finiteDimensional ℚ_[l] ↥K'.1 (PadicAlgCl l)⟩
  let LL' : FinExt l := supExt S N
  have hN : N.1 ≤ LL'.1 := le_sup_right
  have hS : S.1 ≤ LL'.1 := le_sup_left
  obtain ⟨e, he, he', hec⟩ :=
    GlobalTheory.PlaceBridge.exists_mulEquiv (E := L) (j := Bw.j) hj K' rfl
  let B : LocBridge l L Ω (Dec (F := L) A) ↥(OL LL') := {
    Kw := K'
    j := Bw.j
    j_E := fun x => IntermediateField.subset_adjoin ℚ_[l] (Set.range jL) (Set.mem_range_self x)
    j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure jL
    e := e
    e_cont := he
    e_symm_cont := he'
    e_comm := hec
    LL := LL'
    LL_split := fun τ x => hN (τ.fieldRange_le_normalClosure ⟨x, rfl⟩)
    eO := RingEquiv.refl ↥(OL LL')
    eO_alg := fun _ => rfl
    eO_cont := continuous_id
    eO_symm_cont := continuous_id }
  refine ⟨LL', B, rfl, hS, ?_⟩
  show Bw.Kw.1 ≤ K'.1
  rw [BridgeInd.kw_eq_adjoin Bw, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  refine IntermediateField.subset_adjoin _ _ ⟨algebraMap K L x, ?_⟩
  show Bw.j (algebraMap L Ω (algebraMap K L x)) = Bw.j (algebraMap K Ω x)
  rw [← IsScalarTower.algebraMap_apply]

variable {O' : Type} [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
  (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O')
  (hjj : Bw'.j = Bw.j) (hle : Bw.Kw.1 ≤ Bw'.Kw.1)
include hjj hle

theorem decRes_e_symm (g' : ↥(GK Bw'.Kw)) :
    decRes (K := K) A (Bw'.e.symm g') = Bw.e.symm ⟨g', GK_le hle g'.2⟩ := by
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply Bw.j.injective
  have h1 := Bw'.e_comm (Bw'.e.symm g') x
  have h2 := Bw.e_comm (Bw.e.symm ⟨g', GK_le hle g'.2⟩) x
  rw [MulEquiv.apply_symm_apply] at h1 h2
  rw [hjj] at h1
  exact h1.symm.trans h2

theorem repE_decRes (T : FinExt l) {m : ℕ} (t : ↥(Dec (F := K) A) →* GL (Fin m) ↥T.1) :
    Bw'.repE T (t.comp (decRes A)) = GlobalTheory.Pst.resTo (Bw.repE T t) hle := by
  ext g' v i
  simp only [LocBridge.repE, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, GlobalTheory.Pst.resTo]
  rw [decRes_e_symm Bw Bw' hjj hle]
  rfl

variable {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v')

theorem weilToGK_eq (σ : Weil h) (σ' : Weil h') (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) :
    (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l) := by
  have e1 := decRes_e_symm Bw Bw' hjj hle (weilToGK Bw' h' σ')
  have e2 : decRes (K := K) A (Bw'.e.symm (weilToGK Bw' h' σ')) = Subgroup.inclusion (Weil_le_Dec h) σ := by
    rw [weilToGK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact Subtype.ext (AlgEquiv.ext fun z => (hσ z).symm)
  rw [e2, MulEquiv.eq_symm_apply] at e1
  exact (congrArg Subtype.val e1).symm

end Bridge

end GlobalTheory.AboveLRes
