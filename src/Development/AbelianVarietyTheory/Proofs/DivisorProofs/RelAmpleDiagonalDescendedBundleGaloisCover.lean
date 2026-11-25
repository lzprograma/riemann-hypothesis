module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

@[expose] public section

noncomputable section

namespace GlobalTheory.FiniteAmpleFP

open Polynomial CategoryTheory GlobalTheory.FiniteAmple

section Algebra

variable {A B : Type} [CommRing A] [CommRing B]

theorem exists_finFree_away_fp {φ : A →+* B} (hf : φ.Finite) (hfl : φ.Flat) (hfp : φ.FinitePresentation)
    (p : PrimeSpectrum A) :
    ∃ r ∉ p.asIdeal, ∀ {A' B' : Type} [CommRing A'] [CommRing B'] {α : A →+* A'} {β : B →+* B'} {φ' : A' →+* B'},
      IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
      IsUnit (α r) → FinFree φ' := by
  algebraize [φ]
  have : Module.FinitePresentation A B := Module.FinitePresentation.of_finite_of_finitePresentation A B
  have : Module.Free (Localization p.asIdeal.primeCompl) (LocalizedModule p.asIdeal.primeCompl B) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl B) (Localization p.asIdeal.primeCompl)
  refine ⟨r, hr, ?_⟩
  intro A' B' _ _ α β φ' H hu
  algebraize [α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  refine ⟨Module.Finite.equiv hb.equiv, ?_⟩
  letI : Algebra (Localization.Away r) A' := (IsLocalization.Away.lift r (g := α) hu).toAlgebra
  have : IsScalarTower A (Localization.Away r) A' :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq r hu x).symm
  have h₁ : Module.Free (Localization.Away r) (TensorProduct A (Localization.Away r) B) :=
    Module.Free.of_equiv (IsLocalizedModule.isBaseChange (.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (.powers r) B)).equiv.symm
  exact Module.Free.of_equiv
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away r) A' A' B).trans hb.equiv)

end Algebra

section Geometry

open AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LBGerm

variable {X Y : Scheme.{0}} (f : Y ⟶ X)

theorem exists_finFree_app_fp [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U ∧ FinFree (f.app V).hom := by
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset hx
  have hfl : (f.app V).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact f.flat_appLE hV (hV.preimage f) _
  have hfp : (f.app V).hom.FinitePresentation := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE @LocallyOfFinitePresentation f ‹_› ⟨V, hV⟩ ⟨_, hV.preimage f⟩ _
  obtain ⟨r, hr, H⟩ := exists_finFree_away_fp (f.finite_app V hV) hfl hfp (hV.primeIdealOf ⟨x, hxV⟩)
  refine ⟨X.basicOpen r, hV.basicOpen r, ?_, (X.basicOpen_le r).trans hle,
    H (isPushout_app f hV (hV.basicOpen r) (X.basicOpen_le r)) (X.toRingedSpace.isUnit_res_basicOpen r)⟩
  have e := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have h₁ : hV.primeIdealOf ⟨x, hxV⟩ ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen r := by
    rw [hV.fromSpec_preimage_basicOpen]
    exact hr
  exact (congrArg (· ∈ X.basicOpen r) e).mp h₁

end Geometry

end GlobalTheory.FiniteAmpleFP

namespace GlobalTheory.HeckeAmple

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory

theorem relAmple_of_pull_hom {S : Scheme.{0}} {A B : Over S} [GrpObj B] (hB : IsAbelianScheme B) (ψ : A ⟶ B)
    [IsFinite ψ.left] [Flat ψ.left] [Surjective ψ.left] [LocallyOfFinitePresentation ψ.left]
    {M : LB B.left} (hM : M.IsLB) (hA : Out.RelAmple A (M.pull ψ.left)) : Out.RelAmple B M := by
  refine relAmple_of_isAbelianScheme B hB hM fun U hU => ?_
  have h₁ := isAmpleLB_of_relAmple A (LB.isLB_pull hM _) hA U hU
  have pre : A.hom ⁻¹ᵁ U = ψ.left ⁻¹ᵁ (B.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, Over.w ψ]
  rw [pre] at h₁
  have h₃ : IsAmpleLB ((M.pull (B.hom ⁻¹ᵁ U).ι).pull (ψ.left ∣_ (B.hom ⁻¹ᵁ U))) :=
    (isAmpleLB_congr (LB.isLB_pull (LB.isLB_pull hM _) _) (LB.isLB_pull (LB.isLB_pull hM _) _)
      (FiniteAmple.lbIso_pull_pull _ hM (morphismRestrict_ι ψ.left _).symm)).1 h₁
  have : Surjective (ψ.left ∣_ B.hom ⁻¹ᵁ U) := MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict ψ.left _).flip inferInstance
  have : IsFinite (ψ.left ∣_ B.hom ⁻¹ᵁ U) := MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_morphismRestrict ψ.left _).flip inferInstance
  have : Flat (ψ.left ∣_ B.hom ⁻¹ᵁ U) := MorphismProperty.of_isPullback (P := @Flat) (isPullback_morphismRestrict ψ.left _).flip inferInstance
  have : LocallyOfFinitePresentation (ψ.left ∣_ B.hom ⁻¹ᵁ U) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_morphismRestrict ψ.left _).flip inferInstance
  exact FiniteAmple.isAmpleLB_of_pull_of _ (fun hx => FiniteAmpleFP.exists_finFree_app_fp _ hx) (LB.isLB_pull hM _) h₃

theorem relAmple_diag_of_galois : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ), 1 ≤ m → ∀ (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) := by
  intro p _ D R _ b M S s o A' _ _ ψ G hA' _ hG m hm P' hP' hw
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have : Flat ψ.left := inferInstance
  have : LocallyOfFinitePresentation ψ.left := inferInstance
  have hP := o.isLB
  have e : ψ.left ≫ (lift (𝟙 A') (𝟙 A')).left = (lift (𝟙 o.A) (𝟙 o.A)).left ≫ Hecke.sq2 ψ := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    ext <;> simp
  have hL' : (P'.pull (lift (𝟙 A') (𝟙 A')).left).IsLB := LB.isLB_pull hP' _
  refine relAmple_of_pull_hom hA' ψ hL' ?_
  have hLd : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := LB.isLB_pull hP _
  have H₁ := FiniteAmple.lbIso_pull_pull (lift (𝟙 A') (𝟙 A')).left hP' e
  have H₂ : LBIso ((P'.pull (Hecke.sq2 ψ)).pull (lift (𝟙 o.A) (𝟙 o.A)).left)
      ((Hecke.lbPow o.P m).pull (lift (𝟙 o.A) (𝟙 o.A)).left) :=
    LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) hw.symm
  have H₃ : LBIso ((Hecke.lbPow o.P m).pull (lift (𝟙 o.A) (𝟙 o.A)).left)
      (LB.LinComb o.P (K := Fin m) (fun _ => (lift (𝟙 o.A) (𝟙 o.A)).left) (fun _ => 1)) :=
    lbIso_of_chartPull (chartPullOut o.P (fun _ => 𝟙 _) (fun _ => 1) (lift (𝟙 o.A) (𝟙 o.A)).left
      (fun _ => (lift (𝟙 o.A) (𝟙 o.A)).left) fun _ => (Category.comp_id _).symm) (LB.isLB_linComb hP _ _)
  have H₄ := (lbIso_lbPow_finPow hP (lift (𝟙 o.A) (𝟙 o.A)).left m).symm
  have hLB₁ := LB.isLB_pull hL' ψ.left
  have hLB₂ : ((P'.pull (Hecke.sq2 ψ)).pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := LB.isLB_pull (LB.isLB_pull hP' _) _
  have hLB₃ : ((Hecke.lbPow o.P m).pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB :=
    LB.isLB_pull (LB.isLB_linComb hP _ _) _
  have hLB₄ := LB.isLB_linComb hP (K := Fin m) (fun _ => (lift (𝟙 o.A) (𝟙 o.A)).left) (fun _ => 1)
  have hLB₅ := isLB_lbPow hLd m
  have H : LBIso ((P'.pull (lift (𝟙 A') (𝟙 A')).left).pull ψ.left) (lbPow (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) m) :=
    LBIso.trans hLB₁ hLB₄ hLB₅ (LBIso.trans hLB₁ hLB₃ hLB₄ (LBIso.trans hLB₁ hLB₂ hLB₃ H₁ H₂) H₃) H₄
  refine relAmple_of_isAbelianScheme o.A o.ab hLB₁ fun U hU => ?_
  have h₁ := isAmpleLB_of_relAmple o.A hLd o.ample U hU
  have h₂ := (isAmpleLB_pow_iff (LB.isLB_pull hLd (o.A.hom ⁻¹ᵁ U).ι) hm).2 h₁
  have h₃ := h₂.of_lbIso (LB.isLB_pull hLB₅ _) (lbIso_lbPow_pull hLd (o.A.hom ⁻¹ᵁ U).ι m).symm
  exact h₃.of_lbIso (LB.isLB_pull hLB₁ _) (LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) H)

end GlobalTheory.HeckeAmple
