module

public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Mathlib.Algebra.Module.StablyFree.Basic
import Formalism.SharpRestriction.LevelLetterCocycles.StrictSesLetter

@[expose] public section

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

section Funct

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} (f : V →ₗ[LL] V')

theorem crisMap_φVB (z : V ⊗[Qp] B) :
    crisMap B f (φVB PD (LL := LL) (V := V) z) = φVB PD (LL := LL) (V := V') (crisMap B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [crisMap, φVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem crisMap_φVB_pow (s : ℕ) (z : V ⊗[Qp] B) :
    crisMap B f (((φVB PD (LL := LL) (V := V)) ^ s) z) =
      ((φVB PD (LL := LL) (V := V')) ^ s) (crisMap B f z) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', pow_succ']
    exact (crisMap_φVB PD f _).trans (congrArg (φVB PD (LL := LL) (V := V')) ih)

theorem act_φVB (g : G) (z : V ⊗[Qp] B) :
    actVB PD ρ g (φVB PD (LL := LL) (V := V) z) = φVB PD (LL := LL) (V := V) (actVB PD ρ g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [actVB, φVB, PD.φ_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem φVB_Dcris {z : V ⊗[Qp] B} (hz : z ∈ Dcris PD ρ) : φVB PD (LL := LL) (V := V) z ∈ Dcris PD ρ := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz ⊢
  intro g
  rw [act_φVB, hz g]

theorem φVB_pow_Dcris (s : ℕ) {z : V ⊗[Qp] B} (hz : z ∈ Dcris PD ρ) :
    ((φVB PD (LL := LL) (V := V)) ^ s) z ∈ Dcris PD ρ := by
  induction s with
  | zero => simpa using hz
  | succ s ih =>
    rw [pow_succ']
    exact φVB_Dcris PD ih

theorem mulVB_Dcris (c : K₀) {z : V ⊗[Qp] B} (hz : z ∈ Dcris PD ρ) :
    mulVB (LL := LL) (V := V) (B := B) c z ∈ Dcris PD ρ := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz ⊢
  intro g
  rw [Formalism.MainNotions.LiftingTheory.lext_act_mul, hz g]

theorem coord_ιV {ι₀ : Type} (b : Module.Basis ι₀ Qp V) (i : ι₀) (z : V ⊗[Qp] B) :
    Formalism.MainNotions.LiftingTheory.lone_coord b i BdR (ιV PD (LL := LL) (V := V) z) = PD.ι (Formalism.MainNotions.LiftingTheory.lone_coord b i B z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v c =>
    simp [Formalism.MainNotions.LiftingTheory.lone_coord, ιV, Algebra.smul_def, IsScalarTower.algebraMap_apply Qp K₀ B,
      IsScalarTower.algebraMap_apply Qp K₀ BdR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem filCris_triv [FiniteDimensional Qp V] (hρ : ∀ g x, ρ g x = x) (u : ℤ) (hu : 1 ≤ u) {z : V ⊗[Qp] B}
    (hz : z ∈ FilCris PD ρ u) : z = 0 := by
  rw [FilCris, Submodule.mem_inf] at hz
  obtain ⟨hD, hF⟩ := hz
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hD
  rw [Submodule.mem_comap] at hF
  have b : Module.Basis (Fin (Module.finrank Qp V)) Qp V := Module.finBasis Qp V
  have key : ∀ i, Formalism.MainNotions.LiftingTheory.lone_coord b i B z = 0 := by
    intro i
    have hinv : ∀ g, PD.actB g (Formalism.MainNotions.LiftingTheory.lone_coord b i B z) =
        Formalism.MainNotions.LiftingTheory.lone_coord b i B z := by
      intro g
      rw [← Formalism.MainNotions.LiftingTheory.lone_coord_actB PD ρ hρ b i g z, hD g]
    obtain ⟨k, hk⟩ := PD.invB _ hinv
    have hι : PD.ι (Formalism.MainNotions.LiftingTheory.lone_coord b i B z) ∈ PD.Fil u := by
      rw [← coord_ιV PD (LL := LL) b i z]
      exact Formalism.MainNotions.LiftingTheory.lone_coord_FilV PD b i u _ hF
    rw [← hk] at hι ⊢
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K₀ K BdR] at hι
    have h0 := Formalism.MainNotions.LiftingTheory.lone_K_inter PD _ u hu hι
    apply PD.ι_inj
    rw [PD.ι.commutes, IsScalarTower.algebraMap_apply K₀ K BdR, h0, map_zero, map_zero]
  rw [Formalism.MainNotions.LiftingTheory.lone_decomp b z]
  simp [key]

end Funct

section SES

theorem ses_exact (hK : Function.Bijective (algebraMap K₀ K)) (h9 : DcrisExactStrict PD LL)
    (T₂ Y T₀ : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L T₀.L) (hses : IsSESLat (Qp := Qp) ι π)
    (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (h0 : IsCrys PD T₀.ρ) :
    (∀ y ∈ Dcris PD T₂.ρ, crisMap B ι.f y = 0 → y = 0) ∧
      (∀ x ∈ Dcris PD Y.ρ, crisMap B π.f x = 0 → ∃ y ∈ Dcris PD T₂.ρ, crisMap B ι.f y = x) := by
  have hrk : LinearMap.range ι.f = LinearMap.ker π.f := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    exact (hses.2.2.2.1 x).symm
  obtain ⟨e1, e2, -⟩ := h9 hK T₂.V Y.V T₀.V T₂.ρ Y.ρ T₀.ρ ι.f π.f T₂.cont Y.cont T₀.cont ι.equiv π.equiv
    hses.1 hses.2.1 hrk h2 hY h0
  exact ⟨e1, e2⟩

variable {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

private theorem crisMap_rT_lemma_9 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (C : Type) [CommRing C] [Algebra Qp C]
    (f : V →ₗ[LL] V') (x : V ⊗[Qp] C) :
    crisMap C f x = LinearMap.rTensor C (f.restrictScalars Qp) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [crisMap]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem crisMap_inj_lemma_10 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (C : Type) [CommRing C] [Algebra Qp C]
    (f : V →ₗ[LL] V') (hf : Function.Injective f) : Function.Injective (crisMap (Qp := Qp) C f) := by
  intro x y h
  rw [crisMap_rT_lemma_9 C f x, crisMap_rT_lemma_9 C f y] at h
  have hi : Function.Injective (LinearMap.rTensor C (f.restrictScalars Qp)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hf
  exact hi h

private theorem crisMap_exact_lemma_11 {V₀ V V' : Type} [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀] [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (C : Type) [CommRing C] [Algebra Qp C]
    (f : V₀ →ₗ[LL] V) (g : V →ₗ[LL] V') (hfg : ∀ x, g x = 0 ↔ ∃ y, f y = x) (hg : Function.Surjective g)
    (x : V ⊗[Qp] C) (hx : crisMap C g x = 0) : ∃ y, crisMap C f y = x := by
  rw [crisMap_rT_lemma_9] at hx
  have hex : Function.Exact (f.restrictScalars Qp) (g.restrictScalars Qp) := by
    intro x
    rw [Set.mem_range]
    exact hfg x
  obtain ⟨y, hy⟩ := (rTensor_exact C hex hg x).1 hx
  exact ⟨y, by rw [crisMap_rT_lemma_9]; exact hy⟩

private theorem crisMap_act_lemma_12 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] {ρ : Representation LL G V}
    {ρ' : Representation LL G V'} (f : V →ₗ[LL] V') (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : G) (z : V ⊗[Qp] B) :
    crisMap B f (actVB PD ρ g z) = actVB PD ρ' g (crisMap B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [crisMap, actVB, hf]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem algmap_lT_lemma_15 {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U] {C D : Type} [AddCommGroup C] [Module Qp C]
    [AddCommGroup D] [Module Qp D] (g : C →ₗ[Qp] D) (w : U ⊗[Qp] C) :
    AlgebraTensorModule.map (LinearMap.id : U →ₗ[LL] U) g w = LinearMap.lTensor U g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem filV_iff_lemma_13 {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U] (a : ℤ) (y : U ⊗[Qp] BdR) :
    y ∈ FilV PD (LL := LL) (V := U) a ↔ LinearMap.lTensor U ((PD.Fil a).restrictScalars Qp).mkQ y = 0 := by
  have hex := lTensor_exact U (LinearMap.exact_subtype_mkQ ((PD.Fil a).restrictScalars Qp))
    (Submodule.mkQ_surjective ((PD.Fil a).restrictScalars Qp))
  rw [hex y, FilV, LinearMap.mem_range, Set.mem_range]
  simp only [algmap_lT_lemma_15]

private theorem comm_q_lemma_21 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') (a : ℤ) (x : V ⊗[Qp] BdR) :
    LinearMap.lTensor V' ((PD.Fil a).restrictScalars Qp).mkQ (LinearMap.rTensor BdR (f.restrictScalars Qp) x) =
      LinearMap.rTensor (BdR ⧸ (PD.Fil a).restrictScalars Qp) (f.restrictScalars Qp)
        (LinearMap.lTensor V ((PD.Fil a).restrictScalars Qp).mkQ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem filV_strict_lemma_16 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') (hf : Function.Injective f)
    (a : ℤ) (x : V ⊗[Qp] BdR) (hx : crisMap BdR f x ∈ FilV PD (LL := LL) (V := V') a) :
    x ∈ FilV PD (LL := LL) (V := V) a := by
  rw [filV_iff_lemma_13 PD] at hx
  rw [filV_iff_lemma_13 PD]
  rw [crisMap_rT_lemma_9] at hx
  have hc := comm_q_lemma_21 PD f a x
  rw [hc] at hx
  have hi : Function.Injective (LinearMap.rTensor (BdR ⧸ (PD.Fil a).restrictScalars Qp) (f.restrictScalars Qp)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hf
  exact hi (hx.trans (map_zero _).symm)

private theorem filV_fwd_lemma_20 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') (a : ℤ) (x : V ⊗[Qp] BdR)
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) : crisMap BdR f x ∈ FilV PD (LL := LL) (V := V') a := by
  rw [filV_iff_lemma_13 PD] at hx
  rw [filV_iff_lemma_13 PD, crisMap_rT_lemma_9]
  have hc := comm_q_lemma_21 PD f a x
  rw [hc, hx, map_zero]

private theorem crisMap_iV_lemma_17 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') (z : V ⊗[Qp] B) :
    crisMap BdR f (ιV PD (LL := LL) (V := V) z) = ιV PD (LL := LL) (V := V') (crisMap B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [crisMap, ιV]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem fil_pull [FiniteDimensional Qp LL] (W : LocWach PD LL O v n)
    (hK : Function.Bijective (algebraMap K₀ K)) (h9 : DcrisExactStrict PD LL)
    (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L) (hses : IsSESLat (Qp := Qp) ι π)
    (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (u : ℤ) (hu : 1 ≤ u) (τ₀ : K₀ →ₐ[Qp] LL)
    {ν : Y.V ⊗[Qp] B} (hν : ν ∈ FilCris PD Y.ρ u ⊓ DcrisL PD Y.ρ τ₀) :
    ∃ μ ∈ FilCris PD T₂.ρ u ⊓ DcrisL PD T₂.ρ τ₀, crisMap B ι.f μ = ν := by
  haveI : FiniteDimensional Qp W.one.V := Module.Finite.trans LL W.one.V
  obtain ⟨hνF, hνL⟩ := Submodule.mem_inf.1 hν
  rw [FilCris, Submodule.mem_inf] at hνF
  obtain ⟨hνD, hνV⟩ := hνF
  have hπD : crisMap B π.f ν ∈ Dcris PD W.one.ρ := by
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hνD ⊢
    intro g
    rw [← crisMap_act_lemma_12 PD π.f π.equiv, hνD g]
  have hπV : crisMap B π.f ν ∈
      (FilV PD (LL := LL) (V := W.one.V) u).comap (ιV PD (LL := LL) (V := W.one.V)) := by
    rw [Submodule.mem_comap, ← crisMap_iV_lemma_17 PD π.f]
    rw [Submodule.mem_comap] at hνV
    exact filV_fwd_lemma_20 PD π.f u _ hνV
  have hπ0 : crisMap B π.f ν = 0 :=
    filCris_triv PD W.94 u hu (by rw [FilCris, Submodule.mem_inf]; exact ⟨hπD, hπV⟩)
  obtain ⟨μ, hμ⟩ := crisMap_exact_lemma_11 B ι.f π.f hses.2.2.2.1 hses.2.1 ν hπ0
  have hinj := crisMap_inj_lemma_10 (Qp := Qp) B ι.f hses.1
  have hμD : μ ∈ Dcris PD T₂.ρ := by
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hνD ⊢
    intro g
    apply hinj
    rw [crisMap_act_lemma_12 PD ι.f ι.equiv, hμ, hνD g]
  have hμF : μ ∈ FilCris PD T₂.ρ u := by
    rw [FilCris, Submodule.mem_inf, Submodule.mem_comap]
    refine ⟨hμD, filV_strict_lemma_16 PD ι.f hses.1 u _ ?_⟩
    rw [crisMap_iV_lemma_17 PD ι.f, hμ]
    rw [Submodule.mem_comap] at hνV
    exact hνV
  have hμL : μ ∈ DcrisL PD T₂.ρ τ₀ := by
    rw [DcrisL, Submodule.mem_inf] at hνL ⊢
    refine ⟨hμD, ?_⟩
    have hνL2 := hνL.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hνL2 ⊢
    intro c
    apply hinj
    rw [_root_.Formalism.MainNotions.UnusedSlot80.Strict.crisMap_mulVB ι.f, map_smul, hμ, hνL2 c]
  exact ⟨μ, Submodule.mem_inf.2 ⟨hμF, hμL⟩, hμ⟩

end SES

end Formalism.MainNotions.UnusedSlot80.SplitP
