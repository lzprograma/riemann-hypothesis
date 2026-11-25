module

public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreDefs
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasGl
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCyc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.HighestWeightExists

@[expose] public section

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem exists_factor {M T P : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T]
    [AddCommGroup P] [Module ℂ P] (φ : M →ₗ[ℂ] T) (hφ : Function.Surjective φ) (g : M →ₗ[ℂ] P)
    (h : LinearMap.ker φ ≤ LinearMap.ker g) : ∃ π : T →ₗ[ℂ] P, ∀ m, π (φ m) = g m := by
  refine ⟨((LinearMap.ker φ).liftQ g h) ∘ₗ (φ.quotKerEquivOfSurjective hφ).symm.toLinearMap, fun m => ?_⟩
  have e : (φ.quotKerEquivOfSurjective hφ).symm (φ m) = Submodule.Quotient.mk m := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]

theorem quot_of_local {J M T T' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T]
    [AddCommGroup T'] [Module ℂ T'] [Nontrivial T] [Nontrivial T']
    (actM : J → Module.End ℂ M) (act : J → Module.End ℂ T) (act' : J → Module.End ℂ T')
    (R : Submodule ℂ M) (hR : R ≠ ⊤)
    (hN : ∀ N : Submodule ℂ M, (∀ W, ∀ x ∈ N, actM W x ∈ N) → N ≠ ⊤ → N ≤ R)
    (φ : M →ₗ[ℂ] T) (φ' : M →ₗ[ℂ] T') (hφ : Function.Surjective φ) (hφ' : Function.Surjective φ')
    (e : ∀ W x, φ (actM W x) = act W (φ x)) (e' : ∀ W x, φ' (actM W x) = act' W (φ' x)) :
    ∃ (Pi : Type) (_ : AddCommGroup Pi) (_ : Module ℂ Pi) (actP : J → Module.End ℂ Pi)
      (π : T →ₗ[ℂ] Pi) (π' : T' →ₗ[ℂ] Pi), Function.Surjective π ∧ Function.Surjective π' ∧
      (∀ W x, π (act W x) = actP W (π x)) ∧ (∀ W x, π' (act' W x) = actP W (π' x)) ∧ Nontrivial Pi ∧
      ∀ N : Submodule ℂ Pi, (∀ W, ∀ x ∈ N, actP W x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  classical
  set S : Set (Submodule ℂ M) := {N | (∀ W, ∀ x ∈ N, actM W x ∈ N) ∧ N ≠ ⊤} with hS
  set Rm : Submodule ℂ M := sSup S with hRm
  have hRmR : Rm ≤ R := sSup_le fun N' hN' => hN N' hN'.1 hN'.2
  have hRmtop : Rm ≠ ⊤ := fun h => hR (top_le_iff.mp (h ▸ hRmR))
  have hRst : ∀ W, ∀ x ∈ Rm, actM W x ∈ Rm := by
    intro W
    have hle : Rm ≤ Rm.comap (actM W) :=
      sSup_le fun N hN x hx => (le_sSup hN : N ≤ Rm) (hN.1 W x hx)
    exact fun x hx => hle hx
  have hker : ∀ {T₀ : Type} [AddCommGroup T₀] [Module ℂ T₀] [Nontrivial T₀]
      (act₀ : J → Module.End ℂ T₀) (ψ : M →ₗ[ℂ] T₀), Function.Surjective ψ →
      (∀ W x, ψ (actM W x) = act₀ W (ψ x)) → LinearMap.ker ψ ≤ Rm := by
    intro T₀ _ _ _ act₀ ψ hψ eψ
    refine le_sSup ⟨fun W x hx => ?_, fun htop => ?_⟩
    · rw [LinearMap.mem_ker] at hx ⊢
      rw [eψ, hx, map_zero]
    · obtain ⟨y, hy⟩ := exists_ne (0 : T₀)
      obtain ⟨m, rfl⟩ := hψ y
      exact hy (LinearMap.mem_ker.mp (htop ▸ Submodule.mem_top))
  let actP : J → Module.End ℂ (M ⧸ Rm) := fun W => Rm.mapQ Rm (actM W) (fun x hx => hRst W x hx)
  obtain ⟨π, hπ⟩ := exists_factor φ hφ Rm.mkQ (by simpa using hker act φ hφ e)
  obtain ⟨π', hπ'⟩ := exists_factor φ' hφ' Rm.mkQ (by simpa using hker act' φ' hφ' e')
  refine ⟨M ⧸ Rm, inferInstance, inferInstance, actP, π, π', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨m, rfl⟩ := Rm.mkQ_surjective y
    exact ⟨φ m, hπ m⟩
  · intro y
    obtain ⟨m, rfl⟩ := Rm.mkQ_surjective y
    exact ⟨φ' m, hπ' m⟩
  · intro W x
    obtain ⟨m, rfl⟩ := hφ x
    rw [← e, hπ, hπ]
    rfl
  · intro W x
    obtain ⟨m, rfl⟩ := hφ' x
    rw [← e', hπ', hπ']
    rfl
  · exact Submodule.Quotient.nontrivial_iff.mpr hRmtop
  · intro N hN
    by_cases hc : N.comap Rm.mkQ = ⊤
    · right
      rw [eq_top_iff]
      intro y _
      obtain ⟨m, rfl⟩ := Rm.mkQ_surjective y
      have : m ∈ N.comap Rm.mkQ := hc ▸ Submodule.mem_top
      exact this
    · left
      have hst : ∀ W, ∀ x ∈ N.comap Rm.mkQ, actM W x ∈ N.comap Rm.mkQ := by
        intro W x hx
        exact hN W _ hx
      have hle : N.comap Rm.mkQ ≤ Rm := le_sSup ⟨hst, hc⟩
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨m, rfl⟩ := Rm.mkQ_surjective y
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hle hy

section Gen

variable {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem le_genG' (act : Mat r s →ₗ[ℂ] Module.End ℂ M) (S : Submodule ℂ M) : S ≤ genG act S :=
  le_sInf fun _ hN => hN.1

theorem genG_le' {act : Mat r s →ₗ[ℂ] Module.End ℂ M} {S N : Submodule ℂ M} (h1 : S ≤ N)
    (h2 : ∀ W, ∀ x ∈ N, act W x ∈ N) : genG act S ≤ N :=
  sInf_le ⟨h1, h2⟩

theorem genG_stable' (act : Mat r s →ₗ[ℂ] Module.End ℂ M) (S : Submodule ℂ M) :
    ∀ W, ∀ x ∈ genG act S, act W x ∈ genG act S := by
  intro W x hx
  simp only [genG, Submodule.mem_sInf, Set.mem_setOf_eq] at hx ⊢
  intro N hN
  exact hN.2 W x (hx N hN)

theorem sameBlock_symm' {a b : Ix r s} (h : sameBlock a b) : sameBlock b a := by
  exact (CasGl.sb_iff _ _).2 ((CasGl.sb_iff _ _).1 h).symm

theorem casK_mem {ρ : Ix r s → Ix r s → Module.End ℂ M} {N : Submodule ℂ M} (h : KSt ρ N) {x : M}
    (hx : x ∈ N) : casK ρ x ∈ N := by
  simp only [casK, LinearMap.sum_apply]
  refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
  split_ifs with hab
  · exact h a b hab _ (h b a (sameBlock_symm' hab) _ hx)
  · exact N.zero_mem

theorem casK_intertw {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Ix r s → Ix r s → Module.End ℂ V}
    {ρ' : Ix r s → Ix r s → Module.End ℂ M} (ι : V →ₗ[ℂ] M)
    (h : ∀ a b, sameBlock a b → ∀ v, ι (ρ a b v) = ρ' a b (ι v)) (v : V) :
    ι (casK ρ v) = casK ρ' (ι v) := by

  simp only [casK, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with hab
  · simp only [Module.End.mul_apply]
    rw [h a b hab, h b a (sameBlock_symm' hab)]
  · simp

theorem local_of (act : Mat r s →ₗ[ℂ] Module.End ℂ M) (hL : IsLie act) (La : Ix r s → ℚ)
    {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
    (ρ : Ix r s → Ix r s → Module.End ℂ A) (ι : A →ₗ[ℂ] M) (f : A)
    (hadj : AdjK ρ) (hgl : GlK ρ) (hw : HwK ρ La f)
    (hι : ∀ a b, sameBlock a b → ∀ u, ι (ρ a b u) = act (Eab a b) (ι u))
    (hs : StarK act (LinearMap.range ι) ((casW La : ℚ) : ℝ)) (h0 : ι f ≠ 0) :
    ∃ R : Submodule ℂ M, ι f ∉ R ∧ ∀ N : Submodule ℂ M, N ≤ genG act (Submodule.span ℂ {ι f}) →
      (∀ W, ∀ x ∈ N, act W x ∈ N) → N ≠ genG act (Submodule.span ℂ {ι f}) → N ≤ R := by
  classical
  have hsym : ∀ {a b : Ix r s}, sameBlock a b → sameBlock b a := fun h => sameBlock_symm' h
  let B := cycK ρ f
  have hfB : f ∈ B := self_mem_cycK ρ f
  have hBK : KSt ρ B := kSt_cycK ρ f
  have hirr (W : Submodule ℂ A) (hWB : W ≤ B) (hWK : KSt ρ W) (hfW : f ∉ W) : W = ⊥ := by
    rcases cyc_irred hadj hgl hw W hWB hWK with hbot | hcyc
    · exact hbot
    · rw [hcyc] at hfW
      exact (hfW hfB).elim
  let c0 : ℝ := ((casW La : ℚ) : ℝ)
  have hBE : ∀ u ∈ B, casK ρ u = ((c0 : ℝ) : ℂ) • u := by
    simpa [c0] using cas_cyc hgl hw
  let ρ0 : Ix r s → Ix r s → Module.End ℂ B := fun a b =>
    if h : sameBlock a b then (ρ a b).restrict (fun x hx => hBK a b h x hx) else 0
  have hρ0 : ∀ a b, sameBlock a b → ∀ v : B, ((ρ0 a b v : B) : A) = ρ a b v := by
    intro a b h v
    simp only [ρ0, dite_eq_left h, LinearMap.restrict_apply]
  have hcas0 : casK ρ0 = ((c0 : ℝ) : ℂ) • 1 := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have := casK_intertw (ρ := ρ0) (ρ' := ρ) B.subtype (fun a b h v => hρ0 a b h v) v
    simp only [Submodule.coe_subtype] at this
    rw [this, hBE v v.2]
    simp
  have hadj0 : AdjK ρ0 := by
    intro a b h u v
    rw [Submodule.coe_inner, Submodule.coe_inner, hρ0 a b h, hρ0 b a (hsym h)]
    exact hadj a b h u v
  let ι0 : B →ₗ[ℂ] M := ι ∘ₗ B.subtype
  have hι0 : ∀ a b, sameBlock a b → ∀ v : B, ι0 (ρ0 a b v) = act (Eab a b) (ι0 v) := by
    intro a b h v
    simp only [ι0, LinearMap.comp_apply, Submodule.coe_subtype]
    rw [hρ0 a b h]
    exact hι a b h v
  have hs0 : StarK act (LinearMap.range ι0) c0 := by
    intro t ht x hx hC
    refine hs t ht x ?_ hC
    refine Submodule.span_mono ?_ hx
    rintro y ⟨a, b, hab, v, ⟨w, rfl⟩, rfl⟩
    exact ⟨a, b, hab, ι w, ⟨w, rfl⟩, rfl⟩
  obtain ⟨hi, hii⟩ := cas_bound_gl act hL ρ0 hadj0 c0 hcas0 ι0 hι0 hs0
  set C := casK (units act) with hC
  set L := LinearMap.range ι0 with hLdef
  have hfL : ι f ∈ L := ⟨⟨f, hfB⟩, rfl⟩
  have hGL : genG act (Submodule.span ℂ {ι f}) ≤ genG act L := by
    refine genG_le' ?_ (genG_stable' act L)
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact le_genG' act L hfL
  have hCst : ∀ N : Submodule ℂ M, (∀ W, ∀ x ∈ N, act W x ∈ N) → ∀ x ∈ N, C x ∈ N :=
    fun N hN x hx => casK_mem (fun a b _ y hy => hN _ y hy) hx
  have hCL : ∀ v : B, C (ι0 v) = ((c0 : ℝ) : ℂ) • ι0 v := by
    intro v
    rw [hC, ← casK_intertw (ρ := ρ0) (ρ' := units act) ι0 (fun a b h v => hι0 a b h v) v, hcas0]
    simp
  have hind : ∀ k : ℕ, ∀ y ∈ genG act L, ((C - ((c0 : ℝ) : ℂ) • 1) ^ k) y = 0 → y ∈ L := by
    intro k
    induction k with
    | zero =>
      intro y _ h
      rw [pow_zero, Module.End.one_apply] at h
      rw [h]
      exact L.zero_mem
    | succ k ih =>
      intro y hy h
      have hz : (C - ((c0 : ℝ) : ℂ) • 1) y ∈ genG act L := by
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
        exact Submodule.sub_mem _ (hCst _ (genG_stable' act L) y hy) (Submodule.smul_mem _ _ hy)
      have := ih _ hz (by rw [← Module.End.mul_apply, ← pow_succ]; exact h)
      refine hi y hy ?_
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
      exact this
  let R : Submodule ℂ M :=
    { carrier := {x | ∃ q : Polynomial ℂ, q.eval ((c0 : ℝ) : ℂ) ≠ 0 ∧ Polynomial.aeval C q x = 0}
      add_mem' := by
        rintro x y ⟨p, hp, hpx⟩ ⟨q, hq, hqy⟩
        refine ⟨p * q, by rw [Polynomial.eval_mul]; exact mul_ne_zero hp hq, ?_⟩
        have h1 : Polynomial.aeval C (p * q) x = 0 := by
          rw [mul_comm, map_mul, Module.End.mul_apply, hpx, map_zero]
        have h2 : Polynomial.aeval C (p * q) y = 0 := by
          rw [map_mul, Module.End.mul_apply, hqy, map_zero]
        rw [map_add (f := _), h1, h2, add_zero]
      zero_mem' := ⟨1, by simp, by simp⟩
      smul_mem' := by
        rintro a x ⟨q, hq, hqx⟩
        exact ⟨q, hq, by rw [map_smul, hqx, smul_zero]⟩ }
  have hfR : ι f ∉ R := by
    rintro ⟨q, hq, hqf⟩
    have hev : Module.End.HasEigenvector C ((c0 : ℝ) : ℂ) (ι f) :=
      ⟨Module.End.mem_eigenspace_iff.mpr (hCL ⟨f, hfB⟩), h0⟩
    rw [Module.End.aeval_apply_of_hasEigenvector hev] at hqf
    exact hq ((smul_eq_zero.mp hqf).resolve_right h0)
  refine ⟨R, hfR, fun N hNG hNst hNne => ?_⟩
  intro x hx
  obtain ⟨F, hFfd, hxF, hFK⟩ := hii x (hGL (hNG hx))
  have hF'C : ∀ y ∈ F ⊓ N, C y ∈ F ⊓ N := fun y hy => ⟨casK_mem hFK hy.1, hCst N hNst y hy.2⟩
  haveI : FiniteDimensional ℂ (F ⊓ N : Submodule ℂ M) := Submodule.finiteDimensional_of_le inf_le_left
  set Cf : Module.End ℂ (F ⊓ N : Submodule ℂ M) := C.restrict hF'C with hCf
  have hres : ∀ (P : Polynomial ℂ) (v : (F ⊓ N : Submodule ℂ M)),
      ((Polynomial.aeval Cf P v : (F ⊓ N : Submodule ℂ M)) : M) = Polynomial.aeval C P (v : M) := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
      intro v
      simp only [map_add (f := _), LinearMap.add_apply, Submodule.coe_add, hp, hq]
    | monomial n a =>
      intro v
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
        Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
        Submodule.coe_smul, hCf, Module.End.pow_restrict, LinearMap.restrict_apply]
  have hp0 : minpoly ℂ Cf ≠ 0 := minpoly.ne_zero (IsIntegral.of_finite ℂ Cf)
  obtain ⟨q, hpq, hndvd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly ℂ Cf) hp0 ((c0 : ℝ) : ℂ)
  have hq : q.eval ((c0 : ℝ) : ℂ) ≠ 0 := fun h => hndvd (Polynomial.dvd_iff_isRoot.mpr h)
  set k := (minpoly ℂ Cf).rootMultiplicity ((c0 : ℝ) : ℂ)
  let xF : (F ⊓ N : Submodule ℂ M) := ⟨x, hxF, hx⟩
  set y := Polynomial.aeval C q x with hy
  have hyN : y ∈ N := by
    rw [hy, show x = (xF : M) from rfl, ← hres q xF]
    exact (Polynomial.aeval Cf q xF).2.2
  have hyk : ((C - ((c0 : ℝ) : ℂ) • 1) ^ k) y = 0 := by
    have h2 : Polynomial.aeval C (minpoly ℂ Cf) x = 0 := by
      rw [show x = (xF : M) from rfl, ← hres _ xF, minpoly.aeval]
      rfl
    rw [hpq, map_mul, Module.End.mul_apply] at h2
    simpa [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one] using h2
  have hyL : y ∈ L := hind k y (hGL (hNG hyN)) hyk
  have hy0 : y = 0 := by
    by_contra hyne
    obtain ⟨v, hv⟩ := hyL
    have hWK : KSt ρ (N.comap ι ⊓ B) := by
      intro a b hab u hu
      refine ⟨?_, hBK a b hab u hu.2⟩
      show ι (ρ a b u) ∈ N
      rw [hι a b hab]
      exact hNst _ _ hu.1
    have hvW : (v : A) ∈ N.comap ι ⊓ B := ⟨by
      show ι v ∈ N
      have e0 : ι0 v = ι v := rfl
      rw [← e0, hv]
      exact hyN, v.2⟩
    have hfW : f ∈ N.comap ι ⊓ B := by
      by_contra hfW
      have hbot := hirr _ inf_le_right hWK hfW
      rw [hbot, Submodule.mem_bot] at hvW
      apply hyne
      rw [← hv]
      show ι (v : A) = 0
      rw [hvW, map_zero]
    have hGN : genG act (Submodule.span ℂ {ι f}) ≤ N := by
      refine genG_le' ?_ hNst
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hfW.1
    exact hNne (le_antisymm hNG hGN)
  exact ⟨q, hq, hy0⟩

end Gen

def mainProdAct {r s : ℕ} {T T' : Type} [AddCommGroup T] [Module ℂ T] [AddCommGroup T'] [Module ℂ T']
    (act : Mat r s →ₗ[ℂ] Module.End ℂ T) (act' : Mat r s →ₗ[ℂ] Module.End ℂ T') :
    Mat r s →ₗ[ℂ] Module.End ℂ (T × T') where
  toFun W := (act W).prodMap (act' W)
  map_add' W W' := by
    refine LinearMap.ext fun x => ?_
    simp
  map_smul' a W := by
    refine LinearMap.ext fun x => ?_
    simp

theorem ne_zero_of_gen {r s : ℕ} {T : Type} [AddCommGroup T] [Module ℂ T] [Nontrivial T]
    (act : Mat r s →ₗ[ℂ] Module.End ℂ T) (v : T) (h : genG act (Submodule.span ℂ {v}) = ⊤) : v ≠ 0 := by
  rintro rfl
  have : genG act (Submodule.span ℂ {(0 : T)}) ≤ ⊥ := by
    refine genG_le' (by simp) fun W x hx => ?_
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]
  rw [h] at this
  exact top_ne_bot (le_bot_iff.1 this)

theorem common_quot {r s : ℕ} (La : Ix r s → ℚ) (T T' : Type) [AddCommGroup T] [Module ℂ T]
    [AddCommGroup T'] [Module ℂ T'] (act : Mat r s →ₗ[ℂ] Module.End ℂ T) (act' : Mat r s →ₗ[ℂ] Module.End ℂ T')
    (h : Side La T act) (h' : Side La T' act') :
    ∃ (Pi : Type) (_ : AddCommGroup Pi) (_ : Module ℂ Pi) (actP : Mat r s → Module.End ℂ Pi)
      (π : T →ₗ[ℂ] Pi) (π' : T' →ₗ[ℂ] Pi), Function.Surjective π ∧ Function.Surjective π' ∧
      (∀ W x, π (act W x) = actP W (π x)) ∧ (∀ W x, π' (act' W x) = actP W (π' x)) ∧ Nontrivial Pi ∧
      ∀ N : Submodule ℂ Pi, (∀ W, ∀ x ∈ N, actP W x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  classical
  obtain ⟨hL, hT, A, iA1, iA2, iA3, ρ, ι, f, hadj, hgl, hw, hι, hgen, hs⟩ := h
  obtain ⟨hL', hT', A', iB1, iB2, iB3, ρ', ι', f', hadj', hgl', hw', hι', hgen', hs'⟩ := h'
  set P := mainProdAct act act' with hP
  let eA := WithLp.linearEquiv 2 ℂ (A × A')
  let ρ₂ : Ix r s → Ix r s → Module.End ℂ (WithLp 2 (A × A')) := fun a b =>
    eA.symm.toLinearMap ∘ₗ ((ρ a b).prodMap (ρ' a b)) ∘ₗ eA.toLinearMap
  let ι₂ : WithLp 2 (A × A') →ₗ[ℂ] T × T' := (ι.prodMap ι') ∘ₗ eA.toLinearMap
  let f₂ : WithLp 2 (A × A') := WithLp.toLp 2 (f, f')
  have hρ₂ : ∀ a b u, (ρ₂ a b u).ofLp = (ρ a b u.ofLp.1, ρ' a b u.ofLp.2) := fun a b u => rfl
  have hι₂ : ∀ u, ι₂ u = (ι u.ofLp.1, ι' u.ofLp.2) := fun u => rfl
  have hPapp : ∀ W x, P W x = (act W x.1, act' W x.2) := fun W x => rfl
  have hLP : IsLie P := by
    intro X Y
    refine LinearMap.ext fun x => Prod.ext ?_ ?_
    · simpa [hPapp] using LinearMap.congr_fun (hL X Y) x.1
    · simpa [hPapp] using LinearMap.congr_fun (hL' X Y) x.2
  have key : ∀ X Y : Module.End ℂ (WithLp 2 (A × A')), (∀ u, (X u).ofLp = (Y u).ofLp) → X = Y := by
    intro X Y hXY
    refine LinearMap.ext fun u => ?_
    have := hXY u
    cases hx : X u
    cases hy : Y u
    rw [hx, hy] at this
    simp_all
  have hadj₂ : AdjK ρ₂ := by
    intro a b hab u v
    rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply, hρ₂, hρ₂]
    simp only
    rw [hadj a b hab, hadj' a b hab]
  have hgl₂ : GlK ρ₂ := by
    intro a b c d h1 h2
    refine key _ _ fun u => Prod.ext ?_ ?_
    · have := LinearMap.congr_fun (hgl a b c d h1 h2) u.ofLp.1
      split_ifs at this ⊢ <;> simpa [hρ₂] using this
    · have := LinearMap.congr_fun (hgl' a b c d h1 h2) u.ofLp.2
      split_ifs at this ⊢ <;> simpa [hρ₂] using this
  have hv : ∀ x y : WithLp 2 (A × A'), x.ofLp = y.ofLp → x = y := by
    intro x y hxy
    cases x
    cases y
    simp_all
  have hw₂ : HwK ρ₂ La f₂ := by
    constructor
    · intro a
      apply hv
      rw [hρ₂]
      simp [f₂, hw.1 a, hw'.1 a]
    · intro a b hab
      apply hv
      rw [hρ₂]
      simp [f₂, hw.2 a b hab, hw'.2 a b hab]
  have hιP : ∀ a b, sameBlock a b → ∀ u, ι₂ (ρ₂ a b u) = P (Eab a b) (ι₂ u) := by
    intro a b hab u
    rw [hι₂, hι₂, hPapp, hρ₂, hι a b hab, hι' a b hab]
  have hcas : ∀ x : T × T', casK (units P) x = (casK (units act) x.1, casK (units act') x.2) := by
    intro x
    simp only [casK, units, LinearMap.sum_apply]
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_sum, Prod.snd_sum] <;>
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_ <;> split_ifs <;> rfl
  have hs₂ : StarK P (LinearMap.range ι₂) ((casW La : ℚ) : ℝ) := by
    intro t ht x hx hC
    have m1 : Submodule.map (LinearMap.fst ℂ T T') (Submodule.span ℂ {y : T × T' | ∃ a b, ¬ sameBlock a b ∧ ∃ v ∈ LinearMap.range ι₂, y = P (Eab a b) v}) ≤ Submodule.span ℂ {y : T | ∃ a b, ¬ sameBlock a b ∧ ∃ v ∈ LinearMap.range ι, y = act (Eab a b) v} := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨y, ⟨a, b, hab, v, ⟨u, rfl⟩, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨a, b, hab, ι u.ofLp.1, ⟨_, rfl⟩, rfl⟩
    have m2 : Submodule.map (LinearMap.snd ℂ T T') (Submodule.span ℂ {y : T × T' | ∃ a b, ¬ sameBlock a b ∧ ∃ v ∈ LinearMap.range ι₂, y = P (Eab a b) v}) ≤ Submodule.span ℂ {y : T' | ∃ a b, ¬ sameBlock a b ∧ ∃ v ∈ LinearMap.range ι', y = act' (Eab a b) v} := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨y, ⟨a, b, hab, v, ⟨u, rfl⟩, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨a, b, hab, ι' u.ofLp.2, ⟨_, rfl⟩, rfl⟩
    rw [hcas] at hC
    refine Prod.ext ?_ ?_
    · exact hs t ht x.1 (m1 (Submodule.mem_map_of_mem hx)) (by simpa using congrArg Prod.fst hC)
    · exact hs' t ht x.2 (m2 (Submodule.mem_map_of_mem hx)) (by simpa using congrArg Prod.snd hC)
  have h0 : ι₂ f₂ ≠ 0 := by
    intro h0
    exact ne_zero_of_gen act (ι f) hgen (by simpa [hι₂, f₂] using congrArg Prod.fst h0)
  obtain ⟨R, hfR, hR⟩ := local_of P hLP La ρ₂ ι₂ f₂ hadj₂ hgl₂ hw₂ hιP hs₂ h0
  haveI := hT
  haveI := hT'
  set G := genG P (Submodule.span ℂ {ι₂ f₂}) with hG
  have hfG : ι₂ f₂ ∈ G := le_genG' P _ (Submodule.mem_span_singleton_self _)
  have hGst := genG_stable' P (Submodule.span ℂ {ι₂ f₂})
  let actM : Mat r s → Module.End ℂ G := fun W => (P W).restrict (fun x hx => hGst W x hx)
  let φ : G →ₗ[ℂ] T := LinearMap.fst ℂ T T' ∘ₗ G.subtype
  let φ' : G →ₗ[ℂ] T' := LinearMap.snd ℂ T T' ∘ₗ G.subtype
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hgen]
    refine genG_le' ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨⟨_, hfG⟩, by simp [φ, hι₂, f₂]⟩
    · rintro W _ ⟨g, rfl⟩
      exact ⟨actM W g, rfl⟩
  have hφ' : Function.Surjective φ' := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hgen']
    refine genG_le' ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨⟨_, hfG⟩, by simp [φ', hι₂, f₂]⟩
    · rintro W _ ⟨g, rfl⟩
      exact ⟨actM W g, rfl⟩
  refine quot_of_local actM (fun W => act W) (fun W => act' W) (R.comap G.subtype) ?_ ?_ φ φ' hφ hφ'
    (fun W x => rfl) (fun W x => rfl)
  · intro htop
    exact hfR (show (⟨_, hfG⟩ : G) ∈ R.comap G.subtype from htop ▸ Submodule.mem_top)
  · intro N hNst hNtop
    have hle : N.map G.subtype ≤ G := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    have hst : ∀ W, ∀ x ∈ N.map G.subtype, P W x ∈ N.map G.subtype := by
      rintro W _ ⟨y, hy, rfl⟩
      exact ⟨actM W y, hNst W y hy, rfl⟩
    have hne : N.map G.subtype ≠ G := by
      intro hEq
      apply hNtop
      rw [eq_top_iff]
      intro y _
      have : (y : T × T') ∈ N.map G.subtype := by
        rw [hEq]
        exact y.2
      obtain ⟨z, hz, hzy⟩ := this
      rw [Subtype.ext hzy] at hz
      exact hz
    intro y hy
    exact hR _ hle hst hne ⟨y, hy, rfl⟩

end PositivityTheory.KReal

end
