module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNoEig
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MemSmulLat
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.NormOneUnitIdealAlt
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.CardSmulMem
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.MemImgLatIff

section
@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate
open Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

variable {ι : Type} [Fintype ι] {V V₁ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V₁] [Module ℂ V₁]

theorem idx_coord (e : V ≃ₗ[ℂ] (ι → V₁)) (i₀ : ι) {M P : AddSubgroup V} {M₁ P₁ : AddSubgroup V₁}
    (hM : ∀ x, x ∈ M ↔ ∀ i, e x i ∈ M₁) (hP : ∀ x, x ∈ P ↔ ∀ i, e x i ∈ P₁) (h : relIdx M P ≠ 0) :
    relIdx M₁ P₁ ≠ 0 := by
  let f : V₁ →+ V := AddMonoidHom.mk' (fun x => e.symm (Pi.single i₀ x)) (fun x y => by
    rw [Pi.single_add, map_add (f := _)])
  have hcomap : ∀ (N : AddSubgroup V) (N₁ : AddSubgroup V₁), (∀ x, x ∈ N ↔ ∀ i, e x i ∈ N₁) →
      N₁ = N.comap f := by
    intro N N₁ hN
    ext x
    rw [AddSubgroup.mem_comap, hN]
    show x ∈ N₁ ↔ ∀ i, e (e.symm (Pi.single i₀ x)) i ∈ N₁
    simp only [LinearEquiv.apply_symm_apply]
    constructor
    · intro hx i
      by_cases hi : i = i₀
      · subst hi
        simpa using hx
      · rw [Pi.single_eq_of_ne hi]
        exact N₁.zero_mem
    · intro h
      simpa using h i₀
  unfold relIdx at *
  rw [hcomap M M₁ hM, hcomap P P₁ hP]
  exact AddSubgroup.relIndex_comap_ne_zero f h

variable {e : V ≃ₗ[ℂ] (ι → V₁)} {H : Sesq V} {H₁ : Sesq V₁} {α : V → ℂ} {α₁ : V₁ → ℂ}
  {Λ : AddSubgroup V} {Λ₁ : AddSubgroup V₁} {δ Ae : V ≃ₗ[ℂ] V} {δ₁ Ae₁ : V₁ ≃ₗ[ℂ] V₁}

theorem Copies.mem_img (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (x : V) :
    x ∈ imgLat (δ : V →ₗ[ℂ] V) Λ ↔ ∀ i, e x i ∈ imgLat (δ₁ : V₁ →ₗ[ℂ] V₁) Λ₁ := by
  have key : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (d : W ≃ₗ[ℂ] W) (L : AddSubgroup W) (z : W),
      z ∈ imgLat (d : W →ₗ[ℂ] W) L ↔ d.symm z ∈ L := by
    intro W _ _ d L z
    simp only [imgLat, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hz
      exact ⟨d.symm z, hz, by simp⟩
  rw [key, c.lat]
  apply forall_congr'
  intro i
  rw [key]
  have hmap := c.map (δ.symm x) i
  rw [LinearEquiv.apply_symm_apply] at hmap
  rw [hmap, LinearEquiv.symm_apply_apply]

theorem Copies.form_single (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (i₀ : ι) (x : V₁) (y : V) :
    H (e.symm (Pi.single i₀ x)) y = H₁ x (e y i₀) := by
  rw [c.form, LinearEquiv.apply_symm_apply, Finset.sum_eq_single i₀]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem Copies.single_mem (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (i₀ : ι) {x : V₁} (hx : x ∈ Λ₁) :
    e.symm (Pi.single i₀ x) ∈ Λ := by
  rw [c.lat]
  intro i
  rw [LinearEquiv.apply_symm_apply]
  by_cases hi : i = i₀
  · subst hi
    simpa using hx
  · rw [Pi.single_eq_of_ne hi]
    exact Λ₁.zero_mem

theorem Copies.char_single (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (h0 : α₁ 0 = 1) (i₀ : ι) {x : V₁} (hx : x ∈ Λ₁) :
    α (e.symm (Pi.single i₀ x)) = α₁ x := by
  rw [c.char _ (c.single_mem i₀ hx), LinearEquiv.apply_symm_apply, Finset.prod_eq_single i₀]
  · simp
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, h0]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem Copies.unitaryData₁ (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (i₀ : ι) (hU : UnitaryData H Λ α δ Ae)
    (hH₁ : IsHerm H₁) (hP₁ : IsPosDef H₁) (hI₁ : IsIsom H₁ H₁ (δ₁ : V₁ →ₗ[ℂ] V₁)) (hA₁ : ∀ x, Ae₁ x = x - δ₁.symm x)
    (h0 : α₁ 0 = 1) (hαδ : ∀ x, α₁ (δ₁ x) = α₁ x) : UnitaryData H₁ Λ₁ α₁ δ₁ Ae₁ := by
  have hs : ∀ x : V₁, e (e.symm (Pi.single i₀ x)) i₀ = x := fun x => by simp
  have hform : ∀ x y : V₁, H (e.symm (Pi.single i₀ x)) (e.symm (Pi.single i₀ y)) = H₁ x y := by
    intro x y
    rw [c.form_single, hs]
  have hadd : ∀ x y : V₁, e.symm (Pi.single i₀ (x + y)) = e.symm (Pi.single i₀ x) + e.symm (Pi.single i₀ y) := by
    intro x y
    rw [Pi.single_add, map_add (f := _)]
  have hδs : ∀ y : V₁, δ (e.symm (Pi.single i₀ y)) = e.symm (Pi.single i₀ (δ₁ y)) := by
    intro y
    apply e.injective
    funext i
    rw [c.map, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    by_cases hi : i = i₀
    · subst hi
      simp
    · simp [Pi.single_eq_of_ne hi]
  have himg_single : ∀ x : V₁, x ∈ imgLat (δ₁ : V₁ →ₗ[ℂ] V₁) Λ₁ →
      e.symm (Pi.single i₀ x) ∈ imgLat (δ : V →ₗ[ℂ] V) Λ := by
    intro x hx
    rw [c.mem_img]
    intro i
    rw [LinearEquiv.apply_symm_apply]
    by_cases hi : i = i₀
    · subst hi
      simpa using hx
    · rw [Pi.single_eq_of_ne hi]
      exact (imgLat _ Λ₁).zero_mem
  have hαimg : ∀ x : V₁, x ∈ imgLat (δ₁ : V₁ →ₗ[ℂ] V₁) Λ₁ → α (e.symm (Pi.single i₀ x)) = α₁ x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    show α (e.symm (Pi.single i₀ (δ₁ y))) = α₁ (δ₁ y)
    rw [← hδs, hU.inv _ (c.single_mem i₀ hy), c.char_single h0 i₀ hy, hαδ]
  refine ⟨hH₁, hP₁, ?_, ⟨?_, ?_⟩, hI₁, ⟨?_, ?_⟩, fun x _ => hαδ x, ?_, ?_, hA₁⟩
  · ext x
    constructor
    · intro hx
      have hv : e.symm (Pi.single i₀ x) ∈ Λ := by
        rw [← hU.selfDual]
        intro y hy
        obtain ⟨m, hm⟩ := hx (e y i₀) ((c.lat y).1 hy i₀)
        refine ⟨m, ?_⟩
        simp only [altE] at hm ⊢
        rw [c.form_single]
        exact hm
      have h1 := (c.lat _).1 hv i₀
      rwa [hs] at h1
    · intro hx y hy
      have h1 : e.symm (Pi.single i₀ x) ∈ dualLat H Λ := by
        rw [hU.selfDual]
        exact c.single_mem i₀ hx
      obtain ⟨m, hm⟩ := h1 _ (c.single_mem i₀ hy)
      refine ⟨m, ?_⟩
      simp only [altE] at hm ⊢
      rw [hform] at hm
      exact hm
  · intro x hx
    rw [← c.char_single h0 i₀ hx]
    exact hU.semi.1 _ (c.single_mem i₀ hx)
  · intro x hx y hy
    rw [← c.char_single h0 i₀ hx, ← c.char_single h0 i₀ hy, ← c.char_single h0 i₀ (Λ₁.add_mem hx hy), hadd,
      hU.semi.2 _ (c.single_mem i₀ hx) _ (c.single_mem i₀ hy)]
    simp only [altE, hform]
  · intro x hx
    rw [← hαimg x hx]
    exact hU.semi'.1 _ (himg_single x hx)
  · intro x hx y hy
    rw [← hαimg x hx, ← hαimg y hy, ← hαimg (x + y) ((imgLat _ Λ₁).add_mem hx hy), hadd,
      hU.semi'.2 _ (himg_single x hx) _ (himg_single y hy)]
    simp only [altE, hform]
  · exact idx_coord e i₀ c.mem_img c.lat hU.idx₁
  · exact idx_coord e i₀ c.lat c.mem_img hU.idx₂

theorem alpha_mult {H : Sesq V} {Λ : AddSubgroup V} {δ : V ≃ₗ[ℂ] V} {ℓ ℓ' σ : V →ₗ[ℂ] V} {n : ℕ}
    (hM : Multipliers H Λ δ ℓ ℓ' σ n) (c : ℝ) (α : V → ℂ) (hα : ∀ x, α x = (-1 : ℂ) ^ round (c * (H x x).re))
    (hq : ∀ x ∈ Λ, ∃ m : ℤ, c * (H x x).re = (m : ℝ)) {x : V} (hx : x ∈ Λ) : α (ℓ x) = α x := by
  obtain ⟨m1, hm1⟩ := hq x hx
  obtain ⟨m2, hm2⟩ := hq (σ x) (hM.sΛ x hx)
  obtain ⟨m3, hm3⟩ := hq (x + σ x) (Λ.add_mem hx (hM.sΛ x hx))
  have hexp : H (x + σ x) (x + σ x) = H x x + H x (σ x) + H x (σ x) + H (σ x) (σ x) := by
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [hM.sadj x x]
    ring
  have hk : c * (H x (σ x)).re * 2 = ((m3 - m1 - m2 : ℤ) : ℝ) := by
    rw [hexp] at hm3
    simp only [Complex.add_re] at hm3
    push_cast
    linarith
  have hl : H (ℓ x) (ℓ x) = -H x x + ((4 * n : ℕ) : ℂ) * H x (σ x) := by
    rw [hM.adj, hM.rel, map_add (f := _), map_neg, map_nsmul, nsmul_eq_mul]
  have hq' : c * (H (ℓ x) (ℓ x)).re = ((m1 + 2 * (-m1 + (n : ℤ) * (m3 - m1 - m2)) : ℤ) : ℝ) := by
    rw [hl]
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    push_cast
    push_cast at hk
    nlinarith [hm1, hk]
  rw [hα, hα, hq', hm1, round_intCast, round_intCast, zpow_add₀ (by norm_num), zpow_mul]
  simp

end Formalism.L2.PairingIndexBounds.Eq.J
end
end
end


@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

variable {D : Car}

def NegOneNorm (D : Car) : Prop :=
  ∀ m : ℕ, 0 < m → ∃ lam s : 𝓞 D.host.E, star (s : D.host.E) = (s : D.host.E) ∧
    star (lam : D.host.E) * (lam : D.host.E) = -1 + (m : D.host.E) * (s : D.host.E)

def mulO (N N' : ℕ) (r : D.host.E) : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => TaylorLogMetric.embT D τ r * z τ i j
  map_add' x y := by funext τ i j; exact mul_add _ _ _
  map_smul' c x := by funext τ i j; exact mul_left_comm _ _ _

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ)

theorem mul_integer_mem_base_lattice {N N' : ℕ} (r : 𝓞 D.host.E) {x : TaylorLogMetric.VC D N N'} (hx : x ∈ La0 B N N') :
    mulO N N' (r : D.host.E) x ∈ La0 B N N' := by
  have hle : La0 B N N' ≤ (La0 B N N').comap (mulO N N' (r : D.host.E)).toAddMonoidHom := by
    show TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') ≤
      (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')).comap (mulO N N' (r : D.host.E)).toAddMonoidHom
    rw [TaylorLogMetric.La, AddSubgroup.closure_le]
    rintro _ ⟨w, hw, A, hA, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    apply AddSubgroup.subset_closure
    refine ⟨w, hw, r • A, Submodule.smul_mem _ r hA, ?_⟩
    funext τ i j
    simp [mulO, TaylorLogMetric.embV, TaylorLogMetric.tor0, Algebra.smul_def, map_mul]
    ring
  exact hle hx

theorem star_int (r : 𝓞 D.host.E) : ∃ r' : 𝓞 D.host.E, (r' : D.host.E) = star (r : D.host.E) :=
  ⟨⟨star (r : D.host.E), by
    have h := (NumberField.RingOfIntegers.isIntegral_coe r).map (starRingEnd D.host.E).toIntAlgHom
    first
      | exact (mem_integralClosure_iff ℤ D.host.E).mpr h
      | exact h⟩, rfl⟩

theorem mulO_phi {N N' : ℕ} (r : D.host.E) (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (x : TaylorLogMetric.VC D N N') :
    mulO N N' r (phiU γ γ' x) = phiU γ γ' (mulO N N' r x) := by
  funext τ i j
  show TaylorLogMetric.embT D τ r * (gM (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (x τ) *
      (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j =
    (gM (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (fun i j => TaylorLogMetric.embT D τ r * x τ i j) *
      (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j
  have h1 : Matrix.of (fun i j => TaylorLogMetric.embT D τ r * x τ i j) = TaylorLogMetric.embT D τ r • Matrix.of (x τ) := by
    ext a b
    simp
  rw [h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

theorem mulO_adj (A : ℝ) {N N' : ℕ} (r : D.host.E) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (mulO N N' r x) y = Ker.formV A D.what₂.Tau N N' x (mulO N N' (star r) y) := by
  simp only [Formalism.L2.Ker.formV, LinearMap.mk₂'ₛₗ_apply, mulO, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, embT_star', Complex.star_def, Complex.conj_conj]
  ring

theorem gaussRow_of (hS : B.StdOK) (hL : B.LatAll) (hNeg : NegOneNorm D) : GaussRow B := by
  intro N γ Ae₁ hN hA₁ S hS₁
  have hfix₁ : ∀ y : TaylorLogMetric.VC D N 1, (phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1).symm y = y → y = 0 := by
    intro y hy
    apply Ae₁.injective
    rw [hA₁, hy, sub_self, map_zero]
  have hfix : ∀ x : TaylorLogMetric.VC D N 2, (phiU γ 1 : TaylorLogMetric.VC D N 2 ≃ₗ[ℂ] TaylorLogMetric.VC D N 2).symm x = x → x = 0 := by
    intro x hx
    apply (rowE D N 2).injective
    funext i
    rw [map_zero]
    refine hfix₁ _ ?_
    rw [← symm_coord (rowE D N 2) _ _ (map_row γ), hx]
  obtain ⟨Ae, hA⟩ := exists_cay (phiU γ 1 : TaylorLogMetric.VC D N 2 ≃ₗ[ℂ] TaylorLogMetric.VC D N 2) hfix
  have c : Copies (rowE D N 2) (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 2)
      (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ))
      (La0 B N 2) (La0 B N 1) (phiU γ 1) Ae (phiU γ 1) Ae₁ :=
    { form := form_row _ N 2
      char := al_row B hS N 2
      lat := lat_row B N 2
      map := map_row γ
      cay := fun x i => by
        rw [hA, hA₁, map_sub, Pi.sub_apply, symm_coord (rowE D N 2) _ _ (map_row γ)] }
  have hal0 : TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (0 : TaylorLogMetric.VC D N 1) = 1 := by
    unfold TaylorLogMetric.al TaylorLogMetric.Hf
    simp
  have hU₁ := c.unitaryData₁ 0 (unitaryData hL hN (by decide) γ 1 Ae hA) (_root_.Formalism.L2.Ker.Cd.formV_herm _ _ _ _)
    (formV_pos (area_pos' B) _ _ _) (phiL_isom _ _ _ _ _ _ _) hA₁ hal0 (al_phi _ _ _ _ _ _)
  have hcard : 0 < S.card := by
    obtain ⟨x, hx, -⟩ := hS₁.2.2 0 (AddSubgroup.zero_mem _)
    exact Finset.card_pos.mpr ⟨x, hx⟩
  obtain ⟨lam, s, hs, hrel⟩ := hNeg (4 * S.card) (by omega)
  obtain ⟨lam', hlam'⟩ := star_int lam
  have hM : Multipliers (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (La0 B N 1) (phiU γ 1)
      (mulO N 1 (lam : D.host.E)) (mulO N 1 (star (lam : D.host.E))) (mulO N 1 (s : D.host.E)) S.card :=
    { lΛ := fun x hx => mul_integer_mem_base_lattice B lam hx
      l'Λ := fun x hx => by rw [← hlam']; exact mul_integer_mem_base_lattice B lam' hx
      sΛ := fun x hx => mul_integer_mem_base_lattice B s hx
      lδ := mulO_phi _ γ 1
      l'δ := mulO_phi _ γ 1
      sδ := mulO_phi _ γ 1
      adj := mulO_adj _ _
      sadj := fun x y => by rw [mulO_adj, hs]
      rel := fun x => by
        funext τ i j
        show TaylorLogMetric.embT D τ (star (lam : D.host.E)) * (TaylorLogMetric.embT D τ (lam : D.host.E) * x τ i j) =
          -x τ i j + (4 * S.card) • (TaylorLogMetric.embT D τ (s : D.host.E) * x τ i j)
        rw [← mul_assoc, ← map_mul, hrel, map_add (f := _), map_neg, map_one, map_mul, map_natCast, nsmul_eq_mul]
        ring }
  exact gauss_sq hU₁ hM (fun x hx => card_smul_mem hS₁ hx)
    (fun x hx => alpha_mult hM (Real.sqrt D.host.d / 2) _ (fun _ => rfl) (B.qInt0 hS N 1) hx) hS₁

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
