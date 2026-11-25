module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

open Complex
open scoped BigOperators

namespace GlobalTheory

theorem entire_hom_eq_cexp_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (h : V → ℂ) (hd : Differentiable ℂ h) (h0 : h 0 = 1) (hadd : ∀ y z, h (y + z) = h y * h z)
    (z : V) : h z = cexp (fderiv ℂ h 0 z) := by
  set B : V →L[ℂ] ℂ := fderiv ℂ h 0
  have hder : ∀ w, HasFDerivAt h (h w • B) w := fun w => by
    have e : h = fun u => h w * h (u - w) := funext fun u => by rw [← hadd]; congr 1; abel
    have h1 : HasFDerivAt h B (w - w) := by rw [sub_self]; exact (hd 0).hasFDerivAt
    have h2 : HasFDerivAt (fun u => h (u - w)) B w := by
      simpa [Function.comp_def] using
        HasFDerivAt.comp (f := fun u => u - w) w h1 ((hasFDerivAt_id w).sub_const w)
    have h3 := h2.const_mul (h w)
    rwa [← e] at h3
  have hφ : ∀ w, HasFDerivAt (fun u => h u * cexp (-(B u))) (0 : V →L[ℂ] ℂ) w := fun w => by
    have e : h w • cexp (-B w) • -B + cexp (-B w) • h w • B = 0 := by
      rw [smul_comm (h w) (cexp (-B w)), smul_neg, smul_neg, neg_add_cancel]
    exact e ▸ (hder w).mul B.hasFDerivAt.neg.cexp
  have hc := is_const_of_fderiv_eq_zero (𝕜 := ℂ) (f := fun u => h u * cexp (-(B u)))
    (fun w => (hφ w).differentiableAt) (fun w => (hφ w).fderiv) z 0
  simp only [h0, map_zero, neg_zero, Complex.exp_zero, mul_one, Complex.exp_neg] at hc
  have := Complex.exp_ne_zero (B z)
  field_simp at hc; exact hc

theorem clm_eq_of_cexp_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (B C : V →L[ℂ] ℂ) (h : ∀ z, cexp (B z) = cexp (C z)) : B = C := by
  have h1 : HasFDerivAt (fun u => cexp (C u)) (cexp (B 0) • B) 0 := by
    simpa only [← h] using B.hasFDerivAt.cexp
  simpa using h1.unique C.hasFDerivAt.cexp

theorem prod_finset_fin_three {M : Type*} [CommMonoid M] (f : Finset (Fin 3) → M) :
    ∏ I, f I = f ∅ * (f {0} * (f {1} * (f {2} * (f {0, 1} * (f {0, 2} * (f {1, 2} *
      f {0, 1, 2})))))) := by
  have e : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [e]
  repeat rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_singleton]

theorem automorphyFactor_exp_linear_of_cube :
    (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∀ (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Set.univ)) ∧ (∀ i z, z ∈ W i → z ∈ Set.univ → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Set.univ → fr i z = c i j z * fr j z)) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) → ∃ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∀ l, a l ≠ 0) ∧ (∀ l m : Λ, a (l + m) = a l * a m * cexp (B l m)) ∧ ∀ (l : Λ) i z, z ∈ W i → fr i z = a l * cexp (B l z) * fr i (z + l)) := by
  intro g ι W c hWo hcov _ _ _ T _ hT0 _ Λ _ _ hWp hcp hTp fr κ ⟨hfd, hf0, hfc⟩ hcube
  choose σ hσ using hcov
  have hf0' : ∀ i z, z ∈ W i → fr i z ≠ 0 := fun i z hz => hf0 i z hz (Set.mem_univ _)
  have hfa : ∀ i z, z ∈ W i → DifferentiableAt ℂ (fr i) z := fun i z hz =>
    (Set.inter_univ _ ▸ hfd i).differentiableAt ((hWo i).mem_nhds hz)
  let α : Λ → (Fin g → ℂ) → ℂ := fun l z => fr (σ z) z / fr (σ z) (z + l)
  have hα : ∀ (l : Λ) i z, z ∈ W i → α l z = fr i z / fr i (z + l) := fun l i z hz => by
    have e1 := hfc (σ z) i z (hσ z) hz (Set.mem_univ _)
    have e2 := hfc (σ z) i (z + l) ((hWp _ z l l.2).2 (hσ z)) ((hWp i z l l.2).2 hz) (Set.mem_univ _)
    rw [hcp _ _ z l l.2] at e2
    have hc0 : c (σ z) i z ≠ 0 := fun h => hf0' _ _ (hσ z) (by simpa [h] using e1)
    show fr (σ z) z / fr (σ z) (z + l) = _
    rw [e1, e2, mul_div_mul_left _ _ hc0]
  have hα0 : ∀ (l : Λ) z, α l z ≠ 0 := fun l z =>
    div_ne_zero (hf0' _ _ (hσ z)) (hf0' _ _ ((hWp _ z l l.2).2 (hσ z)))
  have hαd : ∀ l : Λ, Differentiable ℂ (α l) := fun l z => by
    have hzl' : z + l ∈ W (σ z) := (hWp _ z l l.2).2 (hσ z)
    have h1 : DifferentiableAt ℂ (fun w => fr (σ z) (w + l)) z :=
      (hfa _ _ hzl').comp z (differentiableAt_id.add_const _)
    have h2 : DifferentiableAt ℂ (fun w => fr (σ z) w / fr (σ z) (w + l)) z := by
      simp only [div_eq_mul_inv]
      exact (hfa _ _ (hσ z)).mul (h1.inv (hf0' _ _ hzl'))
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [(hWo (σ z)).mem_nhds (hσ z)] with w hw using hα l _ w hw
  have hαc : ∀ (l m : Λ) z, α (l + m) z = α l z * α m (z + l) := fun l m z => by
    have hzl' : z + l ∈ W (σ z) := (hWp _ z l l.2).2 (hσ z)
    rw [hα (l + m) _ z (hσ z), hα l _ z (hσ z), hα m _ (z + l) hzl', Submodule.coe_add, ← add_assoc]
    have := hf0' _ _ hzl'
    field_simp
  have hcubeα : ∀ (l : Λ) y z, α l (y + z) * α l 0 = α l y * α l z := fun l y z => by
    let x : Fin 3 → Fin g → ℂ := ![0, y, z]
    let L : Fin 3 → Fin g → ℂ := ![l, 0, 0]
    have hL : ∀ a, L a ∈ Λ := fun a => by fin_cases a; exacts [l.2, Λ.zero_mem, Λ.zero_mem]
    let j : Finset (Fin 3) → ι := fun I => σ (∑ a ∈ I, x a)
    have hj : ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I) := fun I => hσ _
    have hs : ∀ I : Finset (Fin 3), ∑ a ∈ I, (x + L) a = ∑ a ∈ I, x a + ∑ a ∈ I, L a := fun I =>
      Finset.sum_add_distrib
    have hj' : ∀ I : Finset (Fin 3), ∑ a ∈ I, (x + L) a ∈ W (j I) := fun I =>
      hs I ▸ (hWp _ _ _ (Λ.sum_mem fun a _ => hL a)).2 (hj I)
    have e1 := hcube j x hj
    have e2 := hcube j (x + L) hj'
    have hκ : κ ≠ 0 := fun h => hT0 j x hj (by simpa [h] using e1)
    rw [hTp j x L hL, e1] at e2
    have e3 := mul_left_cancel₀ hκ e2
    let F : Finset (Fin 3) → ℂ := fun I =>
      α ⟨∑ a ∈ I, L a, Λ.sum_mem fun a _ => hL a⟩ (∑ a ∈ I, x a)
    have e4 : ∏ I : Finset (Fin 3), F I ^ ((-1 : ℤ) ^ (3 - I.card)) = 1 := by
      change ∏ I : Finset (Fin 3), (fr (j I) (∑ a ∈ I, x a) /
        fr (j I) (∑ a ∈ I, x a + ∑ a ∈ I, L a)) ^ ((-1 : ℤ) ^ (3 - I.card)) = 1
      simp only [div_zpow, Finset.prod_div_distrib]
      simp only [hs] at e3
      rw [← e3]
      exact div_self (Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (hf0' _ _ (hj I)))
    have hz : ∀ (m : Λ) w, (m : Fin g → ℂ) = 0 → α m w = 1 := fun m w hm => by
      show fr (σ w) w / fr (σ w) (w + m) = 1
      rw [hm, add_zero]; exact div_self (hf0' _ _ (hσ w))
    have hl : ∀ (m : Λ) w w', (m : Fin g → ℂ) = l → w = w' → α m w = α l w' := fun m w w' hm hw => by
      rw [Subtype.ext hm, hw]
    have hF : ∀ I : Finset (Fin 3), F I = if (0 : Fin 3) ∈ I then α l (∑ a ∈ I, x a) else 1 := fun I => by
      have hsumL : ∑ a ∈ I, L a = if (0 : Fin 3) ∈ I then (l : Fin g → ℂ) else 0 := by
        split_ifs with h0
        · rw [Finset.sum_eq_single 0 (fun a _ ha => by fin_cases a <;> simp_all [L]) (fun h => absurd h0 h)]
          simp [L]
        · exact Finset.sum_eq_zero fun a ha => by
            have : a ≠ 0 := fun h => h0 (h ▸ ha)
            fin_cases a <;> simp_all [L]
      split_ifs with h0
      · exact hl _ _ _ (by simpa [h0] using hsumL) rfl
      · exact hz _ _ (by simpa [h0] using hsumL)
    rw [prod_finset_fin_three] at e4
    simp only [hF, x, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      Fin.isValue, Fin.reduceEq, or_self, or_false, ↓reduceIte,
      Finset.sum_singleton, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1),
      Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2),
      Finset.sum_insert (by decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3))),
      Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2),
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, zero_add] at e4
    norm_num at e4
    have := hα0 l y; have := hα0 l z
    field_simp at e4; linear_combination e4
  let B₀ : Λ → ((Fin g → ℂ) →L[ℂ] ℂ) := fun l => fderiv ℂ (fun z => α l z / α l 0) 0
  have hexp : ∀ (l : Λ) z, α l z = α l 0 * cexp (B₀ l z) := fun l z => by
    have h0 := hα0 l 0
    have h1 := entire_hom_eq_cexp_fderiv (fun z => α l z / α l 0)
      (by simp only [div_eq_mul_inv]; exact (hαd l).mul_const _)
      (div_self h0) (fun y z => by have := hcubeα l y z; field_simp; linear_combination this) z
    show _ = _ * cexp (fderiv ℂ (fun z => α l z / α l 0) 0 z)
    rw [← h1]; field_simp
  have ha : ∀ l m : Λ, α (l + m) 0 = α l 0 * α m 0 * cexp (B₀ l m) := fun l m => by
    rw [add_comm, hαc, zero_add, hexp l m]; ring
  have hBadd : ∀ l m : Λ, B₀ (l + m) = B₀ l + B₀ m := fun l m =>
    clm_eq_of_cexp_eq _ _ fun z => by
      have e := hαc m l z
      rw [add_comm m l, hexp (l + m), hexp m, hexp l, ha, map_add, Complex.exp_add] at e
      rw [add_apply, Complex.exp_add]
      have h1 : α l 0 * α m 0 * cexp (B₀ l m) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (hα0 _ _) (hα0 _ _)) (Complex.exp_ne_zero _)
      exact mul_left_cancel₀ h1 (by linear_combination e)
  refine ⟨fun l => α l 0, AddMonoidHom.mk' (fun l => (B₀ l).toLinearMap) fun l m => by rw [hBadd]; rfl,
    fun l => hα0 l 0, ha, fun l i z hz => ?_⟩
  have e := hexp l z
  rwa [hα l i z hz, div_eq_iff (hf0' _ _ ((hWp _ z l l.2).2 hz))] at e

end GlobalTheory
