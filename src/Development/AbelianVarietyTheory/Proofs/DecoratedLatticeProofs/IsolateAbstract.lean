module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Algebra.Operations
import Mathlib.GroupTheory.QuotientGroup.ModEq
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace GlobalTheory

theorem isolate_abstract : ∀ (X : Type) [AddCommGroup X] (Γ G : AddSubgroup X) (V : Type) [AddCommGroup V] [Module ℂ V] (T : X → V →ₗ[ℂ] V) (W : Set V) (β : X → X → ℂ) (a : X → ℂ) (χ : X → X → ℂ), Γ ≤ G → (∀ v, T 0 v = v) → (∀ x y v, T x (T y v) = β x y • T (x + y) v) → (∀ x y, β x y ≠ 0) → (∀ γ ∈ Γ, a γ ≠ 0 ∧ ∀ v ∈ W, T γ v = a γ • v) → (∀ γ ∈ Γ, ∀ x v, T γ (T x v) = χ x γ • T x (T γ v)) → (∀ x, ∀ γ ∈ Γ, ∀ γ' ∈ Γ, χ (x + γ') γ = χ x γ) → (∀ x ∈ G, ∀ y ∈ G, x - y ∉ Γ → ∃ γ ∈ Γ, χ x γ ≠ χ y γ) → ∀ (J : Finset X) (c : X → ℂ), (∀ x ∈ J, x ∈ G) → (∀ v ∈ W, ∑ x ∈ J, c x • T x v = 0) ∨ ∃ κ : X →₀ ℂ, (∀ y ∈ κ.support, y ∈ G) ∧ ∀ v ∈ W, ∑ y ∈ κ.support, κ y • T y (∑ x ∈ J, c x • T x v) = v := by
  intro X _ Γ G V _ _ T W β a χ hΓG hT0 hTT hβ ha hχ hχc hsep J c hJ
  classical
  let A := Submodule.span ℂ (T '' (G : Set X))
  have hTA (y : X) (hy : y ∈ G) : T y ∈ A := Submodule.subset_span ⟨y, hy, rfl⟩
  have hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A := by
    apply Submodule.mul_le.mp
    change Submodule.span ℂ _ * Submodule.span ℂ _ ≤ A
    rw [Submodule.span_mul_span, Submodule.span_le, Set.mul_subset_iff]
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    have he : T y * T z = β y z • T (y + z) := by ext v; simp [hTT]
    rw [he]
    exact A.smul_mem _ (hTA _ (G.add_mem hy hz))
  have hone : (1 : V →ₗ[ℂ] V) ∈ A := by
    have e : (1 : V →ₗ[ℂ] V) = T 0 := by ext v; simp [hT0]
    rw [e]; exact hTA 0 G.zero_mem
  have hκ : ∀ L ∈ A, ∃ κ : X →₀ ℂ, (∀ y ∈ κ.support, y ∈ G) ∧ ∀ u, ∑ y ∈ κ.support, κ y • T y u = L u := by
    intro L hL
    obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hL
    refine ⟨l, fun y hy => (Finsupp.mem_supported _ _).1 hl hy, fun u => ?_⟩
    simp [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  have hshift : ∀ x0 x, x - x0 ∈ Γ → ∀ v ∈ W, T x v = ((β x0 (x - x0))⁻¹ * a (x - x0)) • T x0 v := by
    intro x0 x h v hv
    have h1 := hTT x0 (x - x0) v
    have e : x0 + (x - x0) = x := by abel
    rw [(ha _ h).2 v hv, map_smul, e] at h1
    rw [mul_smul, h1, smul_smul, inv_mul_cancel₀ (hβ _ _), one_smul]
  let d (x0 : X) := ∑ x ∈ J, if x - x0 ∈ Γ then c x * ((β x0 (x - x0))⁻¹ * a (x - x0)) else 0
  have hcls (x0 : X) (v : V) (hv : v ∈ W) :
      ∑ x ∈ J, (if x - x0 ∈ Γ then c x else 0) • T x v = d x0 • T x0 v := by
    simp only [d, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [mul_smul, ← hshift x0 x h v hv]
    · simp
  by_cases h : ∃ x0 ∈ J, d x0 ≠ 0
  · obtain ⟨x0, hx0, hd⟩ := h
    -- Each separating factor kills one translate and fixes the chosen coset.
    have project (S : Finset X) (hS : ∀ x ∈ S, x ∈ G) :
        ∃ L ∈ A, (∀ x, x - x0 ∈ Γ → ∀ v ∈ W, L (T x v) = T x v) ∧
          ∀ x ∈ S, x - x0 ∉ Γ → ∀ v ∈ W, L (T x v) = 0 := by
      induction S using Finset.induction_on with
      | empty => exact ⟨1, hone, by simp, by simp⟩
      | @insert y S _ ih =>
        obtain ⟨L, hL, hfix, hkill⟩ := ih fun x hx => hS x (Finset.mem_insert_of_mem hx)
        by_cases hy : y - x0 ∈ Γ
        · exact ⟨L, hL, hfix, by simpa [hy] using hkill⟩
        obtain ⟨γ, hγ, hne⟩ := hsep y (hS y (Finset.mem_insert_self ..)) x0 (hJ x0 hx0) hy
        let Q : V →ₗ[ℂ] V := (χ x0 γ - χ y γ)⁻¹ • ((a γ)⁻¹ • T γ - χ y γ • 1)
        have hQ : Q ∈ A := A.smul_mem _ (A.sub_mem (A.smul_mem _ (hTA _ (hΓG hγ))) (A.smul_mem _ hone))
        have act (x : X) (v : V) (hv : v ∈ W) :
            Q (T x v) = ((χ x0 γ - χ y γ)⁻¹ * (χ x γ - χ y γ)) • T x v := by
          change (χ x0 γ - χ y γ)⁻¹ • ((a γ)⁻¹ • T γ (T x v) - χ y γ • T x v) = _
          simp only [hχ γ hγ, (ha γ hγ).2 v hv, map_smul, smul_smul, ← sub_smul]
          congr 2
          field_simp [(ha γ hγ).1]
        refine ⟨L * Q, hmul _ hL _ hQ, ?_, ?_⟩
        · intro x hx v hv
          have he : χ x γ = χ x0 γ := by simpa using hχc x0 γ hγ (x - x0) hx
          change L (Q (T x v)) = T x v
          rw [act x v hv, he, inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm),
            one_smul, hfix x hx v hv]
        · intro x hx hout v hv
          change L (Q (T x v)) = 0
          rw [act x v hv, map_smul]
          rcases Finset.mem_insert.mp hx with rfl | hs
          · simp
          · rw [hkill x hs hout v hv, smul_zero]
    obtain ⟨L, hL, hfix, hkill⟩ := project J hJ
    have extract (v : V) (hv : v ∈ W) :
        L (∑ x ∈ J, c x • T x v) = d x0 • T x0 v := by
      rw [← hcls x0 v hv, map_sum]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hmem : x - x0 ∈ Γ
      · simp [hmem, hfix x hmem v hv]
      · simp [hmem, hkill x hx hmem v hv]
    obtain ⟨κ, hκG, hκeq⟩ := hκ (((d x0 * β (-x0) x0)⁻¹ • T (-x0)) * L)
      (hmul _ (A.smul_mem _ (hTA _ (G.neg_mem (hJ x0 hx0)))) _ hL)
    refine Or.inr ⟨κ, hκG, fun v hv => ?_⟩
    rw [hκeq]
    change (d x0 * β (-x0) x0)⁻¹ • T (-x0) (L _) = v
    rw [extract v hv, map_smul,
      hTT, neg_add_cancel, hT0, smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ (mul_ne_zero hd (hβ _ _)), one_smul]
  · -- The sum over every coset vanishes, hence so does the original finite sum.
    refine Or.inl fun v hv => ?_
    let q := QuotientAddGroup.mk' Γ
    have class_zero (u : X ⧸ Γ) (hu : u ∈ J.image q) :
        (∑ x ∈ J, if q x = u then c x • T x v else 0) = 0 := by
      obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hu
      have hd : d x0 = 0 := by_contra fun hn => h ⟨x0, hx0, hn⟩
      simpa [q, QuotientAddGroup.eq_iff_sub_mem, ite_smul, hd] using hcls x0 v hv
    calc
      ∑ x ∈ J, c x • T x v = ∑ u ∈ J.image q, ∑ x ∈ J, if q x = u then c x • T x v else 0 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x hx => by simp [Finset.mem_image_of_mem q hx]
      _ = 0 := Finset.sum_eq_zero class_zero

end GlobalTheory
