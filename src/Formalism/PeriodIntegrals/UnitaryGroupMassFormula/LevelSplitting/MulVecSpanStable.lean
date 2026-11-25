module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section

namespace PI.LevelKSplit.W.Loc

open Submodule

variable {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n r : ℕ}



theorem mulVec_span_stable (A : Matrix (Fin n) (Fin n) B) (G : Set (Fin n → B))
    (hG : ∀ x ∈ G, A.mulVec x ∈ span O G) : ∀ x ∈ span O G, A.mulVec x ∈ span O G :=
  fun _ hx => (Submodule.span_le (p := (span O G).comap
    ((Matrix.mulVecLin A).restrictScalars O))).2 hG hx

private theorem sep_lemma' (c v : Fin r → Fin n → B)
    (h : ∀ a b, c b ⬝ᵥ v a = if a = b then 1 else 0) (g : Fin n → B)
    (hg : g ∈ span B (Set.range v)) : g = ∑ a, (c a ⬝ᵥ g) • v a := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a', rfl⟩ := hx
    simp [h]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [dotProduct_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | smul s x _ hx =>
    simp only [dotProduct_smul, smul_eq_mul, mul_smul]
    rw [← Finset.smul_sum, ← hx]

private theorem units_eq_of_res_eq_of_le_iSup (c v : Fin r → Fin n → B)
    (h : ∀ a b, c b ⬝ᵥ v a = 0) (g : Fin n → B)
    (hg : g ∈ span B (Set.range v)) (b : Fin r) : c b ⬝ᵥ g = 0 :=
  (Submodule.span_le (p := LinearMap.ker (dotProductBilin B B (c b)))).2
    (Set.range_subset_iff.2 fun a => h a b) hg

theorem sep (e f ce cf : Fin r → Fin n → B)
    (hee : ∀ a b, ce b ⬝ᵥ e a = 0)
    (hef : ∀ a b, ce b ⬝ᵥ f a = if a = b then 1 else 0)
    (hfe : ∀ a b, cf b ⬝ᵥ e a = if a = b then 1 else 0)
    (GX GW GY : Set (Fin n → B))
    (hGX : GX ⊆ span B (Set.range e)) (hGY : GY ⊆ span B (Set.range f))
    (hGW : ∀ w ∈ GW, ∀ b, ce b ⬝ᵥ w = 0 ∧ cf b ⬝ᵥ w = 0)
    (z y : Fin n → B) (hz : ∀ b, ce b ⬝ᵥ z = 0 ∧ cf b ⬝ᵥ z = 0)
    (hy : y ∈ span O (GX ∪ GW ∪ GY)) (hzy : z - y ∈ span B (Set.range e)) :
    z ∈ span O (GX ∪ GW ∪ GY) := by
  rw [Submodule.span_union, Submodule.span_union] at hy
  obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hs
  have hxB : x ∈ span B (Set.range e) :=
    Submodule.span_le.mpr hGX (Submodule.span_le_restrictScalars O B GX hx)
  have huB : u ∈ span B (Set.range f) :=
    Submodule.span_le.mpr hGY (Submodule.span_le_restrictScalars O B GY hu)
  have hwW (b : Fin r) : ce b ⬝ᵥ w = 0 ∧ cf b ⬝ᵥ w = 0 :=
    (Submodule.span_le (p := LinearMap.ker ((dotProductBilin B B (ce b)).restrictScalars O) ⊓
      LinearMap.ker ((dotProductBilin B B (cf b)).restrictScalars O))).2
      (fun v hv => hGW v hv b) hw
  have hceu : ∀ b, ce b ⬝ᵥ u = 0 := by
    intro b
    have h2 : ce b ⬝ᵥ (z - (x + w + u)) = 0 := units_eq_of_res_eq_of_le_iSup ce e hee _ hzy b
    have h3 : ce b ⬝ᵥ x = 0 := units_eq_of_res_eq_of_le_iSup ce e hee _ hxB b
    rw [dotProduct_sub, dotProduct_add, dotProduct_add, (hz b).1, h3, (hwW b).1] at h2
    linear_combination -h2
  have hu0 : u = 0 := by
    rw [sep_lemma' ce f hef u huB]
    simp [hceu]
  have hzy' := sep_lemma' cf e hfe _ hzy
  have hxe := sep_lemma' cf e hfe x hxB
  have hcoef : ∀ a, cf a ⬝ᵥ (z - (x + w + u)) = -(cf a ⬝ᵥ x) := by
    intro a
    rw [hu0, dotProduct_sub, dotProduct_add, dotProduct_add, (hz a).2, (hwW a).2, dotProduct_zero]
    ring
  have hzx : z - (x + w + u) = -x := by
    rw [hzy']
    simp_rw [hcoef, neg_smul, Finset.sum_neg_distrib]
    rw [← hxe]
  rw [hu0, add_zero, sub_eq_iff_eq_add] at hzx
  rw [hzx, neg_add_cancel_left]
  exact Submodule.span_mono (fun v hv => Or.inl (Or.inr hv)) hw

end PI.LevelKSplit.W.Loc
