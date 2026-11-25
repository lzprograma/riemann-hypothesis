module

import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G P = Pᵀ * G.map τ * P.map (starRingEnd ℂ) := by
  exact ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq τ G P

theorem gram_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (P * Q) = Qᵀ * gram τ G P * Q.map (starRingEnd ℂ) := by
  exact ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul τ G P Q

theorem sum_castLE {R : Type} [AddCommMonoid R] {i n : ℕ} (h : i ≤ n) (f : Fin n → R)
    (hf : ∀ c : Fin n, i ≤ (c : ℕ) → f c = 0) : ∑ c, f c = ∑ c : Fin i, f (Fin.castLE h c) := by
  refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
    (fun c => f (Fin.castLE h c)) f (fun c hc => hf c ?_) (fun _ => rfl)).symm
  by_contra! hlt
  exact hc ⟨⟨c, hlt⟩, rfl⟩

theorem sub_mul_tri {i : ℕ} (h : i ≤ r) (Q A : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.IsUpperTriangular) :
    (Qᵀ * A * Q.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
      (Q.submatrix (Fin.castLE h) (Fin.castLE h))ᵀ * A.submatrix (Fin.castLE h) (Fin.castLE h) *
        (Q.submatrix (Fin.castLE h) (Fin.castLE h)).map (starRingEnd ℂ) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [sum_castLE h]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [sum_castLE h]
    intro k hk
    have hz : Q k (Fin.castLE h a) = 0 :=
      hQ (by simp only [id_eq, Fin.lt_iff_val_lt_val, Fin.coe_castLE]; exact lt_of_lt_of_le a.isLt hk)
    rw [hz, zero_mul]
  · intro l hl
    have hz : Q l (Fin.castLE h b) = 0 :=
      hQ (by simp only [id_eq, Fin.lt_iff_val_lt_val, Fin.coe_castLE]; exact lt_of_lt_of_le b.isLt hl)
    rw [hz, map_zero, mul_zero]

theorem lminor_mul_tri (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ)
    (hQ : Q.IsUpperTriangular) (i : Fin (r + 1)) :
    lminor (gram τ G (P * Q)) i =
      ((Complex.normSq (Q.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
        (Fin.castLE (Nat.le_of_lt_succ i.isLt))).det : ℝ) : ℂ) * lminor (gram τ G P) i := by
  unfold lminor
  rw [gram_mul, sub_mul_tri (Nat.le_of_lt_succ i.isLt) Q (gram τ G P) hQ, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose]
  generalize Q.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = M
  rw [show (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det from (RingHom.map_det _ M).symm,
    ← Complex.mul_conj]
  ring

theorem det_sub_tri_ne {i : ℕ} (h : i ≤ r) (Q : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.IsUpperTriangular)
    (hd : Q.det ≠ 0) : (Q.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0 := by
  have hsub : (Q.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
    intro a b hab
    simp only [Matrix.submatrix_apply]
    exact hQ (by simp only [id_eq, Fin.lt_iff_val_lt_val, Fin.coe_castLE] at hab ⊢; exact hab)
  rw [Matrix.det_of_upperTriangular hsub]
  rw [Matrix.det_of_upperTriangular hQ] at hd
  rw [Finset.prod_ne_zero_iff] at hd ⊢
  intro c _
  exact hd _ (Finset.mem_univ _)

theorem bor_upper {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) (τ : Ψ) :
    (mat b τ).IsUpperTriangular := by
  intro a c hac
  exact (hb τ).2 a c hac

theorem dom_rmul (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul x b ∈ X.dom := by
  apply _root_.ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.rmul_mem <;> assumption

theorem ustab_mat {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} {γ : GL (Fin r) E}
    (h : IsUStab G Λ γ) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map cc = G := by
  ext k l
  have h1 := h.1 (Pi.single k 1) (Pi.single l 1)
  have hR : herm G (Pi.single k 1) (Pi.single l 1) = G k l := by
    have hs : ∀ b, cc ((Pi.single l (1 : E) : Fin r → E) b) = (Pi.single l (1 : E) : Fin r → E) b := by
      intro b
      by_cases hb : b = l <;> simp [hb, cc]
    simp only [herm, hs]
    simp [Pi.single_apply]
  have hL : herm G (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single k 1))
      (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single l 1)) =
      ((γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map cc) k l := by
    simp only [herm, Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [← hL, h1, hR]

theorem dom_lact (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E}
    (hγ : IsUStab X.Gm X.Λ γ) : lact γ x ∈ X.dom := by
  intros
  apply _root_.GlobalTheory.MajInv.lact_mem_dom <;> assumption

end Formalism.L2.Pj
