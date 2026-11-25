module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulConjTransposeEq

@[expose] public section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.IwaPf

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_mul_self : JJ n * JJ n = -1 := PositivityTheory.Rg.Sw.LVs.JJ_mul_JJ

theorem inG_blocks (g : M2 n) (h : InG g) :
    g.toBlocks₁₁ᴴ * g.toBlocks₂₁ - g.toBlocks₂₁ᴴ * g.toBlocks₁₁ = 0 ∧
    g.toBlocks₁₁ᴴ * g.toBlocks₂₂ - g.toBlocks₂₁ᴴ * g.toBlocks₁₂ = 1 ∧
    g.toBlocks₁₂ᴴ * g.toBlocks₂₂ - g.toBlocks₂₂ᴴ * g.toBlocks₁₂ = 0 := by
  have h' := h
  unfold InG at h'
  rw [← fromBlocks_toBlocks g, fromBlocks_conjTranspose, JJ, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_inj] at h'
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, add_zero, zero_add] at h'
  obtain ⟨h1, h2, h3, h4⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [← h1]; abel
  · rw [← h2]; abel
  · rw [← h4]; abel

theorem inG_rows (g : M2 n) (h : InG g) : g * JJ n * gᴴ = JJ n := by
  apply _root_.PositivityTheory.Rg.Sw.LVs.mul_JJ_conjTranspose <;> assumption

theorem key (a b c d : Matrix (Fin n) (Fin n) ℂ) (E1 : aᴴ * c - cᴴ * a = 0) (E2 : aᴴ * d - cᴴ * b = 1)
    (E3 : bᴴ * d - dᴴ * b = 0) (s : ℂ) :
    (s • a + b)ᴴ * (s • c + d) - (s • c + d)ᴴ * (s • a + b) = (star s - s) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have E2' : dᴴ * a - bᴴ * c = 1 := by
    have e := congrArg conjTranspose E2
    simpa [conjTranspose_sub, conjTranspose_mul] using e
  have expand : (s • a + b)ᴴ * (s • c + d) - (s • c + d)ᴴ * (s • a + b)
      = (star s * s) • (aᴴ * c - cᴴ * a) + star s • (aᴴ * d - cᴴ * b)
        - s • (dᴴ * a - bᴴ * c) + (bᴴ * d - dᴴ * b) := by
    simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul]
    module
  rw [expand, E1, E2, E2', E3]
  module

theorem det_ne (g : M2 n) (h : InG g) (s : ℂ) (hs : star s - s ≠ 0) : (s • g.toBlocks₂₁ + g.toBlocks₂₂).det ≠ 0 := by
  obtain ⟨E1, E2, E3⟩ := inG_blocks g h
  intro hdet
  obtain ⟨v, hv, hYv⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  have K := key g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂ E1 E2 E3 s
  set X := s • g.toBlocks₁₁ + g.toBlocks₁₂
  set Y := s • g.toBlocks₂₁ + g.toBlocks₂₂
  have L : star v ⬝ᵥ ((Xᴴ * Y - Yᴴ * X) *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hYv,
      Matrix.mulVec_zero, zero_sub, dotProduct_neg, dotProduct_mulVec, ← star_mulVec,
      hYv, star_zero, zero_dotProduct, neg_zero]
  rw [K, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at L
  rcases mul_eq_zero.mp L with h0 | h0
  · exact hs h0
  · exact hv (dotProduct_star_self_eq_zero.mp h0)

end PositivityTheory.Rg.Sw.AbsSt.IwaPf
