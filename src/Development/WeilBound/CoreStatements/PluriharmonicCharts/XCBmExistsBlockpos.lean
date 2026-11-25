module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_blockpos

theorem posDef_fromBlocks {m n : Type} [Fintype m] [Fintype n] {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : (Matrix.fromBlocks A 0 0 B).PosDef := by
  classical
  let _ := hA.isUnit.invertible
  have hpsd : (Matrix.fromBlocks A 0 0 B).PosSemidef := by
    simpa only [Matrix.conjTranspose_zero] using
      (Matrix.PosDef.fromBlocks₁₁ (0 : Matrix m n ℂ) B hA).2 (by simpa using hB.posSemidef)
  rw [hpsd.posDef_iff_det_ne_zero, Matrix.det_fromBlocks_zero₁₂]
  exact mul_ne_zero hA.det_pos.ne' hB.det_pos.ne'

end PositivityTheory.Xgp.c_bm_exists_blockpos

theorem PositivityTheory.Xgp.t_c_bm_exists_blockpos : ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef → IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef := by
  intro p q Γ h
  refine ⟨fun a b hab => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := (blockEquiv p q).surjective a
    obtain ⟨b, rfl⟩ := (blockEquiv p q).surjective b
    simp only [blockG, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b
    · exact absurd (show (a : ℕ) < _ ↔ (b : ℕ) < _ by omega) hab
    · rfl
    · rfl
    · exact absurd (show q + (a : ℕ) < _ ↔ q + (b : ℕ) < _ by omega) hab
  · refine Matrix.PosDef.submatrix ?_ (blockEquiv p q).symm.injective
    exact PositivityTheory.Xgp.c_bm_exists_blockpos.posDef_fromBlocks
      (h.submatrix (omEmb_strictMono p q).injective).transpose.inv
      (h.submatrix (wEmb_strictMono p q).injective)
