module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePoint, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePointStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePoint =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePoint", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_unique : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (v' u' : N'.Gt) (vs : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' vs → v' = u' := by
  intro F _ N N' r W φ e wv hT v' u' vs hv hu
  obtain ⟨-, hφ, -, -, -, hw, -⟩ := hT
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨hu1, hu2⟩ := hu
  have hb : v'.b = u'.b := hφ.1 (funext fun j => (hv1 j).trans (hu1 j).symm)
  refine NumD.Gt.ext hb (funext fun χ' => ?_)
  have h1 := hv2 χ'
  have h2 := hu2 χ'
  rw [← hb] at h2
  have hne : wv (N'.c χ') * wv v'.b ≠ 0 := mul_ne_zero (hw _) (hw _)
  apply Units.ext
  apply mul_right_cancel₀ hne
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, h1, h2]

end GlobalTheory.Mum.TensTor
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePoint =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePointStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePointStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePoint\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.tensorTorusValueCorrespondence_unique_point : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (v' u' : N'.Gt) (vs : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' vs → v' = u' := by
  first | exact @GlobalTheory.Mum.TensTor.gtRelV_unique
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePointStatement =====
