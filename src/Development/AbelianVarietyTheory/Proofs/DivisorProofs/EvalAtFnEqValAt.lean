module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer

namespace GlobalTheory.AnPer

theorem evalAt_fn_eq_valAt' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) {X : Scheme.{0}}
    (x : Sp (Hol W) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (p : E) (hp : p ∈ W) :
    ⊤ ≤ (spMap (Hol.ev p hp).toRingHom ≫ x) ⁻¹ᵁ U ∧
      (evalAt x U h f).fn p = valAt' (spMap (Hol.ev p hp).toRingHom ≫ x) U f := by
  set φ : Hol W →+* ℂ := (Hol.ev p hp).toRingHom
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun q _ ↦ h (Set.mem_univ ((spMap φ) q))
  refine ⟨h', ?_⟩
  have e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom =
      x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (Hol W))).hom ≫ CommRingCat.ofHom φ := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
    congr 2
  have e2 := congrArg (fun t ↦ t.hom f) e
  rw [valAt', dite_eq_left h', valAt, ← Hol.ev_apply p hp]
  exact e2.symm

end GlobalTheory.AnPer
