module
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

@[expose] public section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} (G : Grp k n)

namespace P_DUnit
theorem isUnit_det_sub (A : GL (Fin n) 𝒪[k]) (a : Fin G.s)
    (hA : ∀ i j, G.bl j < G.bl i → (A : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k]) :
    IsUnit ((A : Matrix (Fin n) (Fin n) 𝒪[k]).submatrix
      (Subtype.val : {i : Fin n // G.bl i ≤ a} → Fin n) Subtype.val).det := by
  set M := (IsLocalRing.residue 𝒪[k]).mapMatrix (A : Matrix (Fin n) (Fin n) 𝒪[k]) with hM
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  suffices h : IsUnit M.det by
    rw [Matrix.twoBlockTriangular_det M (fun i => G.bl i ≤ a) (fun i hi j hj => by
      rw [hM, RingHom.mapMatrix_apply, Matrix.map_apply, IsLocalRing.residue_eq_zero_iff]
      exact hA i j (lt_of_le_of_lt hj (not_le.1 hi)))] at h
    exact (isUnit_of_mul_isUnit_left h).ne_zero
  rw [hM, ← RingHom.map_det]
  exact (Matrix.isUnits_det_units A).map _
end P_DUnit

theorem step_DUnit : ModulusOnUnitsProp G := by
  intro hb g hg a
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.1 hg.1
  refine ⟨(P_DUnit.isUnit_det_sub G A a ?_).unit, ?_⟩
  · intro i j hij
    obtain ⟨y, hy, hyx⟩ := hg.2 i j hij
    rw [← (show y = (A : Matrix (Fin n) (Fin n) 𝒪[k]) i j from
      (show Function.Injective (algebraMap 𝒪[k] k) from Subtype.val_injective) (by rw [hyx]; rfl))]
    exact Ideal.pow_le_self (by have := hb.1 (G.bl j) (G.bl i) (ne_of_lt hij); omega) hy
  · rw [IsUnit.unit_spec, RingHom.map_det]
    rfl

end UpperTheory.TNZ.Grp
