module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

noncomputable section
namespace GlobalTheory.PhiGam.Model
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam

section
variable (k : Type) [Field k]

instance towerA : IsScalarTower k k⸨X⸩ k⸨X⸩ := ⟨fun c x y => by
  rw [_root_.GlobalTheory.PhiGam.const_smul_eq, _root_.GlobalTheory.PhiGam.const_smul_eq k c, smul_eq_mul, smul_eq_mul, mul_assoc]⟩

instance towerB : IsScalarTower k k⟦X⟧ k⸨X⸩ := ⟨fun c a y => by
  rw [_root_.GlobalTheory.PhiGam.const_smul_eq k c, Algebra.smul_def (c • a), Algebra.smul_def a, Algebra.smul_def c, map_mul, mul_assoc]
  rfl⟩

end

section
variable {k : Type} [Field k]

theorem gmult_top_bot {U : Type} [AddCommGroup U] [Module k U] (T : Module.End k U) (x : k) :
    gmult T ⊤ ⊥ x = Module.finrank k (T.maxGenEigenspace x) := by
  have hS : (⨆ m : ℕ, (⊥ : Submodule k U).comap ((T - algebraMap k (Module.End k U) x) ^ m))
      = T.maxGenEigenspace x := by
    apply le_antisymm
    · refine iSup_le fun m y hy => ?_
      rw [Submodule.mem_comap, Submodule.mem_bot, Algebra.algebraMap_eq_smul_one] at hy
      exact (Module.End.mem_maxGenEigenspace T x y).mpr ⟨m, hy⟩
    · intro y hy
      obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace T x y).mp hy
      refine Submodule.mem_iSup_of_mem m ?_
      rw [Submodule.mem_comap, Submodule.mem_bot, Algebra.algebraMap_eq_smul_one]
      exact hm
  unfold gmult
  rw [top_inf_eq, hS]
  have hb : (⊥ : Submodule k U).submoduleOf (T.maxGenEigenspace x) = ⊥ := by
    ext y
    simp [Submodule.submoduleOf]
  rw [hb]
  exact (Submodule.quotEquivOfEqBot _ rfl).finrank_eq

end

end GlobalTheory.PhiGam.Model
