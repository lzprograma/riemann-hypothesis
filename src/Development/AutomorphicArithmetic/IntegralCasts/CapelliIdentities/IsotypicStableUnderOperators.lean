module

public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.LinearAlgebra.Span.Defs

@[expose] public section

namespace UpperTheory.Reformulated.B.Qf30

@[reducible] noncomputable def GLOps.{u_2, u_3} (n : ℕ) (K : Type u_2) (V : Type u_3) [Field K]
    [AddCommGroup V] [Module K V] : Type u_3 :=
  Fin n → Fin n → Module.End K V

noncomputable def Umon.{u_2, u_3} {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V]
    [Module K V] (E : GLOps n K V) : Submonoid (Module.End K V) :=
  Submonoid.closure (Set.range fun (ab : Fin n × Fin n) ↦ E ab.1 ab.2)

noncomputable def weightSp.{u_2, u_3} {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K]
    [AddCommGroup V] [Module K V] (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  ⨅ (a : Fin n), LinearMap.ker (E a a - (mu a : K) • (1 : Module.End K V))

noncomputable def IsHWV.{u_2, u_3} {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V]
    [Module K V] (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) : Prop :=
  v ≠ 0 ∧ v ∈ weightSp E lam ∧ ∀ (a b : Fin n), a < b → E a b v = 0

noncomputable def isoSub.{u_2, u_3} {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K]
    [AddCommGroup V] [Module K V] (E : GLOps n K V) (lam : Fin n → ℤ) : Submodule K V :=
  Submodule.span K {x : V | ∃ u ∈ Umon E, ∃ (v : V), IsHWV E lam v ∧ x = u v}

theorem isotypic_stable_under_operators.{u_1, u_2} {n : ℕ} {K : Type u_1} {V : Type u_2} [Field K]
    [AddCommGroup V] [Module K V] (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V}
    (hx : x ∈ isoSub E mu) : E a b x ∈ isoSub E mu := by
  unfold isoSub at hx ⊢
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨u, hu, v, hv, rfl⟩
    refine Submodule.subset_span ⟨E a b * u, ?_, v, hv, rfl⟩
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [map_smul]
    exact Submodule.smul_mem _ c hy

end UpperTheory.Reformulated.B.Qf30
