module

public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.LinearAlgebra.Span.Defs

@[expose] public section

namespace UpperTheory.Reformulated.B.Qk30

@[reducible] noncomputable def GLOps.{u_2, u_3} (n : ℕ) (K : Type u_2) (V : Type u_3) [Field K]
    [AddCommGroup V] [Module K V] : Type u_3 :=
  Fin n → Fin n → Module.End K V

noncomputable def loweringMonoid.{u_1, u_2} {n : ℕ} {K : Type u_1} {V : Type u_2} [Field K]
    [AddCommGroup V] [Module K V] (E : GLOps n K V) : Submonoid (Module.End K V) :=
  Submonoid.closure {g : Module.End K V | ∃ (c : Fin n), ∃ d < c, g = E c d}

noncomputable def weightSp.{u_2, u_3} {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K]
    [AddCommGroup V] [Module K V] (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  ⨅ (a : Fin n), LinearMap.ker (E a a - (mu a : K) • (1 : Module.End K V))

noncomputable def IsHWV.{u_2, u_3} {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V]
    [Module K V] (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) : Prop :=
  v ≠ 0 ∧ v ∈ weightSp E lam ∧ ∀ (a b : Fin n), a < b → E a b v = 0

noncomputable def hwvLoweringSpan.{u_1, u_2} {n : ℕ} {K : Type u_1} {V : Type u_2} [Field K]
    [AddCommGroup V] [Module K V] (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  Submodule.span K {x : V | ∃ u ∈ loweringMonoid E, ∃ (w : V), IsHWV E mu w ∧ x = u w}

theorem hwv_lowering_span_lower.{u_1, u_2} {n : ℕ} {K : Type u_1} {V : Type u_2} [Field K]
    [AddCommGroup V] [Module K V] (E : GLOps n K V) (mu : Fin n → ℤ) {a b : Fin n} (hab : b < a)
    {x : V} (hx : x ∈ hwvLoweringSpan E mu) : E a b x ∈ hwvLoweringSpan E mu := by
  unfold hwvLoweringSpan at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hy
    refine Submodule.subset_span ⟨E a b * u, ?_, w, hw, rfl⟩
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨a, b, hab, rfl⟩) hu
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hy

end UpperTheory.Reformulated.B.Qk30
