module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic

@[expose] public section

theorem UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule.{u_1} :
    ∀ {Y : Type u_1} [AddCommGroup Y] [_root_.Module ℂ Y]
    (A : Module.End ℂ Y) (p : Submodule ℂ Y),
    (∀ y ∈ p, (A : Y → Y) y ∈ p) →
      ∀ (q : Polynomial ℂ), ∀ y ∈ p, ((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) q : Y → Y) y ∈ p := by
  intro Y _ _ A p hA q y hy
  exact Polynomial.aeval_apply_smul_mem_of_le_comap hy q A hA
