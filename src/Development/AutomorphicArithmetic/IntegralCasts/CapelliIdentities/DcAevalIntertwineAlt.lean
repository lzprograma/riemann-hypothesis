module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic

import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DcAevalIntertwine

@[expose] public section

theorem UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine.{u_1, u_2} :
    ∀ {Y : Type u_1} {Z : Type u_2} [AddCommGroup Y] [_root_.Module ℂ Y] [AddCommGroup Z]
    [_root_.Module ℂ Z] (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z),
    (∀ (y : Y), (ψ : Y → Z) ((A : Y → Y) y) = (B : Z → Z) ((ψ : Y → Z) y)) →
      ∀ (p : Polynomial ℂ) (y : Y),
        (ψ : Y → Z) (((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) p : Y → Y) y) =
          ((Polynomial.aeval B : Polynomial ℂ → Module.End ℂ Z) p : Z → Z) ((ψ : Y → Z) y) := by
  intro Y Z _ _ _ _ ψ A B h p y
  exact UpperTheory.Reformulated.B.Qj10.dc_aeval_intertwine ψ A B h p y
