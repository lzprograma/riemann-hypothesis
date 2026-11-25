module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Std.Tactic.BVDecide.Normalize.Prop

import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalSmulOfIsHomogeneousAlt

@[expose] public section

theorem UpperTheory.Reformulated.B.HomogeneousEvalSmul.eval_smul_of_isHomogeneous :
    ∀ {σ : Type} [Fintype σ] {h : MvPolynomial σ ℂ} {d : ℕ},
      h.IsHomogeneous d →
        ∀ (t : ℂ) (v : σ → ℂ),
          (MvPolynomial.eval (t • v) : MvPolynomial σ ℂ → ℂ) h = t ^ d * (MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) h := by
  intro σ _ h d hh t v
  exact UpperTheory.Reformulated.B.Ydc1.eval_smul_of_isHomogeneous hh t v
