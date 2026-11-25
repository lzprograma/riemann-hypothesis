module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace PointLine

variable {n : ℕ}

theorem eval_smul_of_isHomogeneous {φ : MvPolynomial (Fin n) ℂ} {m : ℕ} (hφ : φ.IsHomogeneous m)
    (t : ℂ) (x : Fin n → ℂ) : eval (t • x) φ = t ^ m * eval x φ :=
  hφ.eval_smul t x

theorem smul_mem_zeroSet {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsHomogIdeal W)
    {x : Fin n → ℂ} (hx : ∀ q ∈ W, eval x q = 0) (t : ℂ) : ∀ q ∈ W, eval (t • x) q = 0 := by
  intro q hq

  rw [← sum_homogeneousComponent q, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d q), hx _ (hW q hq d), mul_zero]

end PointLine


end

end GroundTheory.Heights₂.Heights
