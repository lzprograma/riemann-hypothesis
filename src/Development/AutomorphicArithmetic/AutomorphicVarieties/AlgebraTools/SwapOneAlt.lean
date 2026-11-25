module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqOneOfStrictMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.LegendreSymbol

@[expose] public section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem pair_lt {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) (u : Perm (Fin n)) (hu : u⁻¹ a < u⁻¹ c) :
    (b.T (swap a c) * b.T u - q • b.T u) + (b.T (swap a c) * b.T (swap a c * u) - q • b.T (swap a c * u)) = 0 := by
  have hu : b.T (swap a c * u) = b.T (swap a c) * b.T u := b.T_mul a c h u hu
  have hsq := b.T_sq a c h
  rw [hu, ← mul_assoc, hsq, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  module

private theorem swap_one {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) : b.T (swap a c) * b.one = q • b.one := by
  have hac : a ≠ c := by
    intro e
    rw [e] at h
    omega
  have key : ∀ w : Perm (Fin n), (b.T (swap a c) * b.T w - q • b.T w)
      + (b.T (swap a c) * b.T (swap a c * w) - q • b.T (swap a c * w)) = 0 := by
    intro w
    rcases lt_or_gt_of_ne (show w⁻¹ a ≠ w⁻¹ c from fun e => hac (w⁻¹.injective e)) with hw | hw
    · exact pair_lt b h w hw
    · have hu : (swap a c * w)⁻¹ a < (swap a c * w)⁻¹ c := by
        simpa [Perm.mul_apply, mul_inv_rev, swap_inv, swap_apply_left, swap_apply_right] using hw
      have := pair_lt b h (swap a c * w) hu
      rw [← mul_assoc, swap_mul_self, one_mul] at this
      rw [add_comm]
      exact this
  have hsum : ∑ w, (b.T (swap a c) * b.T w - q • b.T w) = 0 := by
    refine Finset.sum_ninvolution (fun w => swap a c * w) key ?_ (fun _ => Finset.mem_univ _) ?_
    · intro w _ e
      apply hac
      have := congrArg (fun x : Perm (Fin n) => (x * w⁻¹) a) e
      simp [mul_assoc] at this
      exact this.symm
    · intro w
      rw [← mul_assoc, swap_mul_self, one_mul]
  unfold Bern.one
  rw [Finset.mul_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  exact hsum
